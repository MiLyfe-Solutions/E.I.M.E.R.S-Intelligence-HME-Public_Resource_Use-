import V185TrunkScan23Chunk1283

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7606714 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_7606714 : Nat := 118140960795 + 7606714 * 2 ^ 59
def prefixEnd_7606714 : Nat := 4983230072969 + 3 ^ 40 * 7606714 * 2
def baseEnd_7606714 : Nat := 3905900483284656930192365

theorem tailTrace_7606714 : CollatzResearch.WordTrace tailWord_7606714 prefixEnd_7606714 3905900483284656930192365 := by
  unfold tailWord_7606714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69359913041045444041954799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184959768109454517445212797 69359913041045444041954799)
  ·
    refine ⟨104039869561568166062932199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69359913041045444041954799 104039869561568166062932199)
    ·
      refine ⟨156059804342352249094398299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104039869561568166062932199 156059804342352249094398299)
      ·
        refine ⟨234089706513528373641597449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156059804342352249094398299 234089706513528373641597449)
        ·
          refine ⟨175567279885146280231198087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234089706513528373641597449 175567279885146280231198087)
          ·
            refine ⟨263350919827719420346797131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175567279885146280231198087 263350919827719420346797131)
            ·
              refine ⟨395026379741579130520195697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263350919827719420346797131 395026379741579130520195697)
              ·
                refine ⟨296269784806184347890146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395026379741579130520195697 296269784806184347890146773)
                ·
                  refine ⟨6943823081394945653675315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 296269784806184347890146773 6943823081394945653675315)
                  ·
                    refine ⟨10415734622092418480512973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943823081394945653675315 10415734622092418480512973)
                    ·
                      refine ⟨3905900483284656930192365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415734622092418480512973 3905900483284656930192365)
                      ·
                        rfl

theorem cell23_7606714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_7606714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606714 prefixEnd_7606714 := by exact prefixLift 7606714
  have htrace : WordTrace (prefixWord ++ tailWord_7606714) baseStart_7606714 baseEnd_7606714 := by
    simpa [prefixWord, tailWord_7606714, baseEnd_7606714] using wordTrace_append hprefix tailTrace_7606714
  have hstable : (prefixWord ++ tailWord_7606714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606714).length < 2 ^ (prefixWord ++ tailWord_7606714).sum := by decide
  have hdescent : baseEnd_7606714 < baseStart_7606714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606734 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_7606734 : Nat := 118140960795 + 7606734 * 2 ^ 59
def prefixEnd_7606734 : Nat := 4983230072969 + 3 ^ 40 * 7606734 * 2
def baseEnd_7606734 : Nat := 1301970250965915617314091

theorem tailTrace_7606734 : CollatzResearch.WordTrace tailWord_7606734 prefixEnd_7606734 1301970250965915617314091 := by
  unfold tailWord_7606734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34680047703013664947943407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184960254416072879722364837 34680047703013664947943407)
  ·
    refine ⟨52020071554520497421915111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34680047703013664947943407 52020071554520497421915111)
    ·
      refine ⟨78030107331780746132872667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52020071554520497421915111 78030107331780746132872667)
      ·
        refine ⟨117045160997671119199309001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78030107331780746132872667 117045160997671119199309001)
        ·
          refine ⟨87783870748253339399481751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117045160997671119199309001 87783870748253339399481751)
          ·
            refine ⟨131675806122380009099222627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87783870748253339399481751 131675806122380009099222627)
            ·
              refine ⟨197513709183570013648833941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131675806122380009099222627 197513709183570013648833941)
              ·
                refine ⟨9258455117979844389789091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197513709183570013648833941 9258455117979844389789091)
                ·
                  refine ⟨13887682676969766584683637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258455117979844389789091 13887682676969766584683637)
                  ·
                    refine ⟨1301970250965915617314091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13887682676969766584683637 1301970250965915617314091)
                    ·
                      rfl

theorem cell23_7606734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_7606734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606734 prefixEnd_7606734 := by exact prefixLift 7606734
  have htrace : WordTrace (prefixWord ++ tailWord_7606734) baseStart_7606734 baseEnd_7606734 := by
    simpa [prefixWord, tailWord_7606734, baseEnd_7606734] using wordTrace_append hprefix tailTrace_7606734
  have hstable : (prefixWord ++ tailWord_7606734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606734).length < 2 ^ (prefixWord ++ tailWord_7606734).sum := by decide
  have hdescent : baseEnd_7606734 < baseStart_7606734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606741 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7606741 : Nat := 118140960795 + 7606741 * 2 ^ 59
def prefixEnd_7606741 : Nat := 4983230072969 + 3 ^ 40 * 7606741 * 2
def baseEnd_7606741 : Nat := 3905914347262328324554741

theorem tailTrace_7606741 : CollatzResearch.WordTrace tailWord_7606741 prefixEnd_7606741 3905914347262328324554741 := by
  unfold tailWord_7606741
  simp only [CollatzResearch.WordTrace]
  refine ⟨277440636935083959779052077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184960424623389306519368051 277440636935083959779052077)
  ·
    refine ⟨104040238850656484917144529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277440636935083959779052077 104040238850656484917144529)
    ·
      refine ⟨78030179137992363687858397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104040238850656484917144529 78030179137992363687858397)
      ·
        refine ⟨29261317176747136382946899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78030179137992363687858397 29261317176747136382946899)
        ·
          refine ⟨43891975765120704574420349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29261317176747136382946899 43891975765120704574420349)
          ·
            refine ⟨16459490911920264215407631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43891975765120704574420349 16459490911920264215407631)
            ·
              refine ⟨24689236367880396323111447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16459490911920264215407631 24689236367880396323111447)
              ·
                refine ⟨37033854551820594484667171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24689236367880396323111447 37033854551820594484667171)
                ·
                  refine ⟨55550781827730891727000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37033854551820594484667171 55550781827730891727000757)
                  ·
                    refine ⟨5207885796349771099406321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55550781827730891727000757 5207885796349771099406321)
                    ·
                      refine ⟨3905914347262328324554741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207885796349771099406321 3905914347262328324554741)
                      ·
                        rfl

theorem cell23_7606741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7606741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606741 prefixEnd_7606741 := by exact prefixLift 7606741
  have htrace : WordTrace (prefixWord ++ tailWord_7606741) baseStart_7606741 baseEnd_7606741 := by
    simpa [prefixWord, tailWord_7606741, baseEnd_7606741] using wordTrace_append hprefix tailTrace_7606741
  have hstable : (prefixWord ++ tailWord_7606741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606741).length < 2 ^ (prefixWord ++ tailWord_7606741).sum := by decide
  have hdescent : baseEnd_7606741 < baseStart_7606741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606751 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 1, 5]
def baseStart_7606751 : Nat := 118140960795 + 7606751 * 2 ^ 59
def prefixEnd_7606751 : Nat := 4983230072969 + 3 ^ 40 * 7606751 * 2
def baseEnd_7606751 : Nat := 1301973160689624428476565

theorem tailTrace_7606751 : CollatzResearch.WordTrace tailWord_7606751 prefixEnd_7606751 1301973160689624428476565 := by
  unfold tailWord_7606751
  simp only [CollatzResearch.WordTrace]
  refine ⟨277441001665047731486916107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184960667776698487657944071 277441001665047731486916107)
  ·
    refine ⟨416161502497571597230374161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277441001665047731486916107 416161502497571597230374161)
    ·
      refine ⟨312121126873178697922780621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416161502497571597230374161 312121126873178697922780621)
      ·
        refine ⟨117045422577442011721042733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312121126873178697922780621 117045422577442011721042733)
        ·
          refine ⟨43892033466540754395391025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117045422577442011721042733 43892033466540754395391025)
          ·
            refine ⟨32919025099905565796543269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43892033466540754395391025 32919025099905565796543269)
            ·
              refine ⟨6172317206232293586851863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32919025099905565796543269 6172317206232293586851863)
              ·
                refine ⟨9258475809348440380277795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172317206232293586851863 9258475809348440380277795)
                ·
                  refine ⟨13887713714022660570416693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258475809348440380277795 13887713714022660570416693)
                  ·
                    refine ⟨1301973160689624428476565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13887713714022660570416693 1301973160689624428476565)
                    ·
                      rfl

theorem cell23_7606751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_7606751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606751 prefixEnd_7606751 := by exact prefixLift 7606751
  have htrace : WordTrace (prefixWord ++ tailWord_7606751) baseStart_7606751 baseEnd_7606751 := by
    simpa [prefixWord, tailWord_7606751, baseEnd_7606751] using wordTrace_append hprefix tailTrace_7606751
  have hstable : (prefixWord ++ tailWord_7606751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606751).length < 2 ^ (prefixWord ++ tailWord_7606751).sum := by decide
  have hdescent : baseEnd_7606751 < baseStart_7606751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606764 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_7606764 : Nat := 118140960795 + 7606764 * 2 ^ 59
def prefixEnd_7606764 : Nat := 4983230072969 + 3 ^ 40 * 7606764 * 2
def baseEnd_7606764 : Nat := 1301975385772460578189045

theorem tailTrace_7606764 : CollatzResearch.WordTrace tailWord_7606764 prefixEnd_7606764 1301975385772460578189045 := by
  unfold tailWord_7606764
  simp only [CollatzResearch.WordTrace]
  refine ⟨138720737907000317353569673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184960983876000423138092897 138720737907000317353569673)
  ·
    refine ⟨104040553430250238015177255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138720737907000317353569673 104040553430250238015177255)
    ·
      refine ⟨156060830145375357022765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104040553430250238015177255 156060830145375357022765883)
      ·
        refine ⟨234091245218063035534148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156060830145375357022765883 234091245218063035534148825)
        ·
          refine ⟨175568433913547276650611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234091245218063035534148825 175568433913547276650611619)
          ·
            refine ⟨263352650870320914975917429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175568433913547276650611619 263352650870320914975917429)
            ·
              refine ⟨24689311019092585778992259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263352650870320914975917429 24689311019092585778992259)
              ·
                refine ⟨37033966528638878668488389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24689311019092585778992259 37033966528638878668488389)
                ·
                  refine ⟨6943868724119789750341573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37033966528638878668488389 6943868724119789750341573)
                  ·
                    refine ⟨1301975385772460578189045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943868724119789750341573 1301975385772460578189045)
                    ·
                      rfl

theorem cell23_7606764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_7606764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606764 prefixEnd_7606764 := by exact prefixLift 7606764
  have htrace : WordTrace (prefixWord ++ tailWord_7606764) baseStart_7606764 baseEnd_7606764 := by
    simpa [prefixWord, tailWord_7606764, baseEnd_7606764] using wordTrace_append hprefix tailTrace_7606764
  have hstable : (prefixWord ++ tailWord_7606764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606764).length < 2 ^ (prefixWord ++ tailWord_7606764).sum := by decide
  have hdescent : baseEnd_7606764 < baseStart_7606764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606765 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7606765 : Nat := 118140960795 + 7606765 * 2 ^ 59
def prefixEnd_7606765 : Nat := 4983230072969 + 3 ^ 40 * 7606765 * 2
def baseEnd_7606765 : Nat := 3905926670798036230654631

theorem tailTrace_7606765 : CollatzResearch.WordTrace tailWord_7606765 prefixEnd_7606765 3905926670798036230654631 := by
  unfold tailWord_7606765
  simp only [CollatzResearch.WordTrace]
  refine ⟨277441512286997011877925749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184961008191331341251950499 277441512286997011877925749)
  ·
    refine ⟨26010141776905969863555539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277441512286997011877925749 26010141776905969863555539)
    ·
      refine ⟨39015212665358954795333309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26010141776905969863555539 39015212665358954795333309)
      ·
        refine ⟨14630704749509608048249991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39015212665358954795333309 14630704749509608048249991)
        ·
          refine ⟨21946057124264412072374987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630704749509608048249991 21946057124264412072374987)
          ·
            refine ⟨32919085686396618108562481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946057124264412072374987 32919085686396618108562481)
            ·
              refine ⟨24689314264797463581421861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32919085686396618108562481 24689314264797463581421861)
              ·
                refine ⟨4629246424649524421516599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24689314264797463581421861 4629246424649524421516599)
                ·
                  refine ⟨6943869636974286632274899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629246424649524421516599 6943869636974286632274899)
                  ·
                    refine ⟨10415804455461429948412349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943869636974286632274899 10415804455461429948412349)
                    ·
                      refine ⟨3905926670798036230654631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415804455461429948412349 3905926670798036230654631)
                      ·
                        rfl

theorem cell23_7606765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7606765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606765 prefixEnd_7606765 := by exact prefixLift 7606765
  have htrace : WordTrace (prefixWord ++ tailWord_7606765) baseStart_7606765 baseEnd_7606765 := by
    simpa [prefixWord, tailWord_7606765, baseEnd_7606765] using wordTrace_append hprefix tailTrace_7606765
  have hstable : (prefixWord ++ tailWord_7606765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606765).length < 2 ^ (prefixWord ++ tailWord_7606765).sum := by decide
  have hdescent : baseEnd_7606765 < baseStart_7606765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606767 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_7606767 : Nat := 118140960795 + 7606767 * 2 ^ 59
def prefixEnd_7606767 : Nat := 4983230072969 + 3 ^ 40 * 7606767 * 2
def baseEnd_7606767 : Nat := 3905927697759345222829621

theorem tailTrace_7606767 : CollatzResearch.WordTrace tailWord_7606767 prefixEnd_7606767 3905927697759345222829621 := by
  unfold tailWord_7606767
  simp only [CollatzResearch.WordTrace]
  refine ⟨277441585232989766219498555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184961056821993177479665703 277441585232989766219498555)
  ·
    refine ⟨416162377849484649329247833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277441585232989766219498555 416162377849484649329247833)
    ·
      refine ⟨312121783387113486996935875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416162377849484649329247833 312121783387113486996935875)
      ·
        refine ⟨468182675080670230495403813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312121783387113486996935875 468182675080670230495403813)
        ·
          refine ⟨87784251577625668217888215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468182675080670230495403813 87784251577625668217888215)
          ·
            refine ⟨131676377366438502326832323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87784251577625668217888215 131676377366438502326832323)
            ·
              refine ⟨197514566049657753490248485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131676377366438502326832323 197514566049657753490248485)
              ·
                refine ⟨37033981134310828779421591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197514566049657753490248485 37033981134310828779421591)
                ·
                  refine ⟨55550971701466243169132387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37033981134310828779421591 55550971701466243169132387)
                  ·
                    refine ⟨83326457552199364753698581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55550971701466243169132387 83326457552199364753698581)
                    ·
                      refine ⟨3905927697759345222829621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83326457552199364753698581 3905927697759345222829621)
                      ·
                        rfl

theorem cell23_7606767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_7606767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606767 prefixEnd_7606767 := by exact prefixLift 7606767
  have htrace : WordTrace (prefixWord ++ tailWord_7606767) baseStart_7606767 baseEnd_7606767 := by
    simpa [prefixWord, tailWord_7606767, baseEnd_7606767] using wordTrace_append hprefix tailTrace_7606767
  have hstable : (prefixWord ++ tailWord_7606767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606767).length < 2 ^ (prefixWord ++ tailWord_7606767).sum := by decide
  have hdescent : baseEnd_7606767 < baseStart_7606767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606788 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7606788 : Nat := 118140960795 + 7606788 * 2 ^ 59
def prefixEnd_7606788 : Nat := 4983230072969 + 3 ^ 40 * 7606788 * 2
def baseEnd_7606788 : Nat := 3905938480853089640667025

theorem tailTrace_7606788 : CollatzResearch.WordTrace tailWord_7606788 prefixEnd_7606788 3905938480853089640667025 := by
  unfold tailWord_7606788
  simp only [CollatzResearch.WordTrace]
  refine ⟨138721175582956843403006509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184961567443942457870675345 138721175582956843403006509)
  ·
    refine ⟨52020440843608816276127441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138721175582956843403006509 52020440843608816276127441)
    ·
      refine ⟨39015330632706612207095581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52020440843608816276127441 39015330632706612207095581)
      ·
        refine ⟨14630748987264979577660843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39015330632706612207095581 14630748987264979577660843)
        ·
          refine ⟨21946123480897469366491265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630748987264979577660843 21946123480897469366491265)
          ·
            refine ⟨16459592610673102024868449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21946123480897469366491265 16459592610673102024868449)
            ·
              refine ⟨12344694458004826518651337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16459592610673102024868449 12344694458004826518651337)
              ·
                refine ⟨9258520843503619888988503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344694458004826518651337 9258520843503619888988503)
                ·
                  refine ⟨13887781265255429833482755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258520843503619888988503 13887781265255429833482755)
                  ·
                    refine ⟨20831671897883144750224133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13887781265255429833482755 20831671897883144750224133)
                    ·
                      refine ⟨3905938480853089640667025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20831671897883144750224133 3905938480853089640667025)
                      ·
                        rfl

theorem cell23_7606788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7606788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606788 prefixEnd_7606788 := by exact prefixLift 7606788
  have htrace : WordTrace (prefixWord ++ tailWord_7606788) baseStart_7606788 baseEnd_7606788 := by
    simpa [prefixWord, tailWord_7606788, baseEnd_7606788] using wordTrace_append hprefix tailTrace_7606788
  have hstable : (prefixWord ++ tailWord_7606788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606788).length < 2 ^ (prefixWord ++ tailWord_7606788).sum := by decide
  have hdescent : baseEnd_7606788 < baseStart_7606788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606821 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_7606821 : Nat := 118140960795 + 7606821 * 2 ^ 59
def prefixEnd_7606821 : Nat := 4983230072969 + 3 ^ 40 * 7606821 * 2
def baseEnd_7606821 : Nat := 3905955425714688011554373

theorem tailTrace_7606821 : CollatzResearch.WordTrace tailWord_7606821 prefixEnd_7606821 3905955425714688011554373 := by
  unfold tailWord_7606821
  simp only [CollatzResearch.WordTrace]
  refine ⟨277443554774794133441964317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184962369849862755627976211 277443554774794133441964317)
  ·
    refine ⟨104041333040547800040736619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277443554774794133441964317 104041333040547800040736619)
    ·
      refine ⟨156061999560821700061104929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104041333040547800040736619 156061999560821700061104929)
      ·
        refine ⟨117046499670616275045828697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156061999560821700061104929 117046499670616275045828697)
        ·
          refine ⟨87784874752962206284371523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117046499670616275045828697 87784874752962206284371523)
          ·
            refine ⟨131677312129443309426557285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87784874752962206284371523 131677312129443309426557285)
            ·
              refine ⟨24689496024270620517479491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131677312129443309426557285 24689496024270620517479491)
              ·
                refine ⟨37034244036405930776219237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24689496024270620517479491 37034244036405930776219237)
                ·
                  refine ⟨6943920756826112020541107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37034244036405930776219237 6943920756826112020541107)
                  ·
                    refine ⟨10415881135239168030811661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943920756826112020541107 10415881135239168030811661)
                    ·
                      refine ⟨3905955425714688011554373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415881135239168030811661 3905955425714688011554373)
                      ·
                        rfl

theorem cell23_7606821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_7606821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606821 prefixEnd_7606821 := by exact prefixLift 7606821
  have htrace : WordTrace (prefixWord ++ tailWord_7606821) baseStart_7606821 baseEnd_7606821 := by
    simpa [prefixWord, tailWord_7606821, baseEnd_7606821] using wordTrace_append hprefix tailTrace_7606821
  have hstable : (prefixWord ++ tailWord_7606821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606821).length < 2 ^ (prefixWord ++ tailWord_7606821).sum := by decide
  have hdescent : baseEnd_7606821 < baseStart_7606821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606848 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2]
def baseStart_7606848 : Nat := 118140960795 + 7606848 * 2 ^ 59
def prefixEnd_7606848 : Nat := 4983230072969 + 3 ^ 40 * 7606848 * 2
def baseEnd_7606848 : Nat := 3905969289692359405916749

theorem tailTrace_7606848 : CollatzResearch.WordTrace tailWord_7606848 prefixEnd_7606848 3905969289692359405916749 := by
  unfold tailWord_7606848
  simp only [CollatzResearch.WordTrace]
  refine ⟨138722269772848158526598599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184963026363797544702131465 138722269772848158526598599)
  ·
    refine ⟨208083404659272237789897899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138722269772848158526598599 208083404659272237789897899)
    ·
      refine ⟨312125106988908356684846849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208083404659272237789897899 312125106988908356684846849)
      ·
        refine ⟨234093830241681267513635137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312125106988908356684846849 234093830241681267513635137)
        ·
          refine ⟨175570372681260950635226353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234093830241681267513635137 175570372681260950635226353)
          ·
            refine ⟨131677779510945712976419765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175570372681260950635226353 131677779510945712976419765)
            ·
              refine ⟨12344791829151160591539353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131677779510945712976419765 12344791829151160591539353)
              ·
                refine ⟨9258593871863370443654515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344791829151160591539353 9258593871863370443654515)
                ·
                  refine ⟨13887890807795055665481773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258593871863370443654515 13887890807795055665481773)
                  ·
                    refine ⟨5207959052923145874555665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13887890807795055665481773 5207959052923145874555665)
                    ·
                      refine ⟨3905969289692359405916749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207959052923145874555665 3905969289692359405916749)
                      ·
                        rfl

theorem cell23_7606848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_7606848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606848 prefixEnd_7606848 := by exact prefixLift 7606848
  have htrace : WordTrace (prefixWord ++ tailWord_7606848) baseStart_7606848 baseEnd_7606848 := by
    simpa [prefixWord, tailWord_7606848, baseEnd_7606848] using wordTrace_append hprefix tailTrace_7606848
  have hstable : (prefixWord ++ tailWord_7606848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606848).length < 2 ^ (prefixWord ++ tailWord_7606848).sum := by decide
  have hdescent : baseEnd_7606848 < baseStart_7606848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606865 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 1, 3, 2]
def baseStart_7606865 : Nat := 118140960795 + 7606865 * 2 ^ 59
def prefixEnd_7606865 : Nat := 4983230072969 + 3 ^ 40 * 7606865 * 2
def baseEnd_7606865 : Nat := 3905978018863485839404171

theorem tailTrace_7606865 : CollatzResearch.WordTrace tailWord_7606865 prefixEnd_7606865 3905978018863485839404171 := by
  unfold tailWord_7606865
  simp only [CollatzResearch.WordTrace]
  refine ⟨277445159586634728956566049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184963439724423152637710699 277445159586634728956566049)
  ·
    refine ⟨208083869689976046717424537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277445159586634728956566049 208083869689976046717424537)
    ·
      refine ⟨156062902267482035038068403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208083869689976046717424537 156062902267482035038068403)
      ·
        refine ⟨234094353401223052557102605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156062902267482035038068403 234094353401223052557102605)
        ·
          refine ⟨87785382525458644708913477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234094353401223052557102605 87785382525458644708913477)
          ·
            refine ⟨16459759223523495882921277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87785382525458644708913477 16459759223523495882921277)
            ·
              refine ⟨6172409708821310956095479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16459759223523495882921277 6172409708821310956095479)
              ·
                refine ⟨9258614563231966434143219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172409708821310956095479 9258614563231966434143219)
                ·
                  refine ⟨13887921844847949651214829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258614563231966434143219 13887921844847949651214829)
                  ·
                    refine ⟨5207970691817981119205561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13887921844847949651214829 5207970691817981119205561)
                    ·
                      refine ⟨3905978018863485839404171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207970691817981119205561 3905978018863485839404171)
                      ·
                        rfl

theorem cell23_7606865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 3, 2].length) (baseStart_7606865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606865 prefixEnd_7606865 := by exact prefixLift 7606865
  have htrace : WordTrace (prefixWord ++ tailWord_7606865) baseStart_7606865 baseEnd_7606865 := by
    simpa [prefixWord, tailWord_7606865, baseEnd_7606865] using wordTrace_append hprefix tailTrace_7606865
  have hstable : (prefixWord ++ tailWord_7606865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606865).length < 2 ^ (prefixWord ++ tailWord_7606865).sum := by decide
  have hdescent : baseEnd_7606865 < baseStart_7606865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606884 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 7]
def baseStart_7606884 : Nat := 118140960795 + 7606884 * 2 ^ 59
def prefixEnd_7606884 : Nat := 4983230072969 + 3 ^ 40 * 7606884 * 2
def baseEnd_7606884 : Nat := 433998641666213473896287

theorem tailTrace_7606884 : CollatzResearch.WordTrace tailWord_7606884 prefixEnd_7606884 433998641666213473896287 := by
  unfold tailWord_7606884
  simp only [CollatzResearch.WordTrace]
  refine ⟨138722926286782947600753853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184963901715710596801005137 138722926286782947600753853)
  ·
    refine ⟨52021097357543605350282695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138722926286782947600753853 52021097357543605350282695)
    ·
      refine ⟨78031646036315408025424043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52021097357543605350282695 78031646036315408025424043)
      ·
        refine ⟨117047469054473112038136065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78031646036315408025424043 117047469054473112038136065)
        ·
          refine ⟨87785601790854834028602049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117047469054473112038136065 87785601790854834028602049)
          ·
            refine ⟨65839201343141125521451537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87785601790854834028602049 65839201343141125521451537)
            ·
              refine ⟨49379401007355844141088653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65839201343141125521451537 49379401007355844141088653)
              ·
                refine ⟨18517275377758441552908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49379401007355844141088653 18517275377758441552908245)
                ·
                  refine ⟨433998641666213473896287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18517275377758441552908245 433998641666213473896287)
                  ·
                    rfl

theorem cell23_7606884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_7606884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606884 prefixEnd_7606884 := by exact prefixLift 7606884
  have htrace : WordTrace (prefixWord ++ tailWord_7606884) baseStart_7606884 baseEnd_7606884 := by
    simpa [prefixWord, tailWord_7606884, baseEnd_7606884] using wordTrace_append hprefix tailTrace_7606884
  have hstable : (prefixWord ++ tailWord_7606884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606884).length < 2 ^ (prefixWord ++ tailWord_7606884).sum := by decide
  have hdescent : baseEnd_7606884 < baseStart_7606884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606924 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7606924 : Nat := 118140960795 + 7606924 * 2 ^ 59
def prefixEnd_7606924 : Nat := 4983230072969 + 3 ^ 40 * 7606924 * 2
def baseEnd_7606924 : Nat := 3906008314222101108566399

theorem tailTrace_7606924 : CollatzResearch.WordTrace tailWord_7606924 prefixEnd_7606924 3906008314222101108566399 := by
  unfold tailWord_7606924
  simp only [CollatzResearch.WordTrace]
  refine ⟨138723655746710491016481913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184964874328947321355309217 138723655746710491016481913)
  ·
    refine ⟨104042741810032868262361435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138723655746710491016481913 104042741810032868262361435)
    ·
      refine ⟨156064112715049302393542153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104042741810032868262361435 156064112715049302393542153)
      ·
        refine ⟨117048084536286976795156615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156064112715049302393542153 117048084536286976795156615)
        ·
          refine ⟨175572126804430465192734923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117048084536286976795156615 175572126804430465192734923)
          ·
            refine ⟨263358190206645697789102385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175572126804430465192734923 263358190206645697789102385)
            ·
              refine ⟨197518642654984273341826789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263358190206645697789102385 197518642654984273341826789)
              ·
                refine ⟨37034745497809551251592523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197518642654984273341826789 37034745497809551251592523)
                ·
                  refine ⟨55552118246714326877388785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37034745497809551251592523 55552118246714326877388785)
                  ·
                    refine ⟨41664088685035745158041589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55552118246714326877388785 41664088685035745158041589)
                    ·
                      refine ⟨3906008314222101108566399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41664088685035745158041589 3906008314222101108566399)
                      ·
                        rfl

theorem cell23_7606924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7606924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606924 prefixEnd_7606924 := by exact prefixLift 7606924
  have htrace : WordTrace (prefixWord ++ tailWord_7606924) baseStart_7606924 baseEnd_7606924 := by
    simpa [prefixWord, tailWord_7606924, baseEnd_7606924] using wordTrace_append hprefix tailTrace_7606924
  have hstable : (prefixWord ++ tailWord_7606924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606924).length < 2 ^ (prefixWord ++ tailWord_7606924).sum := by decide
  have hdescent : baseEnd_7606924 < baseStart_7606924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606982 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7606982 : Nat := 118140960795 + 7606982 * 2 ^ 59
def prefixEnd_7606982 : Nat := 4983230072969 + 3 ^ 40 * 7606982 * 2
def baseEnd_7606982 : Nat := 1302012698700020627213711

theorem tailTrace_7606982 : CollatzResearch.WordTrace tailWord_7606982 prefixEnd_7606982 1302012698700020627213711 := by
  unfold tailWord_7606982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670294591475339310580475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184966284618140571959050133 8670294591475339310580475)
  ·
    refine ⟨13005441887213008965870713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8670294591475339310580475 13005441887213008965870713)
    ·
      refine ⟨9754081415409756724403035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13005441887213008965870713 9754081415409756724403035)
      ·
        refine ⟨14631122123114635086604553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754081415409756724403035 14631122123114635086604553)
        ·
          refine ⟨10973341592335976314953415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14631122123114635086604553 10973341592335976314953415)
          ·
            refine ⟨16460012388503964472430123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973341592335976314953415 16460012388503964472430123)
            ·
              refine ⟨24690018582755946708645185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460012388503964472430123 24690018582755946708645185)
              ·
                refine ⟨18517513937066960031483889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24690018582755946708645185 18517513937066960031483889)
                ·
                  refine ⟨13888135452800220023612917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18517513937066960031483889 13888135452800220023612917)
                  ·
                    refine ⟨1302012698700020627213711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13888135452800220023612917 1302012698700020627213711)
                    ·
                      rfl

theorem cell23_7606982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7606982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606982 prefixEnd_7606982 := by exact prefixLift 7606982
  have htrace : WordTrace (prefixWord ++ tailWord_7606982) baseStart_7606982 baseEnd_7606982 := by
    simpa [prefixWord, tailWord_7606982, baseEnd_7606982] using wordTrace_append hprefix tailTrace_7606982
  have hstable : (prefixWord ++ tailWord_7606982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606982).length < 2 ^ (prefixWord ++ tailWord_7606982).sum := by decide
  have hdescent : baseEnd_7606982 < baseStart_7606982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606988 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7606988 : Nat := 118140960795 + 7606988 * 2 ^ 59
def prefixEnd_7606988 : Nat := 4983230072969 + 3 ^ 40 * 7606988 * 2
def baseEnd_7606988 : Nat := 3906041176983988858166105

theorem tailTrace_7606988 : CollatzResearch.WordTrace tailWord_7606988 prefixEnd_7606988 3906041176983988858166105 := by
  unfold tailWord_7606988
  simp only [CollatzResearch.WordTrace]
  refine ⟨138724822882594560481646809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184966430510126080642195745 138724822882594560481646809)
  ·
    refine ⟨104043617161945920361235107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138724822882594560481646809 104043617161945920361235107)
    ·
      refine ⟨156065425742918880541852661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104043617161945920361235107 156065425742918880541852661)
      ·
        refine ⟨14631133663398645050798687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156065425742918880541852661 14631133663398645050798687)
        ·
          refine ⟨21946700495097967576198031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631133663398645050798687 21946700495097967576198031)
          ·
            refine ⟨32920050742646951364297047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21946700495097967576198031 32920050742646951364297047)
            ·
              refine ⟨49380076113970427046445571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32920050742646951364297047 49380076113970427046445571)
              ·
                refine ⟨74070114170955640569668357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49380076113970427046445571 74070114170955640569668357)
                ·
                  refine ⟨13888146407054182606812817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74070114170955640569668357 13888146407054182606812817)
                  ·
                    refine ⟨10416109805290636955109613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13888146407054182606812817 10416109805290636955109613)
                    ·
                      refine ⟨3906041176983988858166105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416109805290636955109613 3906041176983988858166105)
                      ·
                        rfl

theorem cell23_7606988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7606988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606988 prefixEnd_7606988 := by exact prefixLift 7606988
  have htrace : WordTrace (prefixWord ++ tailWord_7606988) baseStart_7606988 baseEnd_7606988 := by
    simpa [prefixWord, tailWord_7606988, baseEnd_7606988] using wordTrace_append hprefix tailTrace_7606988
  have hstable : (prefixWord ++ tailWord_7606988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606988).length < 2 ^ (prefixWord ++ tailWord_7606988).sum := by decide
  have hdescent : baseEnd_7606988 < baseStart_7606988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607018 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_7607018 : Nat := 118140960795 + 7607018 * 2 ^ 59
def prefixEnd_7607018 : Nat := 4983230072969 + 3 ^ 40 * 7607018 * 2
def baseEnd_7607018 : Nat := 3906056581403623740790967

theorem tailTrace_7607018 : CollatzResearch.WordTrace tailWord_7607018 prefixEnd_7607018 3906056581403623740790967 := by
  unfold tailWord_7607018
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362684988770109021721427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184967159970053624057923805 69362684988770109021721427)
  ·
    refine ⟨104044027483155163532582141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362684988770109021721427 104044027483155163532582141)
    ·
      refine ⟨39016510306183186324718303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104044027483155163532582141 39016510306183186324718303)
      ·
        refine ⟨58524765459274779487077455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39016510306183186324718303 58524765459274779487077455)
        ·
          refine ⟨87787148188912169230616183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58524765459274779487077455 87787148188912169230616183)
          ·
            refine ⟨131680722283368253845924275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87787148188912169230616183 131680722283368253845924275)
            ·
              refine ⟨197521083425052380768886413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131680722283368253845924275 197521083425052380768886413)
              ·
                refine ⟨74070406284394642788332405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197521083425052380768886413 74070406284394642788332405)
                ·
                  refine ⟨6944100589161997761406163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74070406284394642788332405 6944100589161997761406163)
                  ·
                    refine ⟨10416150883742996642109245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6944100589161997761406163 10416150883742996642109245)
                    ·
                      refine ⟨3906056581403623740790967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416150883742996642109245 3906056581403623740790967)
                      ·
                        rfl

theorem cell23_7607018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_7607018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607018 prefixEnd_7607018 := by exact prefixLift 7607018
  have htrace : WordTrace (prefixWord ++ tailWord_7607018) baseStart_7607018 baseEnd_7607018 := by
    simpa [prefixWord, tailWord_7607018, baseEnd_7607018] using wordTrace_append hprefix tailTrace_7607018
  have hstable : (prefixWord ++ tailWord_7607018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607018).length < 2 ^ (prefixWord ++ tailWord_7607018).sum := by decide
  have hdescent : baseEnd_7607018 < baseStart_7607018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607061 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_7607061 : Nat := 118140960795 + 7607061 * 2 ^ 59
def prefixEnd_7607061 : Nat := 4983230072969 + 3 ^ 40 * 7607061 * 2
def baseEnd_7607061 : Nat := 3906078661071767072553269

theorem tailTrace_7607061 : CollatzResearch.WordTrace tailWord_7607061 prefixEnd_7607061 3906078661071767072553269 := by
  unfold tailWord_7607061
  simp only [CollatzResearch.WordTrace]
  refine ⟨277452308293924654430701037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184968205529283102953800691 277452308293924654430701037)
  ·
    refine ⟨104044615610221745411512889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277452308293924654430701037 104044615610221745411512889)
    ·
      refine ⟨78033461707666309058634667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104044615610221745411512889 78033461707666309058634667)
      ·
        refine ⟨117050192561499463587952001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78033461707666309058634667 117050192561499463587952001)
        ·
          refine ⟨87787644421124597690964001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117050192561499463587952001 87787644421124597690964001)
          ·
            refine ⟨65840733315843448268223001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87787644421124597690964001 65840733315843448268223001)
            ·
              refine ⟨49380549986882586201167251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65840733315843448268223001 49380549986882586201167251)
              ·
                refine ⟨74070824980323879301750877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49380549986882586201167251 74070824980323879301750877)
                ·
                  refine ⟨27776559367621454738156579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74070824980323879301750877 27776559367621454738156579)
                  ·
                    refine ⟨41664839051432182107234869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27776559367621454738156579 41664839051432182107234869)
                    ·
                      refine ⟨3906078661071767072553269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41664839051432182107234869 3906078661071767072553269)
                      ·
                        rfl

theorem cell23_7607061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_7607061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607061 prefixEnd_7607061 := by exact prefixLift 7607061
  have htrace : WordTrace (prefixWord ++ tailWord_7607061) baseStart_7607061 baseEnd_7607061 := by
    simpa [prefixWord, tailWord_7607061, baseEnd_7607061] using wordTrace_append hprefix tailTrace_7607061
  have hstable : (prefixWord ++ tailWord_7607061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607061).length < 2 ^ (prefixWord ++ tailWord_7607061).sum := by decide
  have hdescent : baseEnd_7607061 < baseStart_7607061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607068 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_7607068 : Nat := 118140960795 + 7607068 * 2 ^ 59
def prefixEnd_7607068 : Nat := 4983230072969 + 3 ^ 40 * 7607068 * 2
def baseEnd_7607068 : Nat := 1302027418478782848388579

theorem tailTrace_7607068 : CollatzResearch.WordTrace tailWord_7607068 prefixEnd_7607068 1302027418478782848388579 := by
  unfold tailWord_7607068
  simp only [CollatzResearch.WordTrace]
  refine ⟨138726281802449647313102929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184968375736599529750803905 138726281802449647313102929)
  ·
    refine ⟨104044711351837235484827197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138726281802449647313102929 104044711351837235484827197)
    ·
      refine ⟨39016766756938963306810199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104044711351837235484827197 39016766756938963306810199)
      ·
        refine ⟨58525150135408444960215299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39016766756938963306810199 58525150135408444960215299)
        ·
          refine ⟨87787725203112667440322949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58525150135408444960215299 87787725203112667440322949)
          ·
            refine ⟨16460198475583625145060553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87787725203112667440322949 16460198475583625145060553)
            ·
              refine ⟨12345148856687718858795415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16460198475583625145060553 12345148856687718858795415)
              ·
                refine ⟨18517723285031578288193123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12345148856687718858795415 18517723285031578288193123)
                ·
                  refine ⟨27776584927547367432289685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18517723285031578288193123 27776584927547367432289685)
                  ·
                    refine ⟨1302027418478782848388579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27776584927547367432289685 1302027418478782848388579)
                    ·
                      rfl

theorem cell23_7607068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_7607068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607068 prefixEnd_7607068 := by exact prefixLift 7607068
  have htrace : WordTrace (prefixWord ++ tailWord_7607068) baseStart_7607068 baseEnd_7607068 := by
    simpa [prefixWord, tailWord_7607068, baseEnd_7607068] using wordTrace_append hprefix tailTrace_7607068
  have hstable : (prefixWord ++ tailWord_7607068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607068).length < 2 ^ (prefixWord ++ tailWord_7607068).sum := by decide
  have hdescent : baseEnd_7607068 < baseStart_7607068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607092 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_7607092 : Nat := 118140960795 + 7607092 * 2 ^ 59
def prefixEnd_7607092 : Nat := 4983230072969 + 3 ^ 40 * 7607092 * 2
def baseEnd_7607092 : Nat := 3906094578972056451265627

theorem tailTrace_7607092 : CollatzResearch.WordTrace tailWord_7607092 prefixEnd_7607092 3906094578972056451265627 := by
  unfold tailWord_7607092
  simp only [CollatzResearch.WordTrace]
  refine ⟨138726719478406173362539765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184968959304541564483386353 138726719478406173362539765)
  ·
    refine ⟨13005629951100578752738103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138726719478406173362539765 13005629951100578752738103)
    ·
      refine ⟨19508444926650868129107155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13005629951100578752738103 19508444926650868129107155)
      ·
        refine ⟨29262667389976302193660733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508444926650868129107155 29262667389976302193660733)
        ·
          refine ⟨10973500271241113322622775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29262667389976302193660733 10973500271241113322622775)
          ·
            refine ⟨16460250406861669983934163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973500271241113322622775 16460250406861669983934163)
            ·
              refine ⟨24690375610292504975901245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460250406861669983934163 24690375610292504975901245)
              ·
                refine ⟨9258890853859689365962967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24690375610292504975901245 9258890853859689365962967)
                ·
                  refine ⟨13888336280789534048944451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258890853859689365962967 13888336280789534048944451)
                  ·
                    refine ⟨20832504421184301073416677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13888336280789534048944451 20832504421184301073416677)
                    ·
                      refine ⟨3906094578972056451265627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20832504421184301073416677 3906094578972056451265627)
                      ·
                        rfl

theorem cell23_7607092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_7607092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607092 prefixEnd_7607092 := by exact prefixLift 7607092
  have htrace : WordTrace (prefixWord ++ tailWord_7607092) baseStart_7607092 baseEnd_7607092 := by
    simpa [prefixWord, tailWord_7607092, baseEnd_7607092] using wordTrace_append hprefix tailTrace_7607092
  have hstable : (prefixWord ++ tailWord_7607092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607092).length < 2 ^ (prefixWord ++ tailWord_7607092).sum := by decide
  have hdescent : baseEnd_7607092 < baseStart_7607092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607141 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_7607141 : Nat := 118140960795 + 7607141 * 2 ^ 59
def prefixEnd_7607141 : Nat := 4983230072969 + 3 ^ 40 * 7607141 * 2
def baseEnd_7607141 : Nat := 1302039913174708919850967

theorem tailTrace_7607141 : CollatzResearch.WordTrace tailWord_7607141 prefixEnd_7607141 1302039913174708919850967 := by
  unfold tailWord_7607141
  simp only [CollatzResearch.WordTrace]
  refine ⟨277455226133634828093613277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184970150755756552062408851 277455226133634828093613277)
  ·
    refine ⟨104045709800113060535104979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277455226133634828093613277 104045709800113060535104979)
    ·
      refine ⟨156068564700169590802657469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104045709800113060535104979 156068564700169590802657469)
      ·
        refine ⟨58525711762563596550996551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156068564700169590802657469 58525711762563596550996551)
        ·
          refine ⟨87788567643845394826494827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58525711762563596550996551 87788567643845394826494827)
          ·
            refine ⟨131682851465768092239742241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87788567643845394826494827 131682851465768092239742241)
            ·
              refine ⟨98762138599326069179806681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131682851465768092239742241 98762138599326069179806681)
              ·
                refine ⟨74071603949494551884855011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98762138599326069179806681 74071603949494551884855011)
                ·
                  refine ⟨111107405924241827827282517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74071603949494551884855011 111107405924241827827282517)
                  ·
                    refine ⟨1302039913174708919850967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111107405924241827827282517 1302039913174708919850967)
                    ·
                      rfl

theorem cell23_7607141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_7607141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607141 prefixEnd_7607141 := by exact prefixLift 7607141
  have htrace : WordTrace (prefixWord ++ tailWord_7607141) baseStart_7607141 baseEnd_7607141 := by
    simpa [prefixWord, tailWord_7607141, baseEnd_7607141] using wordTrace_append hprefix tailTrace_7607141
  have hstable : (prefixWord ++ tailWord_7607141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607141).length < 2 ^ (prefixWord ++ tailWord_7607141).sum := by decide
  have hdescent : baseEnd_7607141 < baseStart_7607141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607186 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7607186 : Nat := 118140960795 + 7607186 * 2 ^ 59
def prefixEnd_7607186 : Nat := 4983230072969 + 3 ^ 40 * 7607186 * 2
def baseEnd_7607186 : Nat := 3906142846153579083490195

theorem tailTrace_7607186 : CollatzResearch.WordTrace tailWord_7607186 prefixEnd_7607186 3906142846153579083490195 := by
  unfold tailWord_7607186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69364216854617950194750353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184971244945647867186000941 69364216854617950194750353)
  ·
    refine ⟨52023162640963462646062765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69364216854617950194750353 52023162640963462646062765)
    ·
      refine ⟨19508685990361298492273537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52023162640963462646062765 19508685990361298492273537)
      ·
        refine ⟨14631514492770973869205153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19508685990361298492273537 14631514492770973869205153)
        ·
          refine ⟨10973635869578230401903865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14631514492770973869205153 10973635869578230401903865)
          ·
            refine ⟨8230226902183672801427899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10973635869578230401903865 8230226902183672801427899)
            ·
              refine ⟨12345340353275509202141849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230226902183672801427899 12345340353275509202141849)
              ·
                refine ⟨9259005264956631901606387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12345340353275509202141849 9259005264956631901606387)
                ·
                  refine ⟨13888507897434947852409581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9259005264956631901606387 13888507897434947852409581)
                  ·
                    refine ⟨5208190461538105444653593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13888507897434947852409581 5208190461538105444653593)
                    ·
                      refine ⟨3906142846153579083490195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208190461538105444653593 3906142846153579083490195)
                      ·
                        rfl

theorem cell23_7607186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7607186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607186 prefixEnd_7607186 := by exact prefixLift 7607186
  have htrace : WordTrace (prefixWord ++ tailWord_7607186) baseStart_7607186 baseEnd_7607186 := by
    simpa [prefixWord, tailWord_7607186, baseEnd_7607186] using wordTrace_append hprefix tailTrace_7607186
  have hstable : (prefixWord ++ tailWord_7607186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607186).length < 2 ^ (prefixWord ++ tailWord_7607186).sum := by decide
  have hdescent : baseEnd_7607186 < baseStart_7607186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607188 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 9]
def baseStart_7607188 : Nat := 118140960795 + 7607188 * 2 ^ 59
def prefixEnd_7607188 : Nat := 4983230072969 + 3 ^ 40 * 7607188 * 2
def baseEnd_7607188 : Nat := 434015985901654230629465

theorem tailTrace_7607188 : CollatzResearch.WordTrace tailWord_7607188 prefixEnd_7607188 434015985901654230629465 := by
  unfold tailWord_7607188
  simp only [CollatzResearch.WordTrace]
  refine ⟨138728470182232277560287109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184971293576309703413716145 138728470182232277560287109)
  ·
    refine ⟨26011588159168552042553833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138728470182232277560287109 26011588159168552042553833)
    ·
      refine ⟨19508691119376414031915375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26011588159168552042553833 19508691119376414031915375)
      ·
        refine ⟨29263036679064621047873063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19508691119376414031915375 29263036679064621047873063)
        ·
          refine ⟨43894555018596931571809595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29263036679064621047873063 43894555018596931571809595)
          ·
            refine ⟨65841832527895397357714393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43894555018596931571809595 65841832527895397357714393)
            ·
              refine ⟨49381374395921548018285795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65841832527895397357714393 49381374395921548018285795)
              ·
                refine ⟨74072061593882322027428693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49381374395921548018285795 74072061593882322027428693)
                ·
                  refine ⟨434015985901654230629465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74072061593882322027428693 434015985901654230629465)
                  ·
                    rfl

theorem cell23_7607188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_7607188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607188 prefixEnd_7607188 := by exact prefixLift 7607188
  have htrace : WordTrace (prefixWord ++ tailWord_7607188) baseStart_7607188 baseEnd_7607188 := by
    simpa [prefixWord, tailWord_7607188, baseEnd_7607188] using wordTrace_append hprefix tailTrace_7607188
  have hstable : (prefixWord ++ tailWord_7607188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607188).length < 2 ^ (prefixWord ++ tailWord_7607188).sum := by decide
  have hdescent : baseEnd_7607188 < baseStart_7607188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607211 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_7607211 : Nat := 118140960795 + 7607211 * 2 ^ 59
def prefixEnd_7607211 : Nat := 4983230072969 + 3 ^ 40 * 7607211 * 2
def baseEnd_7607211 : Nat := 3906155683169941485677579

theorem tailTrace_7607211 : CollatzResearch.WordTrace tailWord_7607211 prefixEnd_7607211 3906155683169941485677579 := by
  unfold tailWord_7607211
  simp only [CollatzResearch.WordTrace]
  refine ⟨277457779243381230048661487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184971852828920820032440991 277457779243381230048661487)
  ·
    refine ⟨416186668865071845072992231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277457779243381230048661487 416186668865071845072992231)
    ·
      refine ⟨624280003297607767609488347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416186668865071845072992231 624280003297607767609488347)
      ·
        refine ⟨936420004946411651414232521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624280003297607767609488347 936420004946411651414232521)
        ·
          refine ⟨702315003709808738560674391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936420004946411651414232521 702315003709808738560674391)
          ·
            refine ⟨1053472505564713107841011587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702315003709808738560674391 1053472505564713107841011587)
            ·
              refine ⟨1580208758347069661761517381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053472505564713107841011587 1580208758347069661761517381)
              ·
                refine ⟨296289142190075561580284509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1580208758347069661761517381 296289142190075561580284509)
                ·
                  refine ⟨111108428321278335592606691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296289142190075561580284509 111108428321278335592606691)
                  ·
                    refine ⟨166662642481917503388910037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111108428321278335592606691 166662642481917503388910037)
                    ·
                      refine ⟨3906155683169941485677579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166662642481917503388910037 3906155683169941485677579)
                      ·
                        rfl

theorem cell23_7607211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_7607211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607211 prefixEnd_7607211 := by exact prefixLift 7607211
  have htrace : WordTrace (prefixWord ++ tailWord_7607211) baseStart_7607211 baseEnd_7607211 := by
    simpa [prefixWord, tailWord_7607211, baseEnd_7607211] using wordTrace_append hprefix tailTrace_7607211
  have hstable : (prefixWord ++ tailWord_7607211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607211).length < 2 ^ (prefixWord ++ tailWord_7607211).sum := by decide
  have hdescent : baseEnd_7607211 < baseStart_7607211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607225 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7607225 : Nat := 118140960795 + 7607225 * 2 ^ 59
def prefixEnd_7607225 : Nat := 4983230072969 + 3 ^ 40 * 7607225 * 2
def baseEnd_7607225 : Nat := 3906162871899104430902515

theorem tailTrace_7607225 : CollatzResearch.WordTrace tailWord_7607225 prefixEnd_7607225 3906162871899104430902515 := by
  unfold tailWord_7607225
  simp only [CollatzResearch.WordTrace]
  refine ⟨277458289865330510439671129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184972193243553673626447419 277458289865330510439671129)
  ·
    refine ⟨208093717398997882829753347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277458289865330510439671129 208093717398997882829753347)
    ·
      refine ⟨312140576098496824244630021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208093717398997882829753347 312140576098496824244630021)
      ·
        refine ⟨58526358018468154545868129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312140576098496824244630021 58526358018468154545868129)
        ·
          refine ⟨43894768513851115909401097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58526358018468154545868129 43894768513851115909401097)
          ·
            refine ⟨32921076385388336932050823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43894768513851115909401097 32921076385388336932050823)
            ·
              refine ⟨49381614578082505398076235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32921076385388336932050823 49381614578082505398076235)
              ·
                refine ⟨74072421867123758097114353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49381614578082505398076235 74072421867123758097114353)
                ·
                  refine ⟨55554316400342818572835765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74072421867123758097114353 55554316400342818572835765)
                  ·
                    refine ⟨5208217162532139241203353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55554316400342818572835765 5208217162532139241203353)
                    ·
                      refine ⟨3906162871899104430902515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208217162532139241203353 3906162871899104430902515)
                      ·
                        rfl

theorem cell23_7607225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7607225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607225 prefixEnd_7607225 := by exact prefixLift 7607225
  have htrace : WordTrace (prefixWord ++ tailWord_7607225) baseStart_7607225 baseEnd_7607225 := by
    simpa [prefixWord, tailWord_7607225, baseEnd_7607225] using wordTrace_append hprefix tailTrace_7607225
  have hstable : (prefixWord ++ tailWord_7607225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607225).length < 2 ^ (prefixWord ++ tailWord_7607225).sum := by decide
  have hdescent : baseEnd_7607225 < baseStart_7607225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607252 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_7607252 : Nat := 118140960795 + 7607252 * 2 ^ 59
def prefixEnd_7607252 : Nat := 4983230072969 + 3 ^ 40 * 7607252 * 2
def baseEnd_7607252 : Nat := 1302058911958925275088297

theorem tailTrace_7607252 : CollatzResearch.WordTrace tailWord_7607252 prefixEnd_7607252 1302058911958925275088297 := by
  unfold tailWord_7607252
  simp only [CollatzResearch.WordTrace]
  refine ⟨138729637318116347025452005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184972849757488462700602673 138729637318116347025452005)
  ·
    refine ⟨26011806997146815067272251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138729637318116347025452005 26011806997146815067272251)
    ·
      refine ⟨39017710495720222600908377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26011806997146815067272251 39017710495720222600908377)
      ·
        refine ⟨29263282871790166950681283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39017710495720222600908377 29263282871790166950681283)
        ·
          refine ⟨43894924307685250426021925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29263282871790166950681283 43894924307685250426021925)
          ·
            refine ⟨8230298307690984454879111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43894924307685250426021925 8230298307690984454879111)
            ·
              refine ⟨12345447461536476682318667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230298307690984454879111 12345447461536476682318667)
              ·
                refine ⟨18518171192304715023478001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12345447461536476682318667 18518171192304715023478001)
                ·
                  refine ⟨13888628394228536267608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18518171192304715023478001 13888628394228536267608501)
                  ·
                    refine ⟨1302058911958925275088297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13888628394228536267608501 1302058911958925275088297)
                    ·
                      rfl

theorem cell23_7607252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_7607252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607252 prefixEnd_7607252 := by exact prefixLift 7607252
  have htrace : WordTrace (prefixWord ++ tailWord_7607252) baseStart_7607252 baseEnd_7607252 := by
    simpa [prefixWord, tailWord_7607252, baseEnd_7607252] using wordTrace_append hprefix tailTrace_7607252
  have hstable : (prefixWord ++ tailWord_7607252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607252).length < 2 ^ (prefixWord ++ tailWord_7607252).sum := by decide
  have hdescent : baseEnd_7607252 < baseStart_7607252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607345 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7607345 : Nat := 118140960795 + 7607345 * 2 ^ 59
def prefixEnd_7607345 : Nat := 4983230072969 + 3 ^ 40 * 7607345 * 2
def baseEnd_7607345 : Nat := 3906224489577643961401963

theorem tailTrace_7607345 : CollatzResearch.WordTrace tailWord_7607345 prefixEnd_7607345 3906224489577643961401963 := by
  unfold tailWord_7607345
  simp only [CollatzResearch.WordTrace]
  refine ⟨277462666624895770934039489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184975111083263847289359659 277462666624895770934039489)
  ·
    refine ⟨208096999968671828200529617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277462666624895770934039489 208096999968671828200529617)
    ·
      refine ⟨156072749976503871150397213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208096999968671828200529617 156072749976503871150397213)
      ·
        refine ⟨58527281241188951681398955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156072749976503871150397213 58527281241188951681398955)
        ·
          refine ⟨87790921861783427522098433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58527281241188951681398955 87790921861783427522098433)
          ·
            refine ⟨65843191396337570641573825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87790921861783427522098433 65843191396337570641573825)
            ·
              refine ⟨49382393547253177981180369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65843191396337570641573825 49382393547253177981180369)
              ·
                refine ⟨37036795160439883485885277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49382393547253177981180369 37036795160439883485885277)
                ·
                  refine ⟨13888798185164956307206979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37036795160439883485885277 13888798185164956307206979)
                  ·
                    refine ⟨20833197277747434460810469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13888798185164956307206979 20833197277747434460810469)
                    ·
                      refine ⟨3906224489577643961401963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20833197277747434460810469 3906224489577643961401963)
                      ·
                        rfl

theorem cell23_7607345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7607345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607345 prefixEnd_7607345 := by exact prefixLift 7607345
  have htrace : WordTrace (prefixWord ++ tailWord_7607345) baseStart_7607345 baseEnd_7607345 := by
    simpa [prefixWord, tailWord_7607345, baseEnd_7607345] using wordTrace_append hprefix tailTrace_7607345
  have hstable : (prefixWord ++ tailWord_7607345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607345).length < 2 ^ (prefixWord ++ tailWord_7607345).sum := by decide
  have hdescent : baseEnd_7607345 < baseStart_7607345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607366 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7607366 : Nat := 118140960795 + 7607366 * 2 ^ 59
def prefixEnd_7607366 : Nat := 4983230072969 + 3 ^ 40 * 7607366 * 2
def baseEnd_7607366 : Nat := 3906235272671388379239367

theorem tailTrace_7607366 : CollatzResearch.WordTrace tailWord_7607366 prefixEnd_7607366 3906235272671388379239367 := by
  unfold tailWord_7607366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8670732267431865360017311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184975621705213127680369301 8670732267431865360017311)
  ·
    refine ⟨13006098401147798040025967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8670732267431865360017311 13006098401147798040025967)
    ·
      refine ⟨19509147601721697060038951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13006098401147798040025967 19509147601721697060038951)
      ·
        refine ⟨29263721402582545590058427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19509147601721697060038951 29263721402582545590058427)
        ·
          refine ⟨43895582103873818385087641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29263721402582545590058427 43895582103873818385087641)
          ·
            refine ⟨32921686577905363788815731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43895582103873818385087641 32921686577905363788815731)
            ·
              refine ⟨49382529866858045683223597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32921686577905363788815731 49382529866858045683223597)
              ·
                refine ⟨18518448700071767131208849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49382529866858045683223597 18518448700071767131208849)
                ·
                  refine ⟨13888836525053825348406637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18518448700071767131208849 13888836525053825348406637)
                  ·
                    refine ⟨5208313696895184505652489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13888836525053825348406637 5208313696895184505652489)
                    ·
                      refine ⟨3906235272671388379239367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208313696895184505652489 3906235272671388379239367)
                      ·
                        rfl

theorem cell23_7607366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7607366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607366 prefixEnd_7607366 := by exact prefixLift 7607366
  have htrace : WordTrace (prefixWord ++ tailWord_7607366) baseStart_7607366 baseEnd_7607366 := by
    simpa [prefixWord, tailWord_7607366, baseEnd_7607366] using wordTrace_append hprefix tailTrace_7607366
  have hstable : (prefixWord ++ tailWord_7607366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607366).length < 2 ^ (prefixWord ++ tailWord_7607366).sum := by decide
  have hdescent : baseEnd_7607366 < baseStart_7607366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607368 : List Nat := [2, 1, 3, 1, 1, 1, 3, 11]
def baseStart_7607368 : Nat := 118140960795 + 7607368 * 2 ^ 59
def prefixEnd_7607368 : Nat := 4983230072969 + 3 ^ 40 * 7607368 * 2
def baseEnd_7607368 : Nat := 144675418504914717459791

theorem tailTrace_7607368 : CollatzResearch.WordTrace tailWord_7607368 prefixEnd_7607368 144675418504914717459791 := by
  unfold tailWord_7607368
  simp only [CollatzResearch.WordTrace]
  refine ⟨138731752751906222931063379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184975670335874963908084505 138731752751906222931063379)
  ·
    refine ⟨208097629127859334396595069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138731752751906222931063379 208097629127859334396595069)
    ·
      refine ⟨78036610922947250398723151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208097629127859334396595069 78036610922947250398723151)
      ·
        refine ⟨117054916384420875598084727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78036610922947250398723151 117054916384420875598084727)
        ·
          refine ⟨175582374576631313397127091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117054916384420875598084727 175582374576631313397127091)
          ·
            refine ⟨263373561864946970095690637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175582374576631313397127091 263373561864946970095690637)
            ·
              refine ⟨98765085699355113785883989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263373561864946970095690637 98765085699355113785883989)
              ·
                refine ⟨144675418504914717459791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98765085699355113785883989 144675418504914717459791)
                ·
                  rfl

theorem cell23_7607368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 11].length) (baseStart_7607368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607368 prefixEnd_7607368 := by exact prefixLift 7607368
  have htrace : WordTrace (prefixWord ++ tailWord_7607368) baseStart_7607368 baseEnd_7607368 := by
    simpa [prefixWord, tailWord_7607368, baseEnd_7607368] using wordTrace_append hprefix tailTrace_7607368
  have hstable : (prefixWord ++ tailWord_7607368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607368).length < 2 ^ (prefixWord ++ tailWord_7607368).sum := by decide
  have hdescent : baseEnd_7607368 < baseStart_7607368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607390 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_7607390 : Nat := 118140960795 + 7607390 * 2 ^ 59
def prefixEnd_7607390 : Nat := 4983230072969 + 3 ^ 40 * 7607390 * 2
def baseEnd_7607390 : Nat := 3906247596207096285339257

theorem tailTrace_7607390 : CollatzResearch.WordTrace tailWord_7607390 prefixEnd_7607390 3906247596207096285339257 := by
  unfold tailWord_7607390
  simp only [CollatzResearch.WordTrace]
  refine ⟨34683038488716592952428453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184976205273155162412951749 34683038488716592952428453)
  ·
    refine ⟨6503069716634361178580335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34683038488716592952428453 6503069716634361178580335)
    ·
      refine ⟨9754604574951541767870503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6503069716634361178580335 9754604574951541767870503)
      ·
        refine ⟨14631906862427312651805755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754604574951541767870503 14631906862427312651805755)
        ·
          refine ⟨21947860293640968977708633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14631906862427312651805755 21947860293640968977708633)
          ·
            refine ⟨16460895220230726733281475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21947860293640968977708633 16460895220230726733281475)
            ·
              refine ⟨24691342830346090099922213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460895220230726733281475 24691342830346090099922213)
              ·
                refine ⟨4629626780689891893735415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24691342830346090099922213 4629626780689891893735415)
                ·
                  refine ⟨6944440171034837840603123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629626780689891893735415 6944440171034837840603123)
                  ·
                    refine ⟨10416660256552256760904685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6944440171034837840603123 10416660256552256760904685)
                    ·
                      refine ⟨3906247596207096285339257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416660256552256760904685 3906247596207096285339257)
                      ·
                        rfl

theorem cell23_7607390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_7607390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607390 prefixEnd_7607390 := by exact prefixLift 7607390
  have htrace : WordTrace (prefixWord ++ tailWord_7607390) baseStart_7607390 baseEnd_7607390 := by
    simpa [prefixWord, tailWord_7607390, baseEnd_7607390] using wordTrace_append hprefix tailTrace_7607390
  have hstable : (prefixWord ++ tailWord_7607390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607390).length < 2 ^ (prefixWord ++ tailWord_7607390).sum := by decide
  have hdescent : baseEnd_7607390 < baseStart_7607390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607395 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3]
def baseStart_7607395 : Nat := 118140960795 + 7607395 * 2 ^ 59
def prefixEnd_7607395 : Nat := 4983230072969 + 3 ^ 40 * 7607395 * 2
def baseEnd_7607395 : Nat := 3906250163610368765776733

theorem tailTrace_7607395 : CollatzResearch.WordTrace tailWord_7607395 prefixEnd_7607395 3906250163610368765776733 := by
  unfold tailWord_7607395
  simp only [CollatzResearch.WordTrace]
  refine ⟨277464490274714629473359639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184976326849809752982239759 277464490274714629473359639)
  ·
    refine ⟨416196735412071944210039459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277464490274714629473359639 416196735412071944210039459)
    ·
      refine ⟨624295103118107916315059189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416196735412071944210039459 624295103118107916315059189)
      ·
        refine ⟨58527665917322617154536799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624295103118107916315059189 58527665917322617154536799)
        ·
          refine ⟨87791498875983925731805199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58527665917322617154536799 87791498875983925731805199)
          ·
            refine ⟨131687248313975888597707799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87791498875983925731805199 131687248313975888597707799)
            ·
              refine ⟨197530872470963832896561699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131687248313975888597707799 197530872470963832896561699)
              ·
                refine ⟨296296308706445749344842549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197530872470963832896561699 296296308706445749344842549)
                ·
                  refine ⟨27777778941229289001078989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296296308706445749344842549 27777778941229289001078989)
                  ·
                    refine ⟨10416667102960983375404621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27777778941229289001078989 10416667102960983375404621)
                    ·
                      refine ⟨3906250163610368765776733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416667102960983375404621 3906250163610368765776733)
                      ·
                        rfl

theorem cell23_7607395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_7607395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607395 prefixEnd_7607395 := by exact prefixLift 7607395
  have htrace : WordTrace (prefixWord ++ tailWord_7607395) baseStart_7607395 baseEnd_7607395 := by
    simpa [prefixWord, tailWord_7607395, baseEnd_7607395] using wordTrace_append hprefix tailTrace_7607395
  have hstable : (prefixWord ++ tailWord_7607395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607395).length < 2 ^ (prefixWord ++ tailWord_7607395).sum := by decide
  have hdescent : baseEnd_7607395 < baseStart_7607395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607402 : List Nat := [3, 1, 3, 2, 2, 3, 1, 8]
def baseStart_7607402 : Nat := 118140960795 + 7607402 * 2 ^ 59
def prefixEnd_7607402 : Nat := 4983230072969 + 3 ^ 40 * 7607402 * 2
def baseEnd_7607402 : Nat := 144676065110183342162563

theorem tailTrace_7607402 : CollatzResearch.WordTrace tailWord_7607402 prefixEnd_7607402 144676065110183342162563 := by
  unfold tailWord_7607402
  simp only [CollatzResearch.WordTrace]
  refine ⟨69366186396422317417216115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184976497057126179779242973 69366186396422317417216115)
  ·
    refine ⟨104049279594633476125824173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69366186396422317417216115 104049279594633476125824173)
    ·
      refine ⟨39018479847987553547184065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104049279594633476125824173 39018479847987553547184065)
      ·
        refine ⟨29263859885990665160388049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39018479847987553547184065 29263859885990665160388049)
        ·
          refine ⟨21947894914492998870291037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29263859885990665160388049 21947894914492998870291037)
          ·
            refine ⟨8230460592934874576359139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21947894914492998870291037 8230460592934874576359139)
            ·
              refine ⟨12345690889402311864538709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230460592934874576359139 12345690889402311864538709)
              ·
                refine ⟨144676065110183342162563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12345690889402311864538709 144676065110183342162563)
                ·
                  rfl

theorem cell23_7607402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_7607402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607402 prefixEnd_7607402 := by exact prefixLift 7607402
  have htrace : WordTrace (prefixWord ++ tailWord_7607402) baseStart_7607402 baseEnd_7607402 := by
    simpa [prefixWord, tailWord_7607402, baseEnd_7607402] using wordTrace_append hprefix tailTrace_7607402
  have hstable : (prefixWord ++ tailWord_7607402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607402).length < 2 ^ (prefixWord ++ tailWord_7607402).sum := by decide
  have hdescent : baseEnd_7607402 < baseStart_7607402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607413 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7607413 : Nat := 118140960795 + 7607413 * 2 ^ 59
def prefixEnd_7607413 : Nat := 4983230072969 + 3 ^ 40 * 7607413 * 2
def baseEnd_7607413 : Nat := 3906259406262149695351651

theorem tailTrace_7607413 : CollatzResearch.WordTrace tailWord_7607413 prefixEnd_7607413 3906259406262149695351651 := by
  unfold tailWord_7607413
  simp only [CollatzResearch.WordTrace]
  refine ⟨277465146788649418547514893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184976764525766279031676595 277465146788649418547514893)
  ·
    refine ⟨104049430045743531955318085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277465146788649418547514893 104049430045743531955318085)
    ·
      refine ⟨19509268133576912241622141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104049430045743531955318085 19509268133576912241622141)
      ·
        refine ⟨7315975550091342090608303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19509268133576912241622141 7315975550091342090608303)
        ·
          refine ⟨10973963325137013135912455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7315975550091342090608303 10973963325137013135912455)
          ·
            refine ⟨16460944987705519703868683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10973963325137013135912455 16460944987705519703868683)
            ·
              refine ⟨24691417481558279555803025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16460944987705519703868683 24691417481558279555803025)
              ·
                refine ⟨18518563111168709666852269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24691417481558279555803025 18518563111168709666852269)
                ·
                  refine ⟨6944461166688266125069601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18518563111168709666852269 6944461166688266125069601)
                  ·
                    refine ⟨5208345875016199593802201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6944461166688266125069601 5208345875016199593802201)
                    ·
                      refine ⟨3906259406262149695351651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208345875016199593802201 3906259406262149695351651)
                      ·
                        rfl

theorem cell23_7607413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7607413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607413 prefixEnd_7607413 := by exact prefixLift 7607413
  have htrace : WordTrace (prefixWord ++ tailWord_7607413) baseStart_7607413 baseEnd_7607413 := by
    simpa [prefixWord, tailWord_7607413, baseEnd_7607413] using wordTrace_append hprefix tailTrace_7607413
  have hstable : (prefixWord ++ tailWord_7607413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607413).length < 2 ^ (prefixWord ++ tailWord_7607413).sum := by decide
  have hdescent : baseEnd_7607413 < baseStart_7607413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607463 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_7607463 : Nat := 118140960795 + 7607463 * 2 ^ 59
def prefixEnd_7607463 : Nat := 4983230072969 + 3 ^ 40 * 7607463 * 2
def baseEnd_7607463 : Nat := 3906285080294874499726421

theorem tailTrace_7607463 : CollatzResearch.WordTrace tailWord_7607463 prefixEnd_7607463 3906285080294874499726421 := by
  unfold tailWord_7607463
  simp only [CollatzResearch.WordTrace]
  refine ⟨277466970438468277086835043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184977980292312184724556695 277466970438468277086835043)
  ·
    refine ⟨416200455657702415630252565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277466970438468277086835043 416200455657702415630252565)
    ·
      refine ⟨19509396358954800732668089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 416200455657702415630252565 19509396358954800732668089)
      ·
        refine ⟨14632047269216100549501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19509396358954800732668089 14632047269216100549501067)
        ·
          refine ⟨21948070903824150824251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632047269216100549501067 21948070903824150824251601)
          ·
            refine ⟨16461053177868113118188701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21948070903824150824251601 16461053177868113118188701)
            ·
              refine ⟨6172894941700542419320763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16461053177868113118188701 6172894941700542419320763)
              ·
                refine ⟨9259342412550813628981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172894941700542419320763 9259342412550813628981145)
                ·
                  refine ⟨6944506809413110221735859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9259342412550813628981145 6944506809413110221735859)
                  ·
                    refine ⟨10416760214119665332603789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6944506809413110221735859 10416760214119665332603789)
                    ·
                      refine ⟨3906285080294874499726421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416760214119665332603789 3906285080294874499726421)
                      ·
                        rfl

theorem cell23_7607463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_7607463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607463 prefixEnd_7607463 := by exact prefixLift 7607463
  have htrace : WordTrace (prefixWord ++ tailWord_7607463) baseStart_7607463 baseEnd_7607463 := by
    simpa [prefixWord, tailWord_7607463, baseEnd_7607463] using wordTrace_append hprefix tailTrace_7607463
  have hstable : (prefixWord ++ tailWord_7607463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607463).length < 2 ^ (prefixWord ++ tailWord_7607463).sum := by decide
  have hdescent : baseEnd_7607463 < baseStart_7607463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607475 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 7]
def baseStart_7607475 : Nat := 118140960795 + 7607475 * 2 ^ 59
def prefixEnd_7607475 : Nat := 4983230072969 + 3 ^ 40 * 7607475 * 2
def baseEnd_7607475 : Nat := 434032360229192050308485

theorem tailTrace_7607475 : CollatzResearch.WordTrace tailWord_7607475 prefixEnd_7607475 434032360229192050308485 := by
  unfold tailWord_7607475
  simp only [CollatzResearch.WordTrace]
  refine ⟨277467408114424803136271879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184978272076283202090847919 277467408114424803136271879)
  ·
    refine ⟨416201112171637204704407819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277467408114424803136271879 416201112171637204704407819)
    ·
      refine ⟨624301668257455807056611729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416201112171637204704407819 624301668257455807056611729)
      ·
        refine ⟨468226251193091855292458797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624301668257455807056611729 468226251193091855292458797)
        ·
          refine ⟨175584844197409445734672049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468226251193091855292458797 175584844197409445734672049)
          ·
            refine ⟨131688633148057084301004037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175584844197409445734672049 131688633148057084301004037)
            ·
              refine ⟨24691618715260703306438257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131688633148057084301004037 24691618715260703306438257)
              ·
                refine ⟨18518714036445527479828693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24691618715260703306438257 18518714036445527479828693)
                ·
                  refine ⟨434032360229192050308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18518714036445527479828693 434032360229192050308485)
                  ·
                    rfl

theorem cell23_7607475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 7].length) (baseStart_7607475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607475 prefixEnd_7607475 := by exact prefixLift 7607475
  have htrace : WordTrace (prefixWord ++ tailWord_7607475) baseStart_7607475 baseEnd_7607475 := by
    simpa [prefixWord, tailWord_7607475, baseEnd_7607475] using wordTrace_append hprefix tailTrace_7607475
  have hstable : (prefixWord ++ tailWord_7607475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607475).length < 2 ^ (prefixWord ++ tailWord_7607475).sum := by decide
  have hdescent : baseEnd_7607475 < baseStart_7607475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607486 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_7607486 : Nat := 118140960795 + 7607486 * 2 ^ 59
def prefixEnd_7607486 : Nat := 4983230072969 + 3 ^ 40 * 7607486 * 2
def baseEnd_7607486 : Nat := 3906296890349927909738815

theorem tailTrace_7607486 : CollatzResearch.WordTrace tailWord_7607486 prefixEnd_7607486 3906296890349927909738815 := by
  unfold tailWord_7607486
  simp only [CollatzResearch.WordTrace]
  refine ⟨34683476164673119001865289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184978539544923301343281541 34683476164673119001865289)
  ·
    refine ⟨26012607123504839251398967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34683476164673119001865289 26012607123504839251398967)
    ·
      refine ⟨39018910685257258877098451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012607123504839251398967 39018910685257258877098451)
      ·
        refine ⟨58528366027885888315647677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39018910685257258877098451 58528366027885888315647677)
        ·
          refine ⟨21948137260457208118367879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58528366027885888315647677 21948137260457208118367879)
          ·
            refine ⟨32922205890685812177551819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21948137260457208118367879 32922205890685812177551819)
            ·
              refine ⟨49383308836028718266327729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32922205890685812177551819 49383308836028718266327729)
              ·
                refine ⟨37037481627021538699745797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49383308836028718266327729 37037481627021538699745797)
                ·
                  refine ⟨6944527805066538506202337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37037481627021538699745797 6944527805066538506202337)
                  ·
                    refine ⟨5208395853799903879651753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6944527805066538506202337 5208395853799903879651753)
                    ·
                      refine ⟨3906296890349927909738815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208395853799903879651753 3906296890349927909738815)
                      ·
                        rfl

theorem cell23_7607486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_7607486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607486 prefixEnd_7607486 := by exact prefixLift 7607486
  have htrace : WordTrace (prefixWord ++ tailWord_7607486) baseStart_7607486 baseEnd_7607486 := by
    simpa [prefixWord, tailWord_7607486, baseEnd_7607486] using wordTrace_append hprefix tailTrace_7607486
  have hstable : (prefixWord ++ tailWord_7607486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607486).length < 2 ^ (prefixWord ++ tailWord_7607486).sum := by decide
  have hdescent : baseEnd_7607486 < baseStart_7607486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607489 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_7607489 : Nat := 118140960795 + 7607489 * 2 ^ 59
def prefixEnd_7607489 : Nat := 4983230072969 + 3 ^ 40 * 7607489 * 2
def baseEnd_7607489 : Nat := 3906298430791891398001301

theorem tailTrace_7607489 : CollatzResearch.WordTrace tailWord_7607489 prefixEnd_7607489 3906298430791891398001301 := by
  unfold tailWord_7607489
  simp only [CollatzResearch.WordTrace]
  refine ⟨277467918736374083527281521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184978612490916055684854347 277467918736374083527281521)
  ·
    refine ⟨208100939052280562645461141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277467918736374083527281521 208100939052280562645461141)
    ·
      refine ⟨9754731518075651374005991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208100939052280562645461141 9754731518075651374005991)
      ·
        refine ⟨14632097277113477061008987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9754731518075651374005991 14632097277113477061008987)
        ·
          refine ⟨21948145915670215591513481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632097277113477061008987 21948145915670215591513481)
          ·
            refine ⟨16461109436752661693635111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21948145915670215591513481 16461109436752661693635111)
            ·
              refine ⟨24691664155128992540452667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461109436752661693635111 24691664155128992540452667)
              ·
                refine ⟨37037496232693488810679001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24691664155128992540452667 37037496232693488810679001)
                ·
                  refine ⟨27778122174520116608009251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37037496232693488810679001 27778122174520116608009251)
                  ·
                    refine ⟨41667183261780174912013877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27778122174520116608009251 41667183261780174912013877)
                    ·
                      refine ⟨3906298430791891398001301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41667183261780174912013877 3906298430791891398001301)
                      ·
                        rfl

theorem cell23_7607489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_7607489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607489 prefixEnd_7607489 := by exact prefixLift 7607489
  have htrace : WordTrace (prefixWord ++ tailWord_7607489) baseStart_7607489 baseEnd_7607489 := by
    simpa [prefixWord, tailWord_7607489, baseEnd_7607489] using wordTrace_append hprefix tailTrace_7607489
  have hstable : (prefixWord ++ tailWord_7607489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607489).length < 2 ^ (prefixWord ++ tailWord_7607489).sum := by decide
  have hdescent : baseEnd_7607489 < baseStart_7607489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607509 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 7]
def baseStart_7607509 : Nat := 118140960795 + 7607509 * 2 ^ 59
def prefixEnd_7607509 : Nat := 4983230072969 + 3 ^ 40 * 7607509 * 2
def baseEnd_7607509 : Nat := 434034300044997924416801

theorem tailTrace_7607509 : CollatzResearch.WordTrace tailWord_7607509 prefixEnd_7607509 434034300044997924416801 := by
  unfold tailWord_7607509
  simp only [CollatzResearch.WordTrace]
  refine ⟨277468648196301626943009581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184979098797534417962006387 277468648196301626943009581)
  ·
    refine ⟨104050743073613110103628593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277468648196301626943009581 104050743073613110103628593)
    ·
      refine ⟨78038057305209832577721445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104050743073613110103628593 78038057305209832577721445)
      ·
        refine ⟨14632135744726843608322771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78038057305209832577721445 14632135744726843608322771)
        ·
          refine ⟨21948203617090265412484157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14632135744726843608322771 21948203617090265412484157)
          ·
            refine ⟨8230576356408849529681559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21948203617090265412484157 8230576356408849529681559)
            ·
              refine ⟨12345864534613274294522339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230576356408849529681559 12345864534613274294522339)
              ·
                refine ⟨18518796801919911441783509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12345864534613274294522339 18518796801919911441783509)
                ·
                  refine ⟨434034300044997924416801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18518796801919911441783509 434034300044997924416801)
                  ·
                    rfl

theorem cell23_7607509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_7607509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607509 prefixEnd_7607509 := by exact prefixLift 7607509
  have htrace : WordTrace (prefixWord ++ tailWord_7607509) baseStart_7607509 baseEnd_7607509 := by
    simpa [prefixWord, tailWord_7607509, baseEnd_7607509] using wordTrace_append hprefix tailTrace_7607509
  have hstable : (prefixWord ++ tailWord_7607509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607509).length < 2 ^ (prefixWord ++ tailWord_7607509).sum := by decide
  have hdescent : baseEnd_7607509 < baseStart_7607509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607562 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_7607562 : Nat := 118140960795 + 7607562 * 2 ^ 59
def prefixEnd_7607562 : Nat := 4983230072969 + 3 ^ 40 * 7607562 * 2
def baseEnd_7607562 : Nat := 3906335914879669612388465

theorem tailTrace_7607562 : CollatzResearch.WordTrace tailWord_7607562 prefixEnd_7607562 3906335914879669612388465 := by
  unfold tailWord_7607562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69367645316277404248672235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184980387510073077996459293 69367645316277404248672235)
  ·
    refine ⟨104051467974416106373008353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69367645316277404248672235 104051467974416106373008353)
    ·
      refine ⟨78038600980812079779756265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104051467974416106373008353 78038600980812079779756265)
      ·
        refine ⟨58528950735609059834817199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78038600980812079779756265 58528950735609059834817199)
        ·
          refine ⟨87793426103413589752225799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58528950735609059834817199 87793426103413589752225799)
          ·
            refine ⟨131690139155120384628338699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87793426103413589752225799 131690139155120384628338699)
            ·
              refine ⟨197535208732680576942508049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131690139155120384628338699 197535208732680576942508049)
              ·
                refine ⟨148151406549510432706881037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197535208732680576942508049 148151406549510432706881037)
                ·
                  refine ⟨55556777456066412265080389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148151406549510432706881037 55556777456066412265080389)
                  ·
                    refine ⟨10416895773012452299702573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55556777456066412265080389 10416895773012452299702573)
                    ·
                      refine ⟨3906335914879669612388465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10416895773012452299702573 3906335914879669612388465)
                      ·
                        rfl

theorem cell23_7607562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_7607562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607562 prefixEnd_7607562 := by exact prefixLift 7607562
  have htrace : WordTrace (prefixWord ++ tailWord_7607562) baseStart_7607562 baseEnd_7607562 := by
    simpa [prefixWord, tailWord_7607562, baseEnd_7607562] using wordTrace_append hprefix tailTrace_7607562
  have hstable : (prefixWord ++ tailWord_7607562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607562).length < 2 ^ (prefixWord ++ tailWord_7607562).sum := by decide
  have hdescent : baseEnd_7607562 < baseStart_7607562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607586 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7607586 : Nat := 118140960795 + 7607586 * 2 ^ 59
def prefixEnd_7607586 : Nat := 4983230072969 + 3 ^ 40 * 7607586 * 2
def baseEnd_7607586 : Nat := 1302116079471792506162785

theorem tailTrace_7607586 : CollatzResearch.WordTrace tailWord_7607586 prefixEnd_7607586 1302116079471792506162785 := by
  unfold tailWord_7607586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69367864154255667273390653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184980971078015112729041741 69367864154255667273390653)
  ·
    refine ⟨26012949057845875227521495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69367864154255667273390653 26012949057845875227521495)
    ·
      refine ⟨39019423586768812841282243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26012949057845875227521495 39019423586768812841282243)
      ·
        refine ⟨58529135380153219261923365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39019423586768812841282243 58529135380153219261923365)
        ·
          refine ⟨10974212883778728611610631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58529135380153219261923365 10974212883778728611610631)
          ·
            refine ⟨16461319325668092917415947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974212883778728611610631 16461319325668092917415947)
            ·
              refine ⟨24691978988502139376123921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16461319325668092917415947 24691978988502139376123921)
              ·
                refine ⟨18518984241376604532092941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24691978988502139376123921 18518984241376604532092941)
                ·
                  refine ⟨6944619090516226699534853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18518984241376604532092941 6944619090516226699534853)
                  ·
                    refine ⟨1302116079471792506162785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6944619090516226699534853 1302116079471792506162785)
                    ·
                      rfl

theorem cell23_7607586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7607586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607586 prefixEnd_7607586 := by exact prefixLift 7607586
  have htrace : WordTrace (prefixWord ++ tailWord_7607586) baseStart_7607586 baseEnd_7607586 := by
    simpa [prefixWord, tailWord_7607586, baseEnd_7607586] using wordTrace_append hprefix tailTrace_7607586
  have hstable : (prefixWord ++ tailWord_7607586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607586).length < 2 ^ (prefixWord ++ tailWord_7607586).sum := by decide
  have hdescent : baseEnd_7607586 < baseStart_7607586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607595 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 9]
def baseStart_7607595 : Nat := 118140960795 + 7607595 * 2 ^ 59
def prefixEnd_7607595 : Nat := 4983230072969 + 3 ^ 40 * 7607595 * 2
def baseEnd_7607595 : Nat := 1302117619913755994425271

theorem tailTrace_7607595 : CollatzResearch.WordTrace tailWord_7607595 prefixEnd_7607595 1302117619913755994425271 := by
  unfold tailWord_7607595
  simp only [CollatzResearch.WordTrace]
  refine ⟨277471784873990063630640239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184981189915993375753760159 277471784873990063630640239)
  ·
    refine ⟨416207677310985095445960359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277471784873990063630640239 416207677310985095445960359)
    ·
      refine ⟨624311515966477643168940539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416207677310985095445960359 624311515966477643168940539)
      ·
        refine ⟨936467273949716464753410809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624311515966477643168940539 936467273949716464753410809)
        ·
          refine ⟨702350455462287348565058107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936467273949716464753410809 702350455462287348565058107)
          ·
            refine ⟨1053525683193431022847587161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702350455462287348565058107 1053525683193431022847587161)
            ·
              refine ⟨790144262395073267135690371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053525683193431022847587161 790144262395073267135690371)
              ·
                refine ⟨1185216393592609900703535557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790144262395073267135690371 1185216393592609900703535557)
                ·
                  refine ⟨222228073798614356381912917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1185216393592609900703535557 222228073798614356381912917)
                  ·
                    refine ⟨1302117619913755994425271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222228073798614356381912917 1302117619913755994425271)
                    ·
                      rfl

theorem cell23_7607595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 9].length) (baseStart_7607595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607595 prefixEnd_7607595 := by exact prefixLift 7607595
  have htrace : WordTrace (prefixWord ++ tailWord_7607595) baseStart_7607595 baseEnd_7607595 := by
    simpa [prefixWord, tailWord_7607595, baseEnd_7607595] using wordTrace_append hprefix tailTrace_7607595
  have hstable : (prefixWord ++ tailWord_7607595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607595).length < 2 ^ (prefixWord ++ tailWord_7607595).sum := by decide
  have hdescent : baseEnd_7607595 < baseStart_7607595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 4, 3, 2]
def baseStart_7607619 : Nat := 118140960795 + 7607619 * 2 ^ 59
def prefixEnd_7607619 : Nat := 4983230072969 + 3 ^ 40 * 7607619 * 2
def baseEnd_7607619 : Nat := 3906365183276975889375703

theorem tailTrace_7607619 : CollatzResearch.WordTrace tailWord_7607619 prefixEnd_7607619 3906365183276975889375703 := by
  unfold tailWord_7607619
  simp only [CollatzResearch.WordTrace]
  refine ⟨277472660225903115729513911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184981773483935410486342607 277472660225903115729513911)
  ·
    refine ⟨416208990338854673594270867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277472660225903115729513911 416208990338854673594270867)
    ·
      refine ⟨624313485508282010391406301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416208990338854673594270867 624313485508282010391406301)
      ·
        refine ⟨234117557065605753896777363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624313485508282010391406301 234117557065605753896777363)
        ·
          refine ⟨351176335598408630845166045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234117557065605753896777363 351176335598408630845166045)
          ·
            refine ⟨131691125849403236566937267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351176335598408630845166045 131691125849403236566937267)
            ·
              refine ⟨197536688774104854850405901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131691125849403236566937267 197536688774104854850405901)
              ·
                refine ⟨74076258290289320568902213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197536688774104854850405901 74076258290289320568902213)
                ·
                  refine ⟨13889298429429247606669165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74076258290289320568902213 13889298429429247606669165)
                  ·
                    refine ⟨5208486911035967852500937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13889298429429247606669165 5208486911035967852500937)
                    ·
                      refine ⟨3906365183276975889375703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208486911035967852500937 3906365183276975889375703)
                      ·
                        rfl

theorem cell23_7607619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_7607619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607619 prefixEnd_7607619 := by exact prefixLift 7607619
  have htrace : WordTrace (prefixWord ++ tailWord_7607619) baseStart_7607619 baseEnd_7607619 := by
    simpa [prefixWord, tailWord_7607619, baseEnd_7607619] using wordTrace_append hprefix tailTrace_7607619
  have hstable : (prefixWord ++ tailWord_7607619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607619).length < 2 ^ (prefixWord ++ tailWord_7607619).sum := by decide
  have hdescent : baseEnd_7607619 < baseStart_7607619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607660 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_7607660 : Nat := 118140960795 + 7607660 * 2 ^ 59
def prefixEnd_7607660 : Nat := 4983230072969 + 3 ^ 40 * 7607660 * 2
def baseEnd_7607660 : Nat := 3906386235983810228963015

theorem tailTrace_7607660 : CollatzResearch.WordTrace tailWord_7607660 prefixEnd_7607660 3906386235983810228963015 := by
  unfold tailWord_7607660
  simp only [CollatzResearch.WordTrace]
  refine ⟨138737077809377289865878217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184982770412503053154504289 138737077809377289865878217)
  ·
    refine ⟨104052808357032967399408663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138737077809377289865878217 104052808357032967399408663)
    ·
      refine ⟨156079212535549451099112995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104052808357032967399408663 156079212535549451099112995)
      ·
        refine ⟨234118818803324176648669493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156079212535549451099112995 234118818803324176648669493)
        ·
          refine ⟨21948639262811641560812765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234118818803324176648669493 21948639262811641560812765)
          ·
            refine ⟨8230739723554365585304787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21948639262811641560812765 8230739723554365585304787)
            ·
              refine ⟨12346109585331548377957181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230739723554365585304787 12346109585331548377957181)
              ·
                refine ⟨4629791094499330641733943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12346109585331548377957181 4629791094499330641733943)
                ·
                  refine ⟨6944686641748995962600915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629791094499330641733943 6944686641748995962600915)
                  ·
                    refine ⟨10417029962623493943901373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6944686641748995962600915 10417029962623493943901373)
                    ·
                      refine ⟨3906386235983810228963015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417029962623493943901373 3906386235983810228963015)
                      ·
                        rfl

theorem cell23_7607660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_7607660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607660 prefixEnd_7607660 := by exact prefixLift 7607660
  have htrace : WordTrace (prefixWord ++ tailWord_7607660) baseStart_7607660 baseEnd_7607660 := by
    simpa [prefixWord, tailWord_7607660, baseEnd_7607660] using wordTrace_append hprefix tailTrace_7607660
  have hstable : (prefixWord ++ tailWord_7607660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607660).length < 2 ^ (prefixWord ++ tailWord_7607660).sum := by decide
  have hdescent : baseEnd_7607660 < baseStart_7607660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607683 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 3, 2, 2]
def baseStart_7607683 : Nat := 118140960795 + 7607683 * 2 ^ 59
def prefixEnd_7607683 : Nat := 4983230072969 + 3 ^ 40 * 7607683 * 2
def baseEnd_7607683 : Nat := 3906398046038863638975409

theorem tailTrace_7607683 : CollatzResearch.WordTrace tailWord_7607683 prefixEnd_7607683 3906398046038863638975409 := by
  unfold tailWord_7607683
  simp only [CollatzResearch.WordTrace]
  refine ⟨277474994497671254659843703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184983329665114169773229135 277474994497671254659843703)
  ·
    refine ⟨416212491746506881989765555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277474994497671254659843703 416212491746506881989765555)
    ·
      refine ⟨624318737619760322984648333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416212491746506881989765555 624318737619760322984648333)
      ·
        refine ⟨234119526607410121119243125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624318737619760322984648333 234119526607410121119243125)
        ·
          refine ⟨21948705619444698854929043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234119526607410121119243125 21948705619444698854929043)
          ·
            refine ⟨32923058429167048282393565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21948705619444698854929043 32923058429167048282393565)
            ·
              refine ⟨12346146910937643105897587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32923058429167048282393565 12346146910937643105897587)
              ·
                refine ⟨18519220366406464658846381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346146910937643105897587 18519220366406464658846381)
                ·
                  refine ⟨6944707637402424247067393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18519220366406464658846381 6944707637402424247067393)
                  ·
                    refine ⟨5208530728051818185300545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6944707637402424247067393 5208530728051818185300545)
                    ·
                      refine ⟨3906398046038863638975409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208530728051818185300545 3906398046038863638975409)
                      ·
                        rfl

theorem cell23_7607683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_7607683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607683 prefixEnd_7607683 := by exact prefixLift 7607683
  have htrace : WordTrace (prefixWord ++ tailWord_7607683) baseStart_7607683 baseEnd_7607683 := by
    simpa [prefixWord, tailWord_7607683, baseEnd_7607683] using wordTrace_append hprefix tailTrace_7607683
  have hstable : (prefixWord ++ tailWord_7607683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607683).length < 2 ^ (prefixWord ++ tailWord_7607683).sum := by decide
  have hdescent : baseEnd_7607683 < baseStart_7607683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607689 : List Nat := [1, 2, 1, 1, 7, 1, 2, 8]
def baseStart_7607689 : Nat := 118140960795 + 7607689 * 2 ^ 59
def prefixEnd_7607689 : Nat := 4983230072969 + 3 ^ 40 * 7607689 * 2
def baseEnd_7607689 : Nat := 144681523219362615388903

theorem tailTrace_7607689 : CollatzResearch.WordTrace tailWord_7607689 prefixEnd_7607689 144681523219362615388903 := by
  unfold tailWord_7607689
  simp only [CollatzResearch.WordTrace]
  refine ⟨277475213335649517684562121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184983475557099678456374747 277475213335649517684562121)
  ·
    refine ⟨208106410001737138263421591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277475213335649517684562121 208106410001737138263421591)
    ·
      refine ⟨312159615002605707395132387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208106410001737138263421591 312159615002605707395132387)
      ·
        refine ⟨468239422503908561092698581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312159615002605707395132387 468239422503908561092698581)
        ·
          refine ⟨10974361464935356900610123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 468239422503908561092698581 10974361464935356900610123)
          ·
            refine ⟨16461542197403035350915185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974361464935356900610123 16461542197403035350915185)
            ·
              refine ⟨12346156648052276513186389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16461542197403035350915185 12346156648052276513186389)
              ·
                refine ⟨144681523219362615388903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12346156648052276513186389 144681523219362615388903)
                ·
                  rfl

theorem cell23_7607689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 8].length) (baseStart_7607689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607689 prefixEnd_7607689 := by exact prefixLift 7607689
  have htrace : WordTrace (prefixWord ++ tailWord_7607689) baseStart_7607689 baseEnd_7607689 := by
    simpa [prefixWord, tailWord_7607689, baseEnd_7607689] using wordTrace_append hprefix tailTrace_7607689
  have hstable : (prefixWord ++ tailWord_7607689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607689).length < 2 ^ (prefixWord ++ tailWord_7607689).sum := by decide
  have hdescent : baseEnd_7607689 < baseStart_7607689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607692 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7607692 : Nat := 118140960795 + 7607692 * 2 ^ 59
def prefixEnd_7607692 : Nat := 4983230072969 + 3 ^ 40 * 7607692 * 2
def baseEnd_7607692 : Nat := 3906402667364754103762867

theorem tailTrace_7607692 : CollatzResearch.WordTrace tailWord_7607692 prefixEnd_7607692 3906402667364754103762867 := by
  unfold tailWord_7607692
  simp only [CollatzResearch.WordTrace]
  refine ⟨138737661377319324598460665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184983548503092432797947553 138737661377319324598460665)
  ·
    refine ⟨104053246032989493448845499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138737661377319324598460665 104053246032989493448845499)
    ·
      refine ⟨156079869049484240173268249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104053246032989493448845499 156079869049484240173268249)
      ·
        refine ⟨117059901787113180129951187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156079869049484240173268249 117059901787113180129951187)
        ·
          refine ⟨175589852680669770194926781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117059901787113180129951187 175589852680669770194926781)
          ·
            refine ⟨65846194755251163823097543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175589852680669770194926781 65846194755251163823097543)
            ·
              refine ⟨98769292132876745734646315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65846194755251163823097543 98769292132876745734646315)
              ·
                refine ⟨148153938199315118601969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98769292132876745734646315 148153938199315118601969473)
                ·
                  refine ⟨111115453649486338951477105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148153938199315118601969473 111115453649486338951477105)
                  ·
                    refine ⟨83336590237114754213607829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111115453649486338951477105 83336590237114754213607829)
                    ·
                      refine ⟨3906402667364754103762867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83336590237114754213607829 3906402667364754103762867)
                      ·
                        rfl

theorem cell23_7607692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7607692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607692 prefixEnd_7607692 := by exact prefixLift 7607692
  have htrace : WordTrace (prefixWord ++ tailWord_7607692) baseStart_7607692 baseEnd_7607692 := by
    simpa [prefixWord, tailWord_7607692, baseEnd_7607692] using wordTrace_append hprefix tailTrace_7607692
  have hstable : (prefixWord ++ tailWord_7607692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607692).length < 2 ^ (prefixWord ++ tailWord_7607692).sum := by decide
  have hdescent : baseEnd_7607692 < baseStart_7607692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607720 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7607720 : Nat := 118140960795 + 7607720 * 2 ^ 59
def prefixEnd_7607720 : Nat := 4983230072969 + 3 ^ 40 * 7607720 * 2
def baseEnd_7607720 : Nat := 3906417044823079994212739

theorem tailTrace_7607720 : CollatzResearch.WordTrace tailWord_7607720 prefixEnd_7607720 3906417044823079994212739 := by
  unfold tailWord_7607720
  simp only [CollatzResearch.WordTrace]
  refine ⟨138738171999268604989470307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184984229332358139985960409 138738171999268604989470307)
  ·
    refine ⟨208107257998902907484205461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138738171999268604989470307 208107257998902907484205461)
    ·
      refine ⟨9755027718698573788322131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208107257998902907484205461 9755027718698573788322131)
      ·
        refine ⟨14632541578047860682483197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9755027718698573788322131 14632541578047860682483197)
        ·
          refine ⟨5487203091767947755931199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14632541578047860682483197 5487203091767947755931199)
          ·
            refine ⟨8230804637651921633896799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487203091767947755931199 8230804637651921633896799)
            ·
              refine ⟨12346206956477882450845199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8230804637651921633896799 12346206956477882450845199)
              ·
                refine ⟨18519310434716823676267799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12346206956477882450845199 18519310434716823676267799)
                ·
                  refine ⟨27778965652075235514401699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18519310434716823676267799 27778965652075235514401699)
                  ·
                    refine ⟨41668448478112853271602549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27778965652075235514401699 41668448478112853271602549)
                    ·
                      refine ⟨3906417044823079994212739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41668448478112853271602549 3906417044823079994212739)
                      ·
                        rfl

theorem cell23_7607720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7607720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607720 prefixEnd_7607720 := by exact prefixLift 7607720
  have htrace : WordTrace (prefixWord ++ tailWord_7607720) baseStart_7607720 baseEnd_7607720 := by
    simpa [prefixWord, tailWord_7607720, baseEnd_7607720] using wordTrace_append hprefix tailTrace_7607720
  have hstable : (prefixWord ++ tailWord_7607720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607720).length < 2 ^ (prefixWord ++ tailWord_7607720).sum := by decide
  have hdescent : baseEnd_7607720 < baseStart_7607720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607733 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_7607733 : Nat := 118140960795 + 7607733 * 2 ^ 59
def prefixEnd_7607733 : Nat := 4983230072969 + 3 ^ 40 * 7607733 * 2
def baseEnd_7607733 : Nat := 3906423720071588443350179

theorem tailTrace_7607733 : CollatzResearch.WordTrace tailWord_7607733 prefixEnd_7607733 3906423720071588443350179 := by
  unfold tailWord_7607733
  simp only [CollatzResearch.WordTrace]
  refine ⟨277476818147490113199163853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184984545431660075466109235 277476818147490113199163853)
  ·
    refine ⟨104053806805308792449686445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277476818147490113199163853 104053806805308792449686445)
    ·
      refine ⟨39020177551990797168632417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104053806805308792449686445 39020177551990797168632417)
      ·
        refine ⟨29265133163993097876474313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39020177551990797168632417 29265133163993097876474313)
        ·
          refine ⟨21948849872994823407355735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29265133163993097876474313 21948849872994823407355735)
          ·
            refine ⟨32923274809492235111033603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21948849872994823407355735 32923274809492235111033603)
            ·
              refine ⟨49384912214238352666550405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32923274809492235111033603 49384912214238352666550405)
              ·
                refine ⟨9259671040169691124978201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49384912214238352666550405 9259671040169691124978201)
                ·
                  refine ⟨6944753280127268343733651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9259671040169691124978201 6944753280127268343733651)
                  ·
                    refine ⟨10417129920190902515600477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6944753280127268343733651 10417129920190902515600477)
                    ·
                      refine ⟨3906423720071588443350179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417129920190902515600477 3906423720071588443350179)
                      ·
                        rfl

theorem cell23_7607733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_7607733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607733 prefixEnd_7607733 := by exact prefixLift 7607733
  have htrace : WordTrace (prefixWord ++ tailWord_7607733) baseStart_7607733 baseEnd_7607733 := by
    simpa [prefixWord, tailWord_7607733, baseEnd_7607733] using wordTrace_append hprefix tailTrace_7607733
  have hstable : (prefixWord ++ tailWord_7607733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607733).length < 2 ^ (prefixWord ++ tailWord_7607733).sum := by decide
  have hdescent : baseEnd_7607733 < baseStart_7607733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607739 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 10, 2]
def baseStart_7607739 : Nat := 118140960795 + 7607739 * 2 ^ 59
def prefixEnd_7607739 : Nat := 4983230072969 + 3 ^ 40 * 7607739 * 2
def baseEnd_7607739 : Nat := 3906426800955515419875151

theorem tailTrace_7607739 : CollatzResearch.WordTrace tailWord_7607739 prefixEnd_7607739 3906426800955515419875151 := by
  unfold tailWord_7607739
  simp only [CollatzResearch.WordTrace]
  refine ⟨277477036985468376223882271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184984691323645584149254847 277477036985468376223882271)
  ·
    refine ⟨416215555478202564335823407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277477036985468376223882271 416215555478202564335823407)
    ·
      refine ⟨624323333217303846503735111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416215555478202564335823407 624323333217303846503735111)
      ·
        refine ⟨936484999825955769755602667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624323333217303846503735111 936484999825955769755602667)
        ·
          refine ⟨1404727499738933654633404001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936484999825955769755602667 1404727499738933654633404001)
          ·
            refine ⟨1053545624804200240975053001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404727499738933654633404001 1053545624804200240975053001)
            ·
              refine ⟨790159218603150180731289751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053545624804200240975053001 790159218603150180731289751)
              ·
                refine ⟨1185238827904725271096934627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790159218603150180731289751 1185238827904725271096934627)
                ·
                  refine ⟨1777858241857087906645401941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1185238827904725271096934627 1777858241857087906645401941)
                  ·
                    refine ⟨5208569067940687226500201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1777858241857087906645401941 5208569067940687226500201)
                    ·
                      refine ⟨3906426800955515419875151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208569067940687226500201 3906426800955515419875151)
                      ·
                        rfl

theorem cell23_7607739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10, 2].length) (baseStart_7607739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607739 prefixEnd_7607739 := by exact prefixLift 7607739
  have htrace : WordTrace (prefixWord ++ tailWord_7607739) baseStart_7607739 baseEnd_7607739 := by
    simpa [prefixWord, tailWord_7607739, baseEnd_7607739] using wordTrace_append hprefix tailTrace_7607739
  have hstable : (prefixWord ++ tailWord_7607739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607739).length < 2 ^ (prefixWord ++ tailWord_7607739).sum := by decide
  have hdescent : baseEnd_7607739 < baseStart_7607739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607773 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7607773 : Nat := 118140960795 + 7607773 * 2 ^ 59
def prefixEnd_7607773 : Nat := 4983230072969 + 3 ^ 40 * 7607773 * 2
def baseEnd_7607773 : Nat := 3906444259297768286849995

theorem tailTrace_7607773 : CollatzResearch.WordTrace tailWord_7607773 prefixEnd_7607773 3906444259297768286849995 := by
  unfold tailWord_7607773
  simp only [CollatzResearch.WordTrace]
  refine ⟨277478277067345200030619973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184985518044896800020413315 277478277067345200030619973)
  ·
    refine ⟨52027176950127225005741245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277478277067345200030619973 52027176950127225005741245)
    ·
      refine ⟨19510191356297709377152967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52027176950127225005741245 19510191356297709377152967)
      ·
        refine ⟨29265287034446564065729451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19510191356297709377152967 29265287034446564065729451)
        ·
          refine ⟨43897930551669846098594177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29265287034446564065729451 43897930551669846098594177)
          ·
            refine ⟨32923447913752384573945633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43897930551669846098594177 32923447913752384573945633)
            ·
              refine ⟨24692585935314288430459225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32923447913752384573945633 24692585935314288430459225)
              ·
                refine ⟨18519439451485716322844419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24692585935314288430459225 18519439451485716322844419)
                ·
                  refine ⟨27779159177228574484266629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18519439451485716322844419 27779159177228574484266629)
                  ·
                    refine ⟨5208592345730357715799993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27779159177228574484266629 5208592345730357715799993)
                    ·
                      refine ⟨3906444259297768286849995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208592345730357715799993 3906444259297768286849995)
                      ·
                        rfl

theorem cell23_7607773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7607773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607773 prefixEnd_7607773 := by exact prefixLift 7607773
  have htrace : WordTrace (prefixWord ++ tailWord_7607773) baseStart_7607773 baseEnd_7607773 := by
    simpa [prefixWord, tailWord_7607773, baseEnd_7607773] using wordTrace_append hprefix tailTrace_7607773
  have hstable : (prefixWord ++ tailWord_7607773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607773).length < 2 ^ (prefixWord ++ tailWord_7607773).sum := by decide
  have hdescent : baseEnd_7607773 < baseStart_7607773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607816 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_7607816 : Nat := 118140960795 + 7607816 * 2 ^ 59
def prefixEnd_7607816 : Nat := 4983230072969 + 3 ^ 40 * 7607816 * 2
def baseEnd_7607816 : Nat := 3906466338965911618612297

theorem tailTrace_7607816 : CollatzResearch.WordTrace tailWord_7607816 prefixEnd_7607816 3906466338965911618612297 := by
  unfold tailWord_7607816
  simp only [CollatzResearch.WordTrace]
  refine ⟨138739922703094709187217651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184986563604126278916290201 138739922703094709187217651)
  ·
    refine ⟨208109884054642063780826477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138739922703094709187217651 208109884054642063780826477)
    ·
      refine ⟨78041206520490773917809929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208109884054642063780826477 78041206520490773917809929)
      ·
        refine ⟨58530904890368080438357447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78041206520490773917809929 58530904890368080438357447)
        ·
          refine ⟨87796357335552120657536171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58530904890368080438357447 87796357335552120657536171)
          ·
            refine ⟨131694536003328180986304257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87796357335552120657536171 131694536003328180986304257)
            ·
              refine ⟨98770902002496135739728193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131694536003328180986304257 98770902002496135739728193)
              ·
                refine ⟨74078176501872101804796145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98770902002496135739728193 74078176501872101804796145)
                ·
                  refine ⟨55558632376404076353597109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74078176501872101804796145 55558632376404076353597109)
                  ·
                    refine ⟨5208621785287882158149729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55558632376404076353597109 5208621785287882158149729)
                    ·
                      refine ⟨3906466338965911618612297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208621785287882158149729 3906466338965911618612297)
                      ·
                        rfl

theorem cell23_7607816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_7607816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607816 prefixEnd_7607816 := by exact prefixLift 7607816
  have htrace : WordTrace (prefixWord ++ tailWord_7607816) baseStart_7607816 baseEnd_7607816 := by
    simpa [prefixWord, tailWord_7607816, baseEnd_7607816] using wordTrace_append hprefix tailTrace_7607816
  have hstable : (prefixWord ++ tailWord_7607816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607816).length < 2 ^ (prefixWord ++ tailWord_7607816).sum := by decide
  have hdescent : baseEnd_7607816 < baseStart_7607816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607849 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 3]
def baseStart_7607849 : Nat := 118140960795 + 7607849 * 2 ^ 59
def prefixEnd_7607849 : Nat := 4983230072969 + 3 ^ 40 * 7607849 * 2
def baseEnd_7607849 : Nat := 3906483283827509989499645

theorem tailTrace_7607849 : CollatzResearch.WordTrace tailWord_7607849 prefixEnd_7607849 3906483283827509989499645 := by
  unfold tailWord_7607849
  simp only [CollatzResearch.WordTrace]
  refine ⟨277481049015069865010386601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184987366010046576673591067 277481049015069865010386601)
  ·
    refine ⟨208110786761302398757789951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277481049015069865010386601 208110786761302398757789951)
    ·
      refine ⟨312166180141953598136684927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208110786761302398757789951 312166180141953598136684927)
      ·
        refine ⟨468249270212930397205027391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312166180141953598136684927 468249270212930397205027391)
        ·
          refine ⟨702373905319395595807541087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468249270212930397205027391 702373905319395595807541087)
          ·
            refine ⟨1053560857979093393711311631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702373905319395595807541087 1053560857979093393711311631)
            ·
              refine ⟨1580341286968640090566967447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053560857979093393711311631 1580341286968640090566967447)
              ·
                refine ⟨2370511930452960135850451171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580341286968640090566967447 2370511930452960135850451171)
                ·
                  refine ⟨3555767895679440203775676757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370511930452960135850451171 3555767895679440203775676757)
                  ·
                    refine ⟨10417288756873359971999053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 3555767895679440203775676757 10417288756873359971999053)
                    ·
                      refine ⟨3906483283827509989499645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417288756873359971999053 3906483283827509989499645)
                      ·
                        rfl

theorem cell23_7607849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 10, 3].length) (baseStart_7607849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607849 prefixEnd_7607849 := by exact prefixLift 7607849
  have htrace : WordTrace (prefixWord ++ tailWord_7607849) baseStart_7607849 baseEnd_7607849 := by
    simpa [prefixWord, tailWord_7607849, baseEnd_7607849] using wordTrace_append hprefix tailTrace_7607849
  have hstable : (prefixWord ++ tailWord_7607849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607849).length < 2 ^ (prefixWord ++ tailWord_7607849).sum := by decide
  have hdescent : baseEnd_7607849 < baseStart_7607849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607866 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_7607866 : Nat := 118140960795 + 7607866 * 2 ^ 59
def prefixEnd_7607866 : Nat := 4983230072969 + 3 ^ 40 * 7607866 * 2
def baseEnd_7607866 : Nat := 3906492012998636422987067

theorem tailTrace_7607866 : CollatzResearch.WordTrace tailWord_7607866 prefixEnd_7607866 3906492012998636422987067 := by
  unfold tailWord_7607866
  simp only [CollatzResearch.WordTrace]
  refine ⟨69370417264002069228438863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184987779370672184609170301 69370417264002069228438863)
  ·
    refine ⟨104055625896003103842658295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69370417264002069228438863 104055625896003103842658295)
    ·
      refine ⟨156083438844004655763987443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104055625896003103842658295 156083438844004655763987443)
      ·
        refine ⟨234125158266006983645981165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156083438844004655763987443 234125158266006983645981165)
        ·
          refine ⟨87796934349752618867242937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234125158266006983645981165 87796934349752618867242937)
          ·
            refine ⟨65847700762314464150432203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87796934349752618867242937 65847700762314464150432203)
            ·
              refine ⟨98771551143471696225648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65847700762314464150432203 98771551143471696225648305)
              ·
                refine ⟨74078663357603772169236229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98771551143471696225648305 74078663357603772169236229)
                ·
                  refine ⟨13889749379550707281731793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74078663357603772169236229 13889749379550707281731793)
                  ·
                    refine ⟨10417312034663030461298845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13889749379550707281731793 10417312034663030461298845)
                    ·
                      refine ⟨3906492012998636422987067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417312034663030461298845 3906492012998636422987067)
                      ·
                        rfl

theorem cell23_7607866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_7607866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607866 prefixEnd_7607866 := by exact prefixLift 7607866
  have htrace : WordTrace (prefixWord ++ tailWord_7607866) baseStart_7607866 baseEnd_7607866 := by
    simpa [prefixWord, tailWord_7607866, baseEnd_7607866] using wordTrace_append hprefix tailTrace_7607866
  have hstable : (prefixWord ++ tailWord_7607866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607866).length < 2 ^ (prefixWord ++ tailWord_7607866).sum := by decide
  have hdescent : baseEnd_7607866 < baseStart_7607866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607907 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 1, 4]
def baseStart_7607907 : Nat := 118140960795 + 7607907 * 2 ^ 59
def prefixEnd_7607907 : Nat := 4983230072969 + 3 ^ 40 * 7607907 * 2
def baseEnd_7607907 : Nat := 1302171021901823587524793

theorem tailTrace_7607907 : CollatzResearch.WordTrace tailWord_7607907 prefixEnd_7607907 1302171021901823587524793 := by
  unfold tailWord_7607907
  simp only [CollatzResearch.WordTrace]
  refine ⟨277483164448859740915997975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184988776299239827277331983 277483164448859740915997975)
  ·
    refine ⟨416224746673289611373996963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277483164448859740915997975 416224746673289611373996963)
    ·
      refine ⟨624337120009934417060995445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416224746673289611373996963 624337120009934417060995445)
      ·
        refine ⟨58531605000931351599468323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624337120009934417060995445 58531605000931351599468323)
        ·
          refine ⟨87797407501397027399202485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58531605000931351599468323 87797407501397027399202485)
          ·
            refine ⟨8231006953255971318675233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87797407501397027399202485 8231006953255971318675233)
            ·
              refine ⟨6173255214941978489006425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8231006953255971318675233 6173255214941978489006425)
              ·
                refine ⟨4629941411206483866754819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173255214941978489006425 4629941411206483866754819)
                ·
                  refine ⟨6944912116809725800132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629941411206483866754819 6944912116809725800132229)
                  ·
                    refine ⟨1302171021901823587524793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6944912116809725800132229 1302171021901823587524793)
                    ·
                      rfl

theorem cell23_7607907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 4].length) (baseStart_7607907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607907 prefixEnd_7607907 := by exact prefixLift 7607907
  have htrace : WordTrace (prefixWord ++ tailWord_7607907) baseStart_7607907 baseEnd_7607907 := by
    simpa [prefixWord, tailWord_7607907, baseEnd_7607907] using wordTrace_append hprefix tailTrace_7607907
  have hstable : (prefixWord ++ tailWord_7607907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607907).length < 2 ^ (prefixWord ++ tailWord_7607907).sum := by decide
  have hdescent : baseEnd_7607907 < baseStart_7607907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607936 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_7607936 : Nat := 118140960795 + 7607936 * 2 ^ 59
def prefixEnd_7607936 : Nat := 4983230072969 + 3 ^ 40 * 7607936 * 2
def baseEnd_7607936 : Nat := 3906527956644451149111745

theorem tailTrace_7607936 : CollatzResearch.WordTrace tailWord_7607936 prefixEnd_7607936 3906527956644451149111745 := by
  unfold tailWord_7607936
  simp only [CollatzResearch.WordTrace]
  refine ⟨138742111082877339434401831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184989481443836452579202441 138742111082877339434401831)
  ·
    refine ⟨208113166624316009151602747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138742111082877339434401831 208113166624316009151602747)
    ·
      refine ⟨312169749936474013727404121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208113166624316009151602747 312169749936474013727404121)
      ·
        refine ⟨234127312452355510295553091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312169749936474013727404121 234127312452355510295553091)
        ·
          refine ⟨351190968678533265443329637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234127312452355510295553091 351190968678533265443329637)
          ·
            refine ⟨65848306627224987270624307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351190968678533265443329637 65848306627224987270624307)
            ·
              refine ⟨98772459940837480905936461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65848306627224987270624307 98772459940837480905936461)
              ·
                refine ⟨37039672477814055339726173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98772459940837480905936461 37039672477814055339726173)
                ·
                  refine ⟨13889877179180270752397315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37039672477814055339726173 13889877179180270752397315)
                  ·
                    refine ⟨20834815768770406128595973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13889877179180270752397315 20834815768770406128595973)
                    ·
                      refine ⟨3906527956644451149111745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20834815768770406128595973 3906527956644451149111745)
                      ·
                        rfl

theorem cell23_7607936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_7607936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607936 prefixEnd_7607936 := by exact prefixLift 7607936
  have htrace : WordTrace (prefixWord ++ tailWord_7607936) baseStart_7607936 baseEnd_7607936 := by
    simpa [prefixWord, tailWord_7607936, baseEnd_7607936] using wordTrace_append hprefix tailTrace_7607936
  have hstable : (prefixWord ++ tailWord_7607936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607936).length < 2 ^ (prefixWord ++ tailWord_7607936).sum := by decide
  have hdescent : baseEnd_7607936 < baseStart_7607936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607940 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7607940 : Nat := 118140960795 + 7607940 * 2 ^ 59
def prefixEnd_7607940 : Nat := 4983230072969 + 3 ^ 40 * 7607940 * 2
def baseEnd_7607940 : Nat := 3906530010567069133461727

theorem tailTrace_7607940 : CollatzResearch.WordTrace tailWord_7607940 prefixEnd_7607940 3906530010567069133461727 := by
  unfold tailWord_7607940
  simp only [CollatzResearch.WordTrace]
  refine ⟨138742184028870093775974637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184989578705160125034632849 138742184028870093775974637)
  ·
    refine ⟨52028319010826285165990489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138742184028870093775974637 52028319010826285165990489)
    ·
      refine ⟨39021239258119713874492867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52028319010826285165990489 39021239258119713874492867)
      ·
        refine ⟨58531858887179570811739301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39021239258119713874492867 58531858887179570811739301)
        ·
          refine ⟨10974723541346169527201119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58531858887179570811739301 10974723541346169527201119)
          ·
            refine ⟨16462085312019254290801679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974723541346169527201119 16462085312019254290801679)
            ·
              refine ⟨24693127968028881436202519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16462085312019254290801679 24693127968028881436202519)
              ·
                refine ⟨37039691952043322154303779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24693127968028881436202519 37039691952043322154303779)
                ·
                  refine ⟨55559537928064983231455669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37039691952043322154303779 55559537928064983231455669)
                  ·
                    refine ⟨5208706680756092177948969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55559537928064983231455669 5208706680756092177948969)
                    ·
                      refine ⟨3906530010567069133461727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208706680756092177948969 3906530010567069133461727)
                      ·
                        rfl

theorem cell23_7607940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7607940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607940 prefixEnd_7607940 := by exact prefixLift 7607940
  have htrace : WordTrace (prefixWord ++ tailWord_7607940) baseStart_7607940 baseEnd_7607940 := by
    simpa [prefixWord, tailWord_7607940, baseEnd_7607940] using wordTrace_append hprefix tailTrace_7607940
  have hstable : (prefixWord ++ tailWord_7607940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607940).length < 2 ^ (prefixWord ++ tailWord_7607940).sum := by decide
  have hdescent : baseEnd_7607940 < baseStart_7607940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7607950 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_7607950 : Nat := 118140960795 + 7607950 * 2 ^ 59
def prefixEnd_7607950 : Nat := 4983230072969 + 3 ^ 40 * 7607950 * 2
def baseEnd_7607950 : Nat := 1302178381791204698112227

theorem tailTrace_7607950 : CollatzResearch.WordTrace tailWord_7607950 prefixEnd_7607950 1302178381791204698112227 := by
  unfold tailWord_7607950
  simp only [CollatzResearch.WordTrace]
  refine ⟨34685591598462994907476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184989821858469306173208869 34685591598462994907476663)
  ·
    refine ⟨52028387397694492361214995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34685591598462994907476663 52028387397694492361214995)
    ·
      refine ⟨78042581096541738541822493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52028387397694492361214995 78042581096541738541822493)
      ·
        refine ⟨29265967911203151953183435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78042581096541738541822493 29265967911203151953183435)
        ·
          refine ⟨43898951866804727929775153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29265967911203151953183435 43898951866804727929775153)
          ·
            refine ⟨32924213900103545947331365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43898951866804727929775153 32924213900103545947331365)
            ·
              refine ⟨6173290106269414865124631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32924213900103545947331365 6173290106269414865124631)
              ·
                refine ⟨9259935159404122297686947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6173290106269414865124631 9259935159404122297686947)
                ·
                  refine ⟨13889902739106183446530421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9259935159404122297686947 13889902739106183446530421)
                  ·
                    refine ⟨1302178381791204698112227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13889902739106183446530421 1302178381791204698112227)
                    ·
                      rfl

theorem cell23_7607950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_7607950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7607950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7607950 prefixEnd_7607950 := by exact prefixLift 7607950
  have htrace : WordTrace (prefixWord ++ tailWord_7607950) baseStart_7607950 baseEnd_7607950 := by
    simpa [prefixWord, tailWord_7607950, baseEnd_7607950] using wordTrace_append hprefix tailTrace_7607950
  have hstable : (prefixWord ++ tailWord_7607950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7607950).length < 2 ^ (prefixWord ++ tailWord_7607950).sum := by decide
  have hdescent : baseEnd_7607950 < baseStart_7607950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7607950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608036 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_7608036 : Nat := 118140960795 + 7608036 * 2 ^ 59
def prefixEnd_7608036 : Nat := 4983230072969 + 3 ^ 40 * 7608036 * 2
def baseEnd_7608036 : Nat := 1302193101569966919287095

theorem tailTrace_7608036 : CollatzResearch.WordTrace tailWord_7608036 prefixEnd_7608036 1302193101569966919287095 := by
  unfold tailWord_7608036
  simp only [CollatzResearch.WordTrace]
  refine ⟨138743934732696197973721981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184991912976928263964962641 138743934732696197973721981)
  ·
    refine ⟨52028975524761074240145743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138743934732696197973721981 52028975524761074240145743)
    ·
      refine ⟨78043463287141611360218615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52028975524761074240145743 78043463287141611360218615)
      ·
        refine ⟨117065194930712417040327923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78043463287141611360218615 117065194930712417040327923)
        ·
          refine ⟨175597792396068625560491885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117065194930712417040327923 175597792396068625560491885)
          ·
            refine ⟨65849172148525734585184457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175597792396068625560491885 65849172148525734585184457)
            ·
              refine ⟨49386879111394300938888343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65849172148525734585184457 49386879111394300938888343)
              ·
                refine ⟨74080318667091451408332515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49386879111394300938888343 74080318667091451408332515)
                ·
                  refine ⟨111120478000637177112498773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74080318667091451408332515 111120478000637177112498773)
                  ·
                    refine ⟨1302193101569966919287095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111120478000637177112498773 1302193101569966919287095)
                    ·
                      rfl

theorem cell23_7608036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_7608036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608036 prefixEnd_7608036 := by exact prefixLift 7608036
  have htrace : WordTrace (prefixWord ++ tailWord_7608036) baseStart_7608036 baseEnd_7608036 := by
    simpa [prefixWord, tailWord_7608036, baseEnd_7608036] using wordTrace_append hprefix tailTrace_7608036
  have hstable : (prefixWord ++ tailWord_7608036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608036).length < 2 ^ (prefixWord ++ tailWord_7608036).sum := by decide
  have hdescent : baseEnd_7608036 < baseStart_7608036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608056 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_7608056 : Nat := 118140960795 + 7608056 * 2 ^ 59
def prefixEnd_7608056 : Nat := 4983230072969 + 3 ^ 40 * 7608056 * 2
def baseEnd_7608056 : Nat := 3906589574322990679611193

theorem tailTrace_7608056 : CollatzResearch.WordTrace tailWord_7608056 prefixEnd_7608056 3906589574322990679611193 := by
  unfold tailWord_7608056
  simp only [CollatzResearch.WordTrace]
  refine ⟨138744299462659969681586011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184992399283546626242114681 138744299462659969681586011)
  ·
    refine ⟨208116449193989954522379017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138744299462659969681586011 208116449193989954522379017)
    ·
      refine ⟨156087336895492465891784263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208116449193989954522379017 156087336895492465891784263)
      ·
        refine ⟨234131005343238698837676395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156087336895492465891784263 234131005343238698837676395)
        ·
          refine ⟨351196508014858048256514593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234131005343238698837676395 351196508014858048256514593)
          ·
            refine ⟨263397381011143536192385945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351196508014858048256514593 263397381011143536192385945)
            ·
              refine ⟨197548035758357652144289459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263397381011143536192385945 197548035758357652144289459)
              ·
                refine ⟨296322053637536478216434189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197548035758357652144289459 296322053637536478216434189)
                ·
                  refine ⟨111120770114076179331162821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296322053637536478216434189 111120770114076179331162821)
                  ·
                    refine ⟨20835144396389283624593029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111120770114076179331162821 20835144396389283624593029)
                    ·
                      refine ⟨3906589574322990679611193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20835144396389283624593029 3906589574322990679611193)
                      ·
                        rfl

theorem cell23_7608056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_7608056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608056 prefixEnd_7608056 := by exact prefixLift 7608056
  have htrace : WordTrace (prefixWord ++ tailWord_7608056) baseStart_7608056 baseEnd_7608056 := by
    simpa [prefixWord, tailWord_7608056, baseEnd_7608056] using wordTrace_append hprefix tailTrace_7608056
  have hstable : (prefixWord ++ tailWord_7608056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608056).length < 2 ^ (prefixWord ++ tailWord_7608056).sum := by decide
  have hdescent : baseEnd_7608056 < baseStart_7608056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608060 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_7608060 : Nat := 118140960795 + 7608060 * 2 ^ 59
def prefixEnd_7608060 : Nat := 4983230072969 + 3 ^ 40 * 7608060 * 2
def baseEnd_7608060 : Nat := 3906591628245608663961175

theorem tailTrace_7608060 : CollatzResearch.WordTrace tailWord_7608060 prefixEnd_7608060 3906591628245608663961175 := by
  unfold tailWord_7608060
  simp only [CollatzResearch.WordTrace]
  refine ⟨138744372408652724023158817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184992496544870298697545089 138744372408652724023158817)
  ·
    refine ⟨104058279306489543017369113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138744372408652724023158817 104058279306489543017369113)
    ·
      refine ⟨78043709479867157263026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104058279306489543017369113 78043709479867157263026835)
      ·
        refine ⟨117065564219800735894540253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78043709479867157263026835 117065564219800735894540253)
        ·
          refine ⟨43899586582425275960452595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117065564219800735894540253 43899586582425275960452595)
          ·
            refine ⟨65849379873637913940678893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43899586582425275960452595 65849379873637913940678893)
            ·
              refine ⟨24693517452614217727754585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65849379873637913940678893 24693517452614217727754585)
              ·
                refine ⟨18520138089460663295815939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24693517452614217727754585 18520138089460663295815939)
                ·
                  refine ⟨27780207134190994943723909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18520138089460663295815939 27780207134190994943723909)
                  ·
                    refine ⟨5208788837660811551948233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27780207134190994943723909 5208788837660811551948233)
                    ·
                      refine ⟨3906591628245608663961175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208788837660811551948233 3906591628245608663961175)
                      ·
                        rfl

theorem cell23_7608060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_7608060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608060 prefixEnd_7608060 := by exact prefixLift 7608060
  have htrace : WordTrace (prefixWord ++ tailWord_7608060) baseStart_7608060 baseEnd_7608060 := by
    simpa [prefixWord, tailWord_7608060, baseEnd_7608060] using wordTrace_append hprefix tailTrace_7608060
  have hstable : (prefixWord ++ tailWord_7608060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608060).length < 2 ^ (prefixWord ++ tailWord_7608060).sum := by decide
  have hdescent : baseEnd_7608060 < baseStart_7608060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608076 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7608076 : Nat := 118140960795 + 7608076 * 2 ^ 59
def prefixEnd_7608076 : Nat := 4983230072969 + 3 ^ 40 * 7608076 * 2
def baseEnd_7608076 : Nat := 3906599843936080601361101

theorem tailTrace_7608076 : CollatzResearch.WordTrace tailWord_7608076 prefixEnd_7608076 3906599843936080601361101 := by
  unfold tailWord_7608076
  simp only [CollatzResearch.WordTrace]
  refine ⟨138744664192623741389450041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184992885590164988519266721 138744664192623741389450041)
  ·
    refine ⟨104058498144467806042087531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138744664192623741389450041 104058498144467806042087531)
    ·
      refine ⟨156087747216701709063131297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104058498144467806042087531 156087747216701709063131297)
      ·
        refine ⟨117065810412526281797348473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156087747216701709063131297 117065810412526281797348473)
        ·
          refine ⟨87799357809394711348011355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117065810412526281797348473 87799357809394711348011355)
          ·
            refine ⟨131699036714092067022017033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87799357809394711348011355 131699036714092067022017033)
            ·
              refine ⟨98774277535569050266512775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131699036714092067022017033 98774277535569050266512775)
              ·
                refine ⟨148161416303353575399769163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98774277535569050266512775 148161416303353575399769163)
                ·
                  refine ⟨222242124455030363099653745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148161416303353575399769163 222242124455030363099653745)
                  ·
                    refine ⟨166681593341272772324740309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222242124455030363099653745 166681593341272772324740309)
                    ·
                      refine ⟨3906599843936080601361101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166681593341272772324740309 3906599843936080601361101)
                      ·
                        rfl

theorem cell23_7608076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7608076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608076 prefixEnd_7608076 := by exact prefixLift 7608076
  have htrace : WordTrace (prefixWord ++ tailWord_7608076) baseStart_7608076 baseEnd_7608076 := by
    simpa [prefixWord, tailWord_7608076, baseEnd_7608076] using wordTrace_append hprefix tailTrace_7608076
  have hstable : (prefixWord ++ tailWord_7608076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608076).length < 2 ^ (prefixWord ++ tailWord_7608076).sum := by decide
  have hdescent : baseEnd_7608076 < baseStart_7608076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608113 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_7608113 : Nat := 118140960795 + 7608113 * 2 ^ 59
def prefixEnd_7608113 : Nat := 4983230072969 + 3 ^ 40 * 7608113 * 2
def baseEnd_7608113 : Nat := 1302206280906765652199477

theorem tailTrace_7608113 : CollatzResearch.WordTrace tailWord_7608113 prefixEnd_7608113 1302206280906765652199477 := by
  unfold tailWord_7608113
  simp only [CollatzResearch.WordTrace]
  refine ⟨277490677886113438097996993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184993785257408958731997995 277490677886113438097996993)
  ·
    refine ⟨208118008414585078573497745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277490677886113438097996993 208118008414585078573497745)
    ·
      refine ⟨156088506310938808930123309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208118008414585078573497745 156088506310938808930123309)
      ·
        refine ⟨58533189866602053348796241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156088506310938808930123309 58533189866602053348796241)
        ·
          refine ⟨43899892399951540011597181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58533189866602053348796241 43899892399951540011597181)
          ·
            refine ⟨16462459649981827504348943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43899892399951540011597181 16462459649981827504348943)
            ·
              refine ⟨24693689474972741256523415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16462459649981827504348943 24693689474972741256523415)
              ·
                refine ⟨37040534212459111884785123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24693689474972741256523415 37040534212459111884785123)
                ·
                  refine ⟨55560801318688667827177685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37040534212459111884785123 55560801318688667827177685)
                  ·
                    refine ⟨1302206280906765652199477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55560801318688667827177685 1302206280906765652199477)
                    ·
                      rfl

theorem cell23_7608113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_7608113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608113 prefixEnd_7608113 := by exact prefixLift 7608113
  have htrace : WordTrace (prefixWord ++ tailWord_7608113) baseStart_7608113 baseEnd_7608113 := by
    simpa [prefixWord, tailWord_7608113, baseEnd_7608113] using wordTrace_append hprefix tailTrace_7608113
  have hstable : (prefixWord ++ tailWord_7608113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608113).length < 2 ^ (prefixWord ++ tailWord_7608113).sum := by decide
  have hdescent : baseEnd_7608113 < baseStart_7608113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608117 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 5]
def baseStart_7608117 : Nat := 118140960795 + 7608117 * 2 ^ 59
def prefixEnd_7608117 : Nat := 4983230072969 + 3 ^ 40 * 7608117 * 2
def baseEnd_7608117 : Nat := 434068988515879437883157

theorem tailTrace_7608117 : CollatzResearch.WordTrace tailWord_7608117 prefixEnd_7608117 434068988515879437883157 := by
  unfold tailWord_7608117
  simp only [CollatzResearch.WordTrace]
  refine ⟨277490823778098946781142605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184993882518732631187428403 277490823778098946781142605)
  ·
    refine ⟨104059058916787105042928477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277490823778098946781142605 104059058916787105042928477)
    ·
      refine ⟨39022147093795164391098179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104059058916787105042928477 39022147093795164391098179)
      ·
        refine ⟨58533220640692746586647269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39022147093795164391098179 58533220640692746586647269)
        ·
          refine ⟨10974978870129889984996363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58533220640692746586647269 10974978870129889984996363)
          ·
            refine ⟨16462468305194834977494545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10974978870129889984996363 16462468305194834977494545)
            ·
              refine ⟨12346851228896126233120909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16462468305194834977494545 12346851228896126233120909)
              ·
                refine ⟨4630069210836047337420341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12346851228896126233120909 4630069210836047337420341)
                ·
                  refine ⟨434068988515879437883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630069210836047337420341 434068988515879437883157)
                  ·
                    rfl

theorem cell23_7608117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 5].length) (baseStart_7608117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608117 prefixEnd_7608117 := by exact prefixLift 7608117
  have htrace : WordTrace (prefixWord ++ tailWord_7608117) baseStart_7608117 baseEnd_7608117 := by
    simpa [prefixWord, tailWord_7608117, baseEnd_7608117] using wordTrace_append hprefix tailTrace_7608117
  have hstable : (prefixWord ++ tailWord_7608117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608117).length < 2 ^ (prefixWord ++ tailWord_7608117).sum := by decide
  have hdescent : baseEnd_7608117 < baseStart_7608117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608133 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_7608133 : Nat := 118140960795 + 7608133 * 2 ^ 59
def prefixEnd_7608133 : Nat := 4983230072969 + 3 ^ 40 * 7608133 * 2
def baseEnd_7608133 : Nat := 3906629112333386878348339

theorem tailTrace_7608133 : CollatzResearch.WordTrace tailWord_7608133 prefixEnd_7608133 3906629112333386878348339 := by
  unfold tailWord_7608133
  simp only [CollatzResearch.WordTrace]
  refine ⟨277491407346040981513725053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184994271564027321009150035 277491407346040981513725053)
  ·
    refine ⟨104059277754765368067646895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277491407346040981513725053 104059277754765368067646895)
    ·
      refine ⟨156088916632148052101470343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104059277754765368067646895 156088916632148052101470343)
      ·
        refine ⟨234133374948222078152205515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156088916632148052101470343 234133374948222078152205515)
        ·
          refine ⟨351200062422333117228308273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234133374948222078152205515 351200062422333117228308273)
          ·
            refine ⟨263400046816749837921231205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351200062422333117228308273 263400046816749837921231205)
            ·
              refine ⟨49387508778140594610230851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263400046816749837921231205 49387508778140594610230851)
              ·
                refine ⟨74081263167210891915346277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49387508778140594610230851 74081263167210891915346277)
                ·
                  refine ⟨13890236843852042234127427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74081263167210891915346277 13890236843852042234127427)
                  ·
                    refine ⟨20835355265778063351191141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13890236843852042234127427 20835355265778063351191141)
                    ·
                      refine ⟨3906629112333386878348339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20835355265778063351191141 3906629112333386878348339)
                      ·
                        rfl

theorem cell23_7608133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_7608133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608133 prefixEnd_7608133 := by exact prefixLift 7608133
  have htrace : WordTrace (prefixWord ++ tailWord_7608133) baseStart_7608133 baseEnd_7608133 := by
    simpa [prefixWord, tailWord_7608133, baseEnd_7608133] using wordTrace_append hprefix tailTrace_7608133
  have hstable : (prefixWord ++ tailWord_7608133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608133).length < 2 ^ (prefixWord ++ tailWord_7608133).sum := by decide
  have hdescent : baseEnd_7608133 < baseStart_7608133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608134 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_7608134 : Nat := 118140960795 + 7608134 * 2 ^ 59
def prefixEnd_7608134 : Nat := 4983230072969 + 3 ^ 40 * 7608134 * 2
def baseEnd_7608134 : Nat := 434069958423782374937315

theorem tailTrace_7608134 : CollatzResearch.WordTrace tailWord_7608134 prefixEnd_7608134 434069958423782374937315 := by
  unfold tailWord_7608134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671607619344917458890983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184994295879358239123007637 8671607619344917458890983)
  ·
    refine ⟨13007411429017376188336475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671607619344917458890983 13007411429017376188336475)
    ·
      refine ⟨19511117143526064282504713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13007411429017376188336475 19511117143526064282504713)
      ·
        refine ⟨14633337857644548211878535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19511117143526064282504713 14633337857644548211878535)
        ·
          refine ⟨21950006786466822317817803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14633337857644548211878535 21950006786466822317817803)
          ·
            refine ⟨32925010179700233476726705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21950006786466822317817803 32925010179700233476726705)
            ·
              refine ⟨24693757634775175107545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32925010179700233476726705 24693757634775175107545029)
              ·
                refine ⟨4630079556520345332664693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24693757634775175107545029 4630079556520345332664693)
                ·
                  refine ⟨434069958423782374937315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630079556520345332664693 434069958423782374937315)
                  ·
                    rfl

theorem cell23_7608134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_7608134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608134 prefixEnd_7608134 := by exact prefixLift 7608134
  have htrace : WordTrace (prefixWord ++ tailWord_7608134) baseStart_7608134 baseEnd_7608134 := by
    simpa [prefixWord, tailWord_7608134, baseEnd_7608134] using wordTrace_append hprefix tailTrace_7608134
  have hstable : (prefixWord ++ tailWord_7608134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608134).length < 2 ^ (prefixWord ++ tailWord_7608134).sum := by decide
  have hdescent : baseEnd_7608134 < baseStart_7608134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608153 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 3]
def baseStart_7608153 : Nat := 118140960795 + 7608153 * 2 ^ 59
def prefixEnd_7608153 : Nat := 4983230072969 + 3 ^ 40 * 7608153 * 2
def baseEnd_7608153 : Nat := 3906639381946476800098247

theorem tailTrace_7608153 : CollatzResearch.WordTrace tailWord_7608153 prefixEnd_7608153 3906639381946476800098247 := by
  unfold tailWord_7608153
  simp only [CollatzResearch.WordTrace]
  refine ⟨277492136805968524929453113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184994757870645683286302075 277492136805968524929453113)
  ·
    refine ⟨208119102604476393697089835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277492136805968524929453113 208119102604476393697089835)
    ·
      refine ⟨312178653906714590545634753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208119102604476393697089835 312178653906714590545634753)
      ·
        refine ⟨234133990430035942909226065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312178653906714590545634753 234133990430035942909226065)
        ·
          refine ⟨175600492822526957181919549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234133990430035942909226065 175600492822526957181919549)
          ·
            refine ⟨65850184808447608943219831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175600492822526957181919549 65850184808447608943219831)
            ·
              refine ⟨98775277212671413414829747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65850184808447608943219831 98775277212671413414829747)
              ·
                refine ⟨148162915819007120122244621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98775277212671413414829747 148162915819007120122244621)
                ·
                  refine ⟨55561093432127670045841733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148162915819007120122244621 55561093432127670045841733)
                  ·
                    refine ⟨10417705018523938133595325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55561093432127670045841733 10417705018523938133595325)
                    ·
                      refine ⟨3906639381946476800098247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417705018523938133595325 3906639381946476800098247)
                      ·
                        rfl

theorem cell23_7608153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_7608153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608153 prefixEnd_7608153 := by exact prefixLift 7608153
  have htrace : WordTrace (prefixWord ++ tailWord_7608153) baseStart_7608153 baseEnd_7608153 := by
    simpa [prefixWord, tailWord_7608153, baseEnd_7608153] using wordTrace_append hprefix tailTrace_7608153
  have hstable : (prefixWord ++ tailWord_7608153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608153).length < 2 ^ (prefixWord ++ tailWord_7608153).sum := by decide
  have hdescent : baseEnd_7608153 < baseStart_7608153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608160 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_7608160 : Nat := 118140960795 + 7608160 * 2 ^ 59
def prefixEnd_7608160 : Nat := 4983230072969 + 3 ^ 40 * 7608160 * 2
def baseEnd_7608160 : Nat := 1302214325437019424236905

theorem tailTrace_7608160 : CollatzResearch.WordTrace tailWord_7608160 prefixEnd_7608160 1302214325437019424236905 := by
  unfold tailWord_7608160
  simp only [CollatzResearch.WordTrace]
  refine ⟨138746196058471582562478967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184994928077962110083305289 138746196058471582562478967)
  ·
    refine ⟨208119294087707373843718451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138746196058471582562478967 208119294087707373843718451)
    ·
      refine ⟨312178941131561060765577677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208119294087707373843718451 312178941131561060765577677)
      ·
        refine ⟨117067102924335397787091629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312178941131561060765577677 117067102924335397787091629)
        ·
          refine ⟨43900163596625774170159361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117067102924335397787091629 43900163596625774170159361)
          ·
            refine ⟨32925122697469330627619521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43900163596625774170159361 32925122697469330627619521)
            ·
              refine ⟨24693842023101997970714641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32925122697469330627619521 24693842023101997970714641)
              ·
                refine ⟨18520381517326498478035981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24693842023101997970714641 18520381517326498478035981)
                ·
                  refine ⟨6945143068997436929263493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18520381517326498478035981 6945143068997436929263493)
                  ·
                    refine ⟨1302214325437019424236905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945143068997436929263493 1302214325437019424236905)
                    ·
                      rfl

theorem cell23_7608160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_7608160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608160 prefixEnd_7608160 := by exact prefixLift 7608160
  have htrace : WordTrace (prefixWord ++ tailWord_7608160) baseStart_7608160 baseEnd_7608160 := by
    simpa [prefixWord, tailWord_7608160, baseEnd_7608160] using wordTrace_append hprefix tailTrace_7608160
  have hstable : (prefixWord ++ tailWord_7608160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608160).length < 2 ^ (prefixWord ++ tailWord_7608160).sum := by decide
  have hdescent : baseEnd_7608160 < baseStart_7608160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608173 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 8]
def baseStart_7608173 : Nat := 118140960795 + 7608173 * 2 ^ 59
def prefixEnd_7608173 : Nat := 4983230072969 + 3 ^ 40 * 7608173 * 2
def baseEnd_7608173 : Nat := 434072183506618524649795

theorem tailTrace_7608173 : CollatzResearch.WordTrace tailWord_7608173 prefixEnd_7608173 434072183506618524649795 := by
  unfold tailWord_7608173
  simp only [CollatzResearch.WordTrace]
  refine ⟨277492866265896068345181173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184995244177264045563454115 277492866265896068345181173)
  ·
    refine ⟨26014956212427756407360735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277492866265896068345181173 26014956212427756407360735)
    ·
      refine ⟨39022434318641634611041103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26014956212427756407360735 39022434318641634611041103)
      ·
        refine ⟨58533651477962451916561655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39022434318641634611041103 58533651477962451916561655)
        ·
          refine ⟨87800477216943677874842483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58533651477962451916561655 87800477216943677874842483)
          ·
            refine ⟨131700715825415516812263725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87800477216943677874842483 131700715825415516812263725)
            ·
              refine ⟨49387768434530818804598897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131700715825415516812263725 49387768434530818804598897)
              ·
                refine ⟨37040826325898114103449173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49387768434530818804598897 37040826325898114103449173)
                ·
                  refine ⟨434072183506618524649795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37040826325898114103449173 434072183506618524649795)
                  ·
                    rfl

theorem cell23_7608173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_7608173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608173 prefixEnd_7608173 := by exact prefixLift 7608173
  have htrace : WordTrace (prefixWord ++ tailWord_7608173) baseStart_7608173 baseEnd_7608173 := by
    simpa [prefixWord, tailWord_7608173, baseEnd_7608173] using wordTrace_append hprefix tailTrace_7608173
  have hstable : (prefixWord ++ tailWord_7608173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608173).length < 2 ^ (prefixWord ++ tailWord_7608173).sum := by decide
  have hdescent : baseEnd_7608173 < baseStart_7608173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608203 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 3, 5]
def baseStart_7608203 : Nat := 118140960795 + 7608203 * 2 ^ 59
def prefixEnd_7608203 : Nat := 4983230072969 + 3 ^ 40 * 7608203 * 2
def baseEnd_7608203 : Nat := 1302221685326400534824339

theorem tailTrace_7608203 : CollatzResearch.WordTrace tailWord_7608203 prefixEnd_7608203 1302221685326400534824339 := by
  unfold tailWord_7608203
  simp only [CollatzResearch.WordTrace]
  refine ⟨277493960455787383468773263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184995973637191588979182175 277493960455787383468773263)
  ·
    refine ⟨416240940683681075203159895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277493960455787383468773263 416240940683681075203159895)
    ·
      refine ⟨624361411025521612804739843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416240940683681075203159895 624361411025521612804739843)
      ·
        refine ⟨936542116538282419207109765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624361411025521612804739843 936542116538282419207109765)
        ·
          refine ⟨175601646850927953601333081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 936542116538282419207109765 175601646850927953601333081)
          ·
            refine ⟨131701235138195965200999811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175601646850927953601333081 131701235138195965200999811)
            ·
              refine ⟨197551852707293947801499717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131701235138195965200999811 197551852707293947801499717)
              ·
                refine ⟨37040972382617615212781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197551852707293947801499717 37040972382617615212781197)
                ·
                  refine ⟨13890364643481605704792949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37040972382617615212781197 13890364643481605704792949)
                  ·
                    refine ⟨1302221685326400534824339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13890364643481605704792949 1302221685326400534824339)
                    ·
                      rfl

theorem cell23_7608203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 5].length) (baseStart_7608203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608203 prefixEnd_7608203 := by exact prefixLift 7608203
  have htrace : WordTrace (prefixWord ++ tailWord_7608203) baseStart_7608203 baseEnd_7608203 := by
    simpa [prefixWord, tailWord_7608203, baseEnd_7608203] using wordTrace_append hprefix tailTrace_7608203
  have hstable : (prefixWord ++ tailWord_7608203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608203).length < 2 ^ (prefixWord ++ tailWord_7608203).sum := by decide
  have hdescent : baseEnd_7608203 < baseStart_7608203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608277 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7608277 : Nat := 118140960795 + 7608277 * 2 ^ 59
def prefixEnd_7608277 : Nat := 4983230072969 + 3 ^ 40 * 7608277 * 2
def baseEnd_7608277 : Nat := 3906703053547634314947677

theorem tailTrace_7608277 : CollatzResearch.WordTrace tailWord_7608277 prefixEnd_7608277 3906703053547634314947677 := by
  unfold tailWord_7608277
  simp only [CollatzResearch.WordTrace]
  refine ⟨277496659457519294106967085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184997772971679529404644723 277496659457519294106967085)
  ·
    refine ⟨104061247296569735290112657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277496659457519294106967085 104061247296569735290112657)
    ·
      refine ⟨78045935472427301467584493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104061247296569735290112657 78045935472427301467584493)
      ·
        refine ⟨29267225802160238050344185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78045935472427301467584493 29267225802160238050344185)
        ·
          refine ⟨21950419351620178537758139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29267225802160238050344185 21950419351620178537758139)
          ·
            refine ⟨32925629027430267806637209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21950419351620178537758139 32925629027430267806637209)
            ·
              refine ⟨24694221770572700854977907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32925629027430267806637209 24694221770572700854977907)
              ·
                refine ⟨37041332655859051282466861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24694221770572700854977907 37041332655859051282466861)
                ·
                  refine ⟨13890499745947144230925073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37041332655859051282466861 13890499745947144230925073)
                  ·
                    refine ⟨10417874809460358173193805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13890499745947144230925073 10417874809460358173193805)
                    ·
                      refine ⟨3906703053547634314947677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10417874809460358173193805 3906703053547634314947677)
                      ·
                        rfl

theorem cell23_7608277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7608277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608277 prefixEnd_7608277 := by exact prefixLift 7608277
  have htrace : WordTrace (prefixWord ++ tailWord_7608277) baseStart_7608277 baseEnd_7608277 := by
    simpa [prefixWord, tailWord_7608277, baseEnd_7608277] using wordTrace_append hprefix tailTrace_7608277
  have hstable : (prefixWord ++ tailWord_7608277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608277).length < 2 ^ (prefixWord ++ tailWord_7608277).sum := by decide
  have hdescent : baseEnd_7608277 < baseStart_7608277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608278 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7608278 : Nat := 118140960795 + 7608278 * 2 ^ 59
def prefixEnd_7608278 : Nat := 4983230072969 + 3 ^ 40 * 7608278 * 2
def baseEnd_7608278 : Nat := 3906703567028288811035173

theorem tailTrace_7608278 : CollatzResearch.WordTrace tailWord_7608278 prefixEnd_7608278 3906703567028288811035173 := by
  unfold tailWord_7608278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17343543495657229454859593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184997797287010447518502325 17343543495657229454859593)
  ·
    refine ⟨13007657621742922091144695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17343543495657229454859593 13007657621742922091144695)
    ·
      refine ⟨19511486432614383136717043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13007657621742922091144695 19511486432614383136717043)
      ·
        refine ⟨29267229648921574705075565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19511486432614383136717043 29267229648921574705075565)
        ·
          refine ⟨10975211118345590514403337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29267229648921574705075565 10975211118345590514403337)
          ·
            refine ⟨8231408338759192885802503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10975211118345590514403337 8231408338759192885802503)
            ·
              refine ⟨12347112508138789328703755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8231408338759192885802503 12347112508138789328703755)
              ·
                refine ⟨18520668762208183993055633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12347112508138789328703755 18520668762208183993055633)
                ·
                  refine ⟨13890501571656137994791725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18520668762208183993055633 13890501571656137994791725)
                  ·
                    refine ⟨5208938089371051748046897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13890501571656137994791725 5208938089371051748046897)
                    ·
                      refine ⟨3906703567028288811035173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208938089371051748046897 3906703567028288811035173)
                      ·
                        rfl

theorem cell23_7608278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7608278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608278 prefixEnd_7608278 := by exact prefixLift 7608278
  have htrace : WordTrace (prefixWord ++ tailWord_7608278) baseStart_7608278 baseEnd_7608278 := by
    simpa [prefixWord, tailWord_7608278, baseEnd_7608278] using wordTrace_append hprefix tailTrace_7608278
  have hstable : (prefixWord ++ tailWord_7608278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608278).length < 2 ^ (prefixWord ++ tailWord_7608278).sum := by decide
  have hdescent : baseEnd_7608278 < baseStart_7608278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608280 : List Nat := [2, 1, 2, 2, 2, 2, 5, 7]
def baseStart_7608280 : Nat := 118140960795 + 7608280 * 2 ^ 59
def prefixEnd_7608280 : Nat := 4983230072969 + 3 ^ 40 * 7608280 * 2
def baseEnd_7608280 : Nat := 144692762740355474192969

theorem tailTrace_7608280 : CollatzResearch.WordTrace tailWord_7608280 prefixEnd_7608280 144692762740355474192969 := by
  unfold tailWord_7608280
  simp only [CollatzResearch.WordTrace]
  refine ⟨138748384438254212809663147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184997845917672283746217529 138748384438254212809663147)
  ·
    refine ⟨208122576657381319214494721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138748384438254212809663147 208122576657381319214494721)
    ·
      refine ⟨156091932493035989410871041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208122576657381319214494721 156091932493035989410871041)
      ·
        refine ⟨117068949369776992058153281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156091932493035989410871041 117068949369776992058153281)
        ·
          refine ⟨87801712027332744043614961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117068949369776992058153281 87801712027332744043614961)
          ·
            refine ⟨65851284020499558032711221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87801712027332744043614961 65851284020499558032711221)
            ·
              refine ⟨6173557876921833565566677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65851284020499558032711221 6173557876921833565566677)
              ·
                refine ⟨144692762740355474192969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6173557876921833565566677 144692762740355474192969)
                ·
                  rfl

theorem cell23_7608280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 7].length) (baseStart_7608280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608280 prefixEnd_7608280 := by exact prefixLift 7608280
  have htrace : WordTrace (prefixWord ++ tailWord_7608280) baseStart_7608280 baseEnd_7608280 := by
    simpa [prefixWord, tailWord_7608280, baseEnd_7608280] using wordTrace_append hprefix tailTrace_7608280
  have hstable : (prefixWord ++ tailWord_7608280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608280).length < 2 ^ (prefixWord ++ tailWord_7608280).sum := by decide
  have hdescent : baseEnd_7608280 < baseStart_7608280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608291 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7608291 : Nat := 118140960795 + 7608291 * 2 ^ 59
def prefixEnd_7608291 : Nat := 4983230072969 + 3 ^ 40 * 7608291 * 2
def baseEnd_7608291 : Nat := 3906710242276797260172613

theorem tailTrace_7608291 : CollatzResearch.WordTrace tailWord_7608291 prefixEnd_7608291 3906710242276797260172613 := by
  unfold tailWord_7608291
  simp only [CollatzResearch.WordTrace]
  refine ⟨277497170079468574497976727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184998113386312382998651151 277497170079468574497976727)
  ·
    refine ⟨416245755119202861746965091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277497170079468574497976727 416245755119202861746965091)
    ·
      refine ⟨624368632678804292620447637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416245755119202861746965091 624368632678804292620447637)
      ·
        refine ⟨29267279656818951216583483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 624368632678804292620447637 29267279656818951216583483)
        ·
          refine ⟨43900919485228426824875225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29267279656818951216583483 43900919485228426824875225)
          ·
            refine ⟨32925689613921320118656419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43900919485228426824875225 32925689613921320118656419)
            ·
              refine ⟨49388534420881980177984629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32925689613921320118656419 49388534420881980177984629)
              ·
                refine ⟨4630175101957685641686059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49388534420881980177984629 4630175101957685641686059)
                ·
                  refine ⟨6945262652936528462529089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630175101957685641686059 6945262652936528462529089)
                  ·
                    refine ⟨5208946989702396346896817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945262652936528462529089 5208946989702396346896817)
                    ·
                      refine ⟨3906710242276797260172613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208946989702396346896817 3906710242276797260172613)
                      ·
                        rfl

theorem cell23_7608291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7608291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608291 prefixEnd_7608291 := by exact prefixLift 7608291
  have htrace : WordTrace (prefixWord ++ tailWord_7608291) baseStart_7608291 baseEnd_7608291 := by
    simpa [prefixWord, tailWord_7608291, baseEnd_7608291] using wordTrace_append hprefix tailTrace_7608291
  have hstable : (prefixWord ++ tailWord_7608291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608291).length < 2 ^ (prefixWord ++ tailWord_7608291).sum := by decide
  have hdescent : baseEnd_7608291 < baseStart_7608291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608317 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_7608317 : Nat := 118140960795 + 7608317 * 2 ^ 59
def prefixEnd_7608317 : Nat := 4983230072969 + 3 ^ 40 * 7608317 * 2
def baseEnd_7608317 : Nat := 3906723592773814158447493

theorem tailTrace_7608317 : CollatzResearch.WordTrace tailWord_7608317 prefixEnd_7608317 3906723592773814158447493 := by
  unfold tailWord_7608317
  simp only [CollatzResearch.WordTrace]
  refine ⟨277498118377374380938423205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184998745584916253958948803 277498118377374380938423205)
  ·
    refine ⟨52030897195757696425954351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277498118377374380938423205 52030897195757696425954351)
    ·
      refine ⟨78046345793636544638931527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52030897195757696425954351 78046345793636544638931527)
      ·
        refine ⟨117069518690454816958397291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78046345793636544638931527 117069518690454816958397291)
        ·
          refine ⟨175604278035682225437595937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117069518690454816958397291 175604278035682225437595937)
          ·
            refine ⟨131703208526761669078196953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175604278035682225437595937 131703208526761669078196953)
            ·
              refine ⟨98777406395071251808647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131703208526761669078196953 98777406395071251808647715)
              ·
                refine ⟨148166109592606877712971573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98777406395071251808647715 148166109592606877712971573)
                ·
                  refine ⟨13890572774306894785591085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148166109592606877712971573 13890572774306894785591085)
                  ·
                    refine ⟨5208964790365085544596657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13890572774306894785591085 5208964790365085544596657)
                    ·
                      refine ⟨3906723592773814158447493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5208964790365085544596657 3906723592773814158447493)
                      ·
                        rfl

theorem cell23_7608317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_7608317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608317 prefixEnd_7608317 := by exact prefixLift 7608317
  have htrace : WordTrace (prefixWord ++ tailWord_7608317) baseStart_7608317 baseEnd_7608317 := by
    simpa [prefixWord, tailWord_7608317, baseEnd_7608317] using wordTrace_append hprefix tailTrace_7608317
  have hstable : (prefixWord ++ tailWord_7608317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608317).length < 2 ^ (prefixWord ++ tailWord_7608317).sum := by decide
  have hdescent : baseEnd_7608317 < baseStart_7608317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608381 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7608381 : Nat := 118140960795 + 7608381 * 2 ^ 59
def prefixEnd_7608381 : Nat := 4983230072969 + 3 ^ 40 * 7608381 * 2
def baseEnd_7608381 : Nat := 3906756455535701908047199

theorem tailTrace_7608381 : CollatzResearch.WordTrace tailWord_7608381 prefixEnd_7608381 3906756455535701908047199 := by
  unfold tailWord_7608381
  simp only [CollatzResearch.WordTrace]
  refine ⟨277500452649142519868752997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185000301766095013245835331 277500452649142519868752997)
  ·
    refine ⟨52031334871714222475391187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277500452649142519868752997 52031334871714222475391187)
    ·
      refine ⟨78047002307571333713086781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52031334871714222475391187 78047002307571333713086781)
      ·
        refine ⟨29267625865339250142407543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78047002307571333713086781 29267625865339250142407543)
        ·
          refine ⟨43901438798008875213611315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29267625865339250142407543 43901438798008875213611315)
          ·
            refine ⟨65852158197013312820416973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43901438798008875213611315 65852158197013312820416973)
            ·
              refine ⟨24694559323879992307656365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65852158197013312820416973 24694559323879992307656365)
              ·
                refine ⟨9260459746454997115371137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24694559323879992307656365 9260459746454997115371137)
                ·
                  refine ⟨6945344809841247836528353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9260459746454997115371137 6945344809841247836528353)
                  ·
                    refine ⟨5209008607380935877396265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945344809841247836528353 5209008607380935877396265)
                    ·
                      refine ⟨3906756455535701908047199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209008607380935877396265 3906756455535701908047199)
                      ·
                        rfl

theorem cell23_7608381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7608381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608381 prefixEnd_7608381 := by exact prefixLift 7608381
  have htrace : WordTrace (prefixWord ++ tailWord_7608381) baseStart_7608381 baseEnd_7608381 := by
    simpa [prefixWord, tailWord_7608381, baseEnd_7608381] using wordTrace_append hprefix tailTrace_7608381
  have hstable : (prefixWord ++ tailWord_7608381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608381).length < 2 ^ (prefixWord ++ tailWord_7608381).sum := by decide
  have hdescent : baseEnd_7608381 < baseStart_7608381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608410 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7608410 : Nat := 118140960795 + 7608410 * 2 ^ 59
def prefixEnd_7608410 : Nat := 4983230072969 + 3 ^ 40 * 7608410 * 2
def baseEnd_7608410 : Nat := 3906771346474682294584565

theorem tailTrace_7608410 : CollatzResearch.WordTrace tailWord_7608410 prefixEnd_7608410 3906771346474682294584565 := by
  unfold tailWord_7608410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69375377591509364455389671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185001006910691638547705789 69375377591509364455389671)
  ·
    refine ⟨104063066387264046683084507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69375377591509364455389671 104063066387264046683084507)
    ·
      refine ⟨156094599580896070024626761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104063066387264046683084507 156094599580896070024626761)
      ·
        refine ⟨117070949685672052518470071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156094599580896070024626761 117070949685672052518470071)
        ·
          refine ⟨175606424528508078777705107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117070949685672052518470071 175606424528508078777705107)
          ·
            refine ⟨263409636792762118166557661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175606424528508078777705107 263409636792762118166557661)
            ·
              refine ⟨98778613797285794312459123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263409636792762118166557661 98778613797285794312459123)
              ·
                refine ⟨148167920695928691468688685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98778613797285794312459123 148167920695928691468688685)
                ·
                  refine ⟨55562970260973259300758257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148167920695928691468688685 55562970260973259300758257)
                  ·
                    refine ⟨41672227695729944475568693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55562970260973259300758257 41672227695729944475568693)
                    ·
                      refine ⟨3906771346474682294584565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41672227695729944475568693 3906771346474682294584565)
                      ·
                        rfl

theorem cell23_7608410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7608410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608410 prefixEnd_7608410 := by exact prefixLift 7608410
  have htrace : WordTrace (prefixWord ++ tailWord_7608410) baseStart_7608410 baseEnd_7608410 := by
    simpa [prefixWord, tailWord_7608410, baseEnd_7608410] using wordTrace_append hprefix tailTrace_7608410
  have hstable : (prefixWord ++ tailWord_7608410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608410).length < 2 ^ (prefixWord ++ tailWord_7608410).sum := by decide
  have hdescent : baseEnd_7608410 < baseStart_7608410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608421 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 5]
def baseStart_7608421 : Nat := 118140960795 + 7608421 * 2 ^ 59
def prefixEnd_7608421 : Nat := 4983230072969 + 3 ^ 40 * 7608421 * 2
def baseEnd_7608421 : Nat := 434086332751320194616335

theorem tailTrace_7608421 : CollatzResearch.WordTrace tailWord_7608421 prefixEnd_7608421 434086332751320194616335 := by
  unfold tailWord_7608421
  simp only [CollatzResearch.WordTrace]
  refine ⟨277501911568997606700209117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185001274379331737800139411 277501911568997606700209117)
  ·
    refine ⟨104063216838374102512578419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277501911568997606700209117 104063216838374102512578419)
    ·
      refine ⟨156094825257561153768867629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104063216838374102512578419 156094825257561153768867629)
      ·
        refine ⟨58535559471585432663325361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156094825257561153768867629 58535559471585432663325361)
        ·
          refine ⟨43901669603689074497494021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58535559471585432663325361 43901669603689074497494021)
          ·
            refine ⟨8231563050691701468280129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43901669603689074497494021 8231563050691701468280129)
            ·
              refine ⟨6173672288018776101210097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8231563050691701468280129 6173672288018776101210097)
              ·
                refine ⟨4630254216014082075907573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173672288018776101210097 4630254216014082075907573)
                ·
                  refine ⟨434086332751320194616335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630254216014082075907573 434086332751320194616335)
                  ·
                    rfl

theorem cell23_7608421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_7608421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608421 prefixEnd_7608421 := by exact prefixLift 7608421
  have htrace : WordTrace (prefixWord ++ tailWord_7608421) baseStart_7608421 baseEnd_7608421 := by
    simpa [prefixWord, tailWord_7608421, baseEnd_7608421] using wordTrace_append hprefix tailTrace_7608421
  have hstable : (prefixWord ++ tailWord_7608421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608421).length < 2 ^ (prefixWord ++ tailWord_7608421).sum := by decide
  have hdescent : baseEnd_7608421 < baseStart_7608421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608457 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 3]
def baseStart_7608457 : Nat := 118140960795 + 7608457 * 2 ^ 59
def prefixEnd_7608457 : Nat := 4983230072969 + 3 ^ 40 * 7608457 * 2
def baseEnd_7608457 : Nat := 3906795480065443610696849

theorem tailTrace_7608457 : CollatzResearch.WordTrace tailWord_7608457 prefixEnd_7608457 3906795480065443610696849 := by
  unfold tailWord_7608457
  simp only [CollatzResearch.WordTrace]
  refine ⟨277503224596867184848519625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185002149731244789899013083 277503224596867184848519625)
  ·
    refine ⟨208127418447650388636389719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277503224596867184848519625 208127418447650388636389719)
    ·
      refine ⟨312191127671475582954584579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208127418447650388636389719 312191127671475582954584579)
      ·
        refine ⟨468286691507213374431876869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312191127671475582954584579 468286691507213374431876869)
        ·
          refine ⟨87803754657602507705976913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468286691507213374431876869 87803754657602507705976913)
          ·
            refine ⟨65852815993201880779482685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87803754657602507705976913 65852815993201880779482685)
            ·
              refine ⟨24694805997450705292306007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65852815993201880779482685 24694805997450705292306007)
              ·
                refine ⟨37042208996176057938459011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24694805997450705292306007 37042208996176057938459011)
                ·
                  refine ⟨55563313494264086907688517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37042208996176057938459011 55563313494264086907688517)
                  ·
                    refine ⟨10418121280174516295191597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55563313494264086907688517 10418121280174516295191597)
                    ·
                      refine ⟨3906795480065443610696849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418121280174516295191597 3906795480065443610696849)
                      ·
                        rfl

theorem cell23_7608457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_7608457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608457 prefixEnd_7608457 := by exact prefixLift 7608457
  have htrace : WordTrace (prefixWord ++ tailWord_7608457) baseStart_7608457 baseEnd_7608457 := by
    simpa [prefixWord, tailWord_7608457, baseEnd_7608457] using wordTrace_append hprefix tailTrace_7608457
  have hstable : (prefixWord ++ tailWord_7608457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608457).length < 2 ^ (prefixWord ++ tailWord_7608457).sum := by decide
  have hdescent : baseEnd_7608457 < baseStart_7608457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608477 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 8]
def baseStart_7608477 : Nat := 118140960795 + 7608477 * 2 ^ 59
def prefixEnd_7608477 : Nat := 4983230072969 + 3 ^ 40 * 7608477 * 2
def baseEnd_7608477 : Nat := 434089527742059281382973

theorem tailTrace_7608477 : CollatzResearch.WordTrace tailWord_7608477 prefixEnd_7608477 434089527742059281382973 := by
  unfold tailWord_7608477
  simp only [CollatzResearch.WordTrace]
  refine ⟨277503954056794728264247685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185002636037863152176165123 277503954056794728264247685)
  ·
    refine ⟨52031991385649011549546441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277503954056794728264247685 52031991385649011549546441)
    ·
      refine ⟨39023993539236758662159831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52031991385649011549546441 39023993539236758662159831)
      ·
        refine ⟨58535990308855137993239747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39023993539236758662159831 58535990308855137993239747)
        ·
          refine ⟨87803985463282706989859621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58535990308855137993239747 87803985463282706989859621)
          ·
            refine ⟨16463247274365507560598679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87803985463282706989859621 16463247274365507560598679)
            ·
              refine ⟨24694870911548261340898019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16463247274365507560598679 24694870911548261340898019)
              ·
                refine ⟨37042306367322392011347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24694870911548261340898019 37042306367322392011347029)
                ·
                  refine ⟨434089527742059281382973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37042306367322392011347029 434089527742059281382973)
                  ·
                    rfl

theorem cell23_7608477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_7608477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608477 prefixEnd_7608477 := by exact prefixLift 7608477
  have htrace : WordTrace (prefixWord ++ tailWord_7608477) baseStart_7608477 baseEnd_7608477 := by
    simpa [prefixWord, tailWord_7608477, baseEnd_7608477] using wordTrace_append hprefix tailTrace_7608477
  have hstable : (prefixWord ++ tailWord_7608477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608477).length < 2 ^ (prefixWord ++ tailWord_7608477).sum := by decide
  have hdescent : baseEnd_7608477 < baseStart_7608477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608481 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 1, 4]
def baseStart_7608481 : Nat := 118140960795 + 7608481 * 2 ^ 59
def prefixEnd_7608481 : Nat := 4983230072969 + 3 ^ 40 * 7608481 * 2
def baseEnd_7608481 : Nat := 1302269267867050505598913

theorem tailTrace_7608481 : CollatzResearch.WordTrace tailWord_7608481 prefixEnd_7608481 1302269267867050505598913 := by
  unfold tailWord_7608481
  simp only [CollatzResearch.WordTrace]
  refine ⟨277504099948780236947393297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185002733299186824631595531 277504099948780236947393297)
  ·
    refine ⟨208128074961585177710544973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277504099948780236947393297 208128074961585177710544973)
    ·
      refine ⟨78048028110594441641454365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208128074961585177710544973 78048028110594441641454365)
      ·
        refine ⟨29268010541472915615545387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78048028110594441641454365 29268010541472915615545387)
        ·
          refine ⟨43902015812209373423318081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29268010541472915615545387 43902015812209373423318081)
          ·
            refine ⟨32926511859157030067488561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43902015812209373423318081 32926511859157030067488561)
            ·
              refine ⟨24694883894367772550616421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32926511859157030067488561 24694883894367772550616421)
              ·
                refine ⟨4630290730193957353240579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24694883894367772550616421 4630290730193957353240579)
                ·
                  refine ⟨6945436095290936029860869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630290730193957353240579 6945436095290936029860869)
                  ·
                    refine ⟨1302269267867050505598913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945436095290936029860869 1302269267867050505598913)
                    ·
                      rfl

theorem cell23_7608481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_7608481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608481 prefixEnd_7608481 := by exact prefixLift 7608481
  have htrace : WordTrace (prefixWord ++ tailWord_7608481) baseStart_7608481 baseEnd_7608481 := by
    simpa [prefixWord, tailWord_7608481, baseEnd_7608481] using wordTrace_append hprefix tailTrace_7608481
  have hstable : (prefixWord ++ tailWord_7608481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608481).length < 2 ^ (prefixWord ++ tailWord_7608481).sum := by decide
  have hdescent : baseEnd_7608481 < baseStart_7608481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608504 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_7608504 : Nat := 118140960795 + 7608504 * 2 ^ 59
def prefixEnd_7608504 : Nat := 4983230072969 + 3 ^ 40 * 7608504 * 2
def baseEnd_7608504 : Nat := 3906819613656204926809133

theorem tailTrace_7608504 : CollatzResearch.WordTrace tailWord_7608504 prefixEnd_7608504 3906819613656204926809133 := by
  unfold tailWord_7608504
  simp only [CollatzResearch.WordTrace]
  refine ⟨138752469413848455937740283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185003292551797941250320377 138752469413848455937740283)
  ·
    refine ⟨208128704120772683906610425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138752469413848455937740283 208128704120772683906610425)
    ·
      refine ⟨156096528090579512929957819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208128704120772683906610425 156096528090579512929957819)
      ·
        refine ⟨234144792135869269394936729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156096528090579512929957819 234144792135869269394936729)
        ·
          refine ⟨175608594101901952046202547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234144792135869269394936729 175608594101901952046202547)
          ·
            refine ⟨263412891152852928069303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175608594101901952046202547 263412891152852928069303821)
            ·
              refine ⟨98779834182319848025988933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263412891152852928069303821 98779834182319848025988933)
              ·
                refine ⟨18521218909184971504872925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98779834182319848025988933 18521218909184971504872925)
                ·
                  refine ⟨6945457090944364314327347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18521218909184971504872925 6945457090944364314327347)
                  ·
                    refine ⟨10418185636416546471491021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6945457090944364314327347 10418185636416546471491021)
                    ·
                      refine ⟨3906819613656204926809133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418185636416546471491021 3906819613656204926809133)
                      ·
                        rfl

theorem cell23_7608504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_7608504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608504 prefixEnd_7608504 := by exact prefixLift 7608504
  have htrace : WordTrace (prefixWord ++ tailWord_7608504) baseStart_7608504 baseEnd_7608504 := by
    simpa [prefixWord, tailWord_7608504, baseEnd_7608504] using wordTrace_append hprefix tailTrace_7608504
  have hstable : (prefixWord ++ tailWord_7608504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608504).length < 2 ^ (prefixWord ++ tailWord_7608504).sum := by decide
  have hdescent : baseEnd_7608504 < baseStart_7608504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 1, 1, 3]
def baseStart_7608521 : Nat := 118140960795 + 7608521 * 2 ^ 59
def prefixEnd_7608521 : Nat := 4983230072969 + 3 ^ 40 * 7608521 * 2
def baseEnd_7608521 : Nat := 3906828342827331360296555

theorem tailTrace_7608521 : CollatzResearch.WordTrace tailWord_7608521 prefixEnd_7608521 3906828342827331360296555 := by
  unfold tailWord_7608521
  simp only [CollatzResearch.WordTrace]
  refine ⟨277505558868635323778849417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185003705912423549185899611 277505558868635323778849417)
  ·
    refine ⟨208129169151476492834137063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277505558868635323778849417 208129169151476492834137063)
    ·
      refine ⟨312193753727214739251205595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208129169151476492834137063 312193753727214739251205595)
      ·
        refine ⟨468290630590822108876808393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312193753727214739251205595 468290630590822108876808393)
        ·
          refine ⟨351217972943116581657606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468290630590822108876808393 351217972943116581657606295)
          ·
            refine ⟨526826959414674872486409443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351217972943116581657606295 526826959414674872486409443)
            ·
              refine ⟨790240439122012308729614165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526826959414674872486409443 790240439122012308729614165)
              ·
                refine ⟨4630315072980540871462583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 790240439122012308729614165 4630315072980540871462583)
                ·
                  refine ⟨6945472609470811307193875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630315072980540871462583 6945472609470811307193875)
                  ·
                    refine ⟨10418208914206216960790813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6945472609470811307193875 10418208914206216960790813)
                    ·
                      refine ⟨3906828342827331360296555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418208914206216960790813 3906828342827331360296555)
                      ·
                        rfl

theorem cell23_7608521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 1, 3].length) (baseStart_7608521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608521 prefixEnd_7608521 := by exact prefixLift 7608521
  have htrace : WordTrace (prefixWord ++ tailWord_7608521) baseStart_7608521 baseEnd_7608521 := by
    simpa [prefixWord, tailWord_7608521, baseEnd_7608521] using wordTrace_append hprefix tailTrace_7608521
  have hstable : (prefixWord ++ tailWord_7608521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608521).length < 2 ^ (prefixWord ++ tailWord_7608521).sum := by decide
  have hdescent : baseEnd_7608521 < baseStart_7608521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608561 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_7608561 : Nat := 118140960795 + 7608561 * 2 ^ 59
def prefixEnd_7608561 : Nat := 4983230072969 + 3 ^ 40 * 7608561 * 2
def baseEnd_7608561 : Nat := 3906848882053511203796371

theorem tailTrace_7608561 : CollatzResearch.WordTrace tailWord_7608561 prefixEnd_7608561 3906848882053511203796371 := by
  unfold tailWord_7608561
  simp only [CollatzResearch.WordTrace]
  refine ⟨277507017788490410610305537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185004678525660273740203691 277507017788490410610305537)
  ·
    refine ⟨208130263341367807957729153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277507017788490410610305537 208130263341367807957729153)
    ·
      refine ⟨156097697506025855968296865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208130263341367807957729153 156097697506025855968296865)
      ·
        refine ⟨117073273129519391976222649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156097697506025855968296865 117073273129519391976222649)
        ·
          refine ⟨87804954847139543982166987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117073273129519391976222649 87804954847139543982166987)
          ·
            refine ⟨131707432270709315973250481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87804954847139543982166987 131707432270709315973250481)
            ·
              refine ⟨98780574203031986979937861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131707432270709315973250481 98780574203031986979937861)
              ·
                refine ⟨18521357663068497558738349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98780574203031986979937861 18521357663068497558738349)
                ·
                  refine ⟨6945509123650686584526881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18521357663068497558738349 6945509123650686584526881)
                  ·
                    refine ⟨5209131842738014938395161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945509123650686584526881 5209131842738014938395161)
                    ·
                      refine ⟨3906848882053511203796371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209131842738014938395161 3906848882053511203796371)
                      ·
                        rfl

theorem cell23_7608561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_7608561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608561 prefixEnd_7608561 := by exact prefixLift 7608561
  have htrace : WordTrace (prefixWord ++ tailWord_7608561) baseStart_7608561 baseEnd_7608561 := by
    simpa [prefixWord, tailWord_7608561, baseEnd_7608561] using wordTrace_append hprefix tailTrace_7608561
  have hstable : (prefixWord ++ tailWord_7608561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608561).length < 2 ^ (prefixWord ++ tailWord_7608561).sum := by decide
  have hdescent : baseEnd_7608561 < baseStart_7608561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608597 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_7608597 : Nat := 118140960795 + 7608597 * 2 ^ 59
def prefixEnd_7608597 : Nat := 4983230072969 + 3 ^ 40 * 7608597 * 2
def baseEnd_7608597 : Nat := 1302289122452357687648735

theorem tailTrace_7608597 : CollatzResearch.WordTrace tailWord_7608597 prefixEnd_7608597 1302289122452357687648735 := by
  unfold tailWord_7608597
  simp only [CollatzResearch.WordTrace]
  refine ⟨277508330816359988758616045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185005553877573325839077363 277508330816359988758616045)
  ·
    refine ⟨104065624056134995784481017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277508330816359988758616045 104065624056134995784481017)
    ·
      refine ⟨78049218042101246838360763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104065624056134995784481017 78049218042101246838360763)
      ·
        refine ⟨117073827063151870257541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78049218042101246838360763 117073827063151870257541145)
        ·
          refine ⟨87805370297363902693155859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117073827063151870257541145 87805370297363902693155859)
          ·
            refine ⟨131708055446045854039733789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87805370297363902693155859 131708055446045854039733789)
            ·
              refine ⟨49390520792267195264900171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131708055446045854039733789 49390520792267195264900171)
              ·
                refine ⟨74085781188400792897350257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49390520792267195264900171 74085781188400792897350257)
                ·
                  refine ⟨55564335891300594673012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74085781188400792897350257 55564335891300594673012693)
                  ·
                    refine ⟨1302289122452357687648735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55564335891300594673012693 1302289122452357687648735)
                    ·
                      rfl

theorem cell23_7608597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_7608597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608597 prefixEnd_7608597 := by exact prefixLift 7608597
  have htrace : WordTrace (prefixWord ++ tailWord_7608597) baseStart_7608597 baseEnd_7608597 := by
    simpa [prefixWord, tailWord_7608597, baseEnd_7608597] using wordTrace_append hprefix tailTrace_7608597
  have hstable : (prefixWord ++ tailWord_7608597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608597).length < 2 ^ (prefixWord ++ tailWord_7608597).sum := by decide
  have hdescent : baseEnd_7608597 < baseStart_7608597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608611 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 3]
def baseStart_7608611 : Nat := 118140960795 + 7608611 * 2 ^ 59
def prefixEnd_7608611 : Nat := 4983230072969 + 3 ^ 40 * 7608611 * 2
def baseEnd_7608611 : Nat := 3906874556086236008171141

theorem tailTrace_7608611 : CollatzResearch.WordTrace tailWord_7608611 prefixEnd_7608611 3906874556086236008171141 := by
  unfold tailWord_7608611
  simp only [CollatzResearch.WordTrace]
  refine ⟨277508841438309269149625687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185005894292206179433083791 277508841438309269149625687)
  ·
    refine ⟨416263262157463903724438531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277508841438309269149625687 416263262157463903724438531)
    ·
      refine ⟨624394893236195855586657797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416263262157463903724438531 624394893236195855586657797)
      ·
        refine ⟨117074042481786722922498337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624394893236195855586657797 117074042481786722922498337)
        ·
          refine ⟨87805531861340042191873753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117074042481786722922498337 87805531861340042191873753)
          ·
            refine ⟨65854148896005031643905315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87805531861340042191873753 65854148896005031643905315)
            ·
              refine ⟨98781223344007547465857973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65854148896005031643905315 98781223344007547465857973)
              ·
                refine ⟨9260739688500707574924185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98781223344007547465857973 9260739688500707574924185)
                ·
                  refine ⟨6945554766375530681193139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9260739688500707574924185 6945554766375530681193139)
                  ·
                    refine ⟨10418332149563296021789709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6945554766375530681193139 10418332149563296021789709)
                    ·
                      refine ⟨3906874556086236008171141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418332149563296021789709 3906874556086236008171141)
                      ·
                        rfl

theorem cell23_7608611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_7608611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608611 prefixEnd_7608611 := by exact prefixLift 7608611
  have htrace : WordTrace (prefixWord ++ tailWord_7608611) baseStart_7608611 baseEnd_7608611 := by
    simpa [prefixWord, tailWord_7608611, baseEnd_7608611] using wordTrace_append hprefix tailTrace_7608611
  have hstable : (prefixWord ++ tailWord_7608611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608611).length < 2 ^ (prefixWord ++ tailWord_7608611).sum := by decide
  have hdescent : baseEnd_7608611 < baseStart_7608611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608627 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 8]
def baseStart_7608627 : Nat := 118140960795 + 7608627 * 2 ^ 59
def prefixEnd_7608627 : Nat := 4983230072969 + 3 ^ 40 * 7608627 * 2
def baseEnd_7608627 : Nat := 1302294257258902648523689

theorem tailTrace_7608627 : CollatzResearch.WordTrace tailWord_7608627 prefixEnd_7608627 1302294257258902648523689 := by
  unfold tailWord_7608627
  simp only [CollatzResearch.WordTrace]
  refine ⟨277509425006251303882208135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185006283337500869254805423 277509425006251303882208135)
  ·
    refine ⟨416264137509376955823312203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277509425006251303882208135 416264137509376955823312203)
    ·
      refine ⟨624396206264065433734968305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416264137509376955823312203 624396206264065433734968305)
      ·
        refine ⟨468297154698049075301226229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624396206264065433734968305 468297154698049075301226229)
        ·
          refine ⟨43902858252942100809489959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468297154698049075301226229 43902858252942100809489959)
          ·
            refine ⟨65854287379413151214234939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43902858252942100809489959 65854287379413151214234939)
            ·
              refine ⟨98781431069119726821352409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65854287379413151214234939 98781431069119726821352409)
              ·
                refine ⟨74086073301839795116014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98781431069119726821352409 74086073301839795116014307)
                ·
                  refine ⟨111129109952759692674021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74086073301839795116014307 111129109952759692674021461)
                  ·
                    refine ⟨1302294257258902648523689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111129109952759692674021461 1302294257258902648523689)
                    ·
                      rfl

theorem cell23_7608627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_7608627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608627 prefixEnd_7608627 := by exact prefixLift 7608627
  have htrace : WordTrace (prefixWord ++ tailWord_7608627) baseStart_7608627 baseEnd_7608627 := by
    simpa [prefixWord, tailWord_7608627, baseEnd_7608627] using wordTrace_append hprefix tailTrace_7608627
  have hstable : (prefixWord ++ tailWord_7608627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608627).length < 2 ^ (prefixWord ++ tailWord_7608627).sum := by decide
  have hdescent : baseEnd_7608627 < baseStart_7608627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608654 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_7608654 : Nat := 118140960795 + 7608654 * 2 ^ 59
def prefixEnd_7608654 : Nat := 4983230072969 + 3 ^ 40 * 7608654 * 2
def baseEnd_7608654 : Nat := 3906896635754379339933443

theorem tailTrace_7608654 : CollatzResearch.WordTrace tailWord_7608654 prefixEnd_7608654 3906896635754379339933443 := by
  unfold tailWord_7608654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34688801222144185936680127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185006939851435658328960677 34688801222144185936680127)
  ·
    refine ⟨52033201833216278905020191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34688801222144185936680127 52033201833216278905020191)
    ·
      refine ⟨78049802749824418357530287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52033201833216278905020191 78049802749824418357530287)
      ·
        refine ⟨117074704124736627536295431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78049802749824418357530287 117074704124736627536295431)
        ·
          refine ⟨175612056187104941304443147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117074704124736627536295431 175612056187104941304443147)
          ·
            refine ⟨263418084280657411956664721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175612056187104941304443147 263418084280657411956664721)
            ·
              refine ⟨197563563210493058967498541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263418084280657411956664721 197563563210493058967498541)
              ·
                refine ⟨74086336203934897112811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197563563210493058967498541 74086336203934897112811953)
                ·
                  refine ⟨55564752152951172834608965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74086336203934897112811953 55564752152951172834608965)
                  ·
                    refine ⟨10418391028678344906489181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55564752152951172834608965 10418391028678344906489181)
                    ·
                      refine ⟨3906896635754379339933443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418391028678344906489181 3906896635754379339933443)
                      ·
                        rfl

theorem cell23_7608654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_7608654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608654 prefixEnd_7608654 := by exact prefixLift 7608654
  have htrace : WordTrace (prefixWord ++ tailWord_7608654) baseStart_7608654 baseEnd_7608654 := by
    simpa [prefixWord, tailWord_7608654, baseEnd_7608654] using wordTrace_append hprefix tailTrace_7608654
  have hstable : (prefixWord ++ tailWord_7608654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608654).length < 2 ^ (prefixWord ++ tailWord_7608654).sum := by decide
  have hdescent : baseEnd_7608654 < baseStart_7608654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608708 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 5]
def baseStart_7608708 : Nat := 118140960795 + 7608708 * 2 ^ 59
def prefixEnd_7608708 : Nat := 4983230072969 + 3 ^ 40 * 7608708 * 2
def baseEnd_7608708 : Nat := 434102707078858014295355

theorem tailTrace_7608708 : CollatzResearch.WordTrace tailWord_7608708 prefixEnd_7608708 434102707078858014295355 := by
  unfold tailWord_7608708
  simp only [CollatzResearch.WordTrace]
  refine ⟨138756189659478927357953389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185008252879305236477271185 138756189659478927357953389)
  ·
    refine ⟨52033571122304597759232521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138756189659478927357953389 52033571122304597759232521)
    ·
      refine ⟨39025178341728448319424391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52033571122304597759232521 39025178341728448319424391)
      ·
        refine ⟨58537767512592672479136587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39025178341728448319424391 58537767512592672479136587)
        ·
          refine ⟨87806651268889008718704881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58537767512592672479136587 87806651268889008718704881)
          ·
            refine ⟨65854988451666756539028661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87806651268889008718704881 65854988451666756539028661)
            ·
              refine ⟨6173905167343758425533937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65854988451666756539028661 6173905167343758425533937)
              ·
                refine ⟨4630428875507818819150453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173905167343758425533937 4630428875507818819150453)
                ·
                  refine ⟨434102707078858014295355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4630428875507818819150453 434102707078858014295355)
                  ·
                    rfl

theorem cell23_7608708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_7608708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608708 prefixEnd_7608708 := by exact prefixLift 7608708
  have htrace : WordTrace (prefixWord ++ tailWord_7608708) baseStart_7608708 baseEnd_7608708 := by
    simpa [prefixWord, tailWord_7608708, baseEnd_7608708] using wordTrace_append hprefix tailTrace_7608708
  have hstable : (prefixWord ++ tailWord_7608708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608708).length < 2 ^ (prefixWord ++ tailWord_7608708).sum := by decide
  have hdescent : baseEnd_7608708 < baseStart_7608708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608711 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_7608711 : Nat := 118140960795 + 7608711 * 2 ^ 59
def prefixEnd_7608711 : Nat := 4983230072969 + 3 ^ 40 * 7608711 * 2
def baseEnd_7608711 : Nat := 3906925904151685616920681

theorem tailTrace_7608711 : CollatzResearch.WordTrace tailWord_7608711 prefixEnd_7608711 3906925904151685616920681 := by
  unfold tailWord_7608711
  simp only [CollatzResearch.WordTrace]
  refine ⟨277512488737946986228265987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185008325825297990818843991 277512488737946986228265987)
  ·
    refine ⟨416268733106920479342398981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277512488737946986228265987 416268733106920479342398981)
    ·
      refine ⟨78050387457547589876699809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416268733106920479342398981 78050387457547589876699809)
      ·
        refine ⟨58537790593160692407524857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78050387457547589876699809 58537790593160692407524857)
        ·
          refine ⟨43903342944870519305643643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58537790593160692407524857 43903342944870519305643643)
          ·
            refine ⟨65855014417305778958465465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43903342944870519305643643 65855014417305778958465465)
            ·
              refine ⟨49391260812979334218849099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65855014417305778958465465 49391260812979334218849099)
              ·
                refine ⟨74086891219469001328273649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49391260812979334218849099 74086891219469001328273649)
                ·
                  refine ⟨55565168414601750996205237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74086891219469001328273649 55565168414601750996205237)
                  ·
                    refine ⟨5209234538868914155894241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55565168414601750996205237 5209234538868914155894241)
                    ·
                      refine ⟨3906925904151685616920681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209234538868914155894241 3906925904151685616920681)
                      ·
                        rfl

theorem cell23_7608711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_7608711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608711 prefixEnd_7608711 := by exact prefixLift 7608711
  have htrace : WordTrace (prefixWord ++ tailWord_7608711) baseStart_7608711 baseEnd_7608711 := by
    simpa [prefixWord, tailWord_7608711, baseEnd_7608711] using wordTrace_append hprefix tailTrace_7608711
  have hstable : (prefixWord ++ tailWord_7608711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608711).length < 2 ^ (prefixWord ++ tailWord_7608711).sum := by decide
  have hdescent : baseEnd_7608711 < baseStart_7608711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608741 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_7608741 : Nat := 118140960795 + 7608741 * 2 ^ 59
def prefixEnd_7608741 : Nat := 4983230072969 + 3 ^ 40 * 7608741 * 2
def baseEnd_7608741 : Nat := 3906941308571320499545543

theorem tailTrace_7608741 : CollatzResearch.WordTrace tailWord_7608741 prefixEnd_7608741 3906941308571320499545543 := by
  unfold tailWord_7608741
  simp only [CollatzResearch.WordTrace]
  refine ⟨277513582927838301351858077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185009055285225534234572051 277513582927838301351858077)
  ·
    refine ⟨104067593597939363006946779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277513582927838301351858077 104067593597939363006946779)
    ·
      refine ⟨156101390396909044510420169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104067593597939363006946779 156101390396909044510420169)
      ·
        refine ⟨117076042797681783382815127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156101390396909044510420169 117076042797681783382815127)
        ·
          refine ⟨175614064196522675074222691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117076042797681783382815127 175614064196522675074222691)
          ·
            refine ⟨263421096294784012611334037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175614064196522675074222691 263421096294784012611334037)
            ·
              refine ⟨12347863888818000591156283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263421096294784012611334037 12347863888818000591156283)
              ·
                refine ⟨18521795833227000886734425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12347863888818000591156283 18521795833227000886734425)
                ·
                  refine ⟨13891346874920250665050819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18521795833227000886734425 13891346874920250665050819)
                  ·
                    refine ⟨20837020312380375997576229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13891346874920250665050819 20837020312380375997576229)
                    ·
                      refine ⟨3906941308571320499545543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20837020312380375997576229 3906941308571320499545543)
                      ·
                        rfl

theorem cell23_7608741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_7608741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608741 prefixEnd_7608741 := by exact prefixLift 7608741
  have htrace : WordTrace (prefixWord ++ tailWord_7608741) baseStart_7608741 baseEnd_7608741 := by
    simpa [prefixWord, tailWord_7608741, baseEnd_7608741] using wordTrace_append hprefix tailTrace_7608741
  have hstable : (prefixWord ++ tailWord_7608741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608741).length < 2 ^ (prefixWord ++ tailWord_7608741).sum := by decide
  have hdescent : baseEnd_7608741 < baseStart_7608741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608754 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_7608754 : Nat := 118140960795 + 7608754 * 2 ^ 59
def prefixEnd_7608754 : Nat := 4983230072969 + 3 ^ 40 * 7608754 * 2
def baseEnd_7608754 : Nat := 3906947983819828948682983

theorem tailTrace_7608754 : CollatzResearch.WordTrace tailWord_7608754 prefixEnd_7608754 3906947983819828948682983 := by
  unfold tailWord_7608754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69378514269197801143020329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185009371384527469714720877 69378514269197801143020329)
  ·
    refine ⟨52033885701898350857265247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69378514269197801143020329 52033885701898350857265247)
    ·
      refine ⟨78050828552847526285897871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52033885701898350857265247 78050828552847526285897871)
      ·
        refine ⟨117076242829271289428846807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78050828552847526285897871 117076242829271289428846807)
        ·
          refine ⟨175614364243906934143270211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117076242829271289428846807 175614364243906934143270211)
          ·
            refine ⟨263421546365860401214905317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175614364243906934143270211 263421546365860401214905317)
            ·
              refine ⟨49391539943598825227794747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263421546365860401214905317 49391539943598825227794747)
              ·
                refine ⟨74087309915398237841692121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49391539943598825227794747 74087309915398237841692121)
                ·
                  refine ⟨55565482436548678381269091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74087309915398237841692121 55565482436548678381269091)
                  ·
                    refine ⟨83348223654823017571903637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55565482436548678381269091 83348223654823017571903637)
                    ·
                      refine ⟨3906947983819828948682983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83348223654823017571903637 3906947983819828948682983)
                      ·
                        rfl

theorem cell23_7608754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_7608754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608754 prefixEnd_7608754 := by exact prefixLift 7608754
  have htrace : WordTrace (prefixWord ++ tailWord_7608754) baseStart_7608754 baseEnd_7608754 := by
    simpa [prefixWord, tailWord_7608754, baseEnd_7608754] using wordTrace_append hprefix tailTrace_7608754
  have hstable : (prefixWord ++ tailWord_7608754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608754).length < 2 ^ (prefixWord ++ tailWord_7608754).sum := by decide
  have hdescent : baseEnd_7608754 < baseStart_7608754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608804 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_7608804 : Nat := 118140960795 + 7608804 * 2 ^ 59
def prefixEnd_7608804 : Nat := 4983230072969 + 3 ^ 40 * 7608804 * 2
def baseEnd_7608804 : Nat := 3906973657852553753057753

theorem tailTrace_7608804 : CollatzResearch.WordTrace tailWord_7608804 prefixEnd_7608804 3906973657852553753057753 := by
  unfold tailWord_7608804
  simp only [CollatzResearch.WordTrace]
  refine ⟨138757940363305031555700733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185010587151073375407600977 138757940363305031555700733)
  ·
    refine ⟨52034227636239386833387775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138757940363305031555700733 52034227636239386833387775)
    ·
      refine ⟨78051341454359080250081663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52034227636239386833387775 78051341454359080250081663)
      ·
        refine ⟨117077012181538620375122495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78051341454359080250081663 117077012181538620375122495)
        ·
          refine ⟨175615518272307930562683743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117077012181538620375122495 175615518272307930562683743)
          ·
            refine ⟨263423277408461895844025615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175615518272307930562683743 263423277408461895844025615)
            ·
              refine ⟨395134916112692843766038423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263423277408461895844025615 395134916112692843766038423)
              ·
                refine ⟨592702374169039265649057635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395134916112692843766038423 592702374169039265649057635)
                ·
                  refine ⟨889053561253558898473586453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592702374169039265649057635 889053561253558898473586453)
                  ·
                    refine ⟨41674385683760573365949365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 889053561253558898473586453 41674385683760573365949365)
                    ·
                      refine ⟨3906973657852553753057753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41674385683760573365949365 3906973657852553753057753)
                      ·
                        rfl

theorem cell23_7608804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_7608804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608804 prefixEnd_7608804 := by exact prefixLift 7608804
  have htrace : WordTrace (prefixWord ++ tailWord_7608804) baseStart_7608804 baseEnd_7608804 := by
    simpa [prefixWord, tailWord_7608804, baseEnd_7608804] using wordTrace_append hprefix tailTrace_7608804
  have hstable : (prefixWord ++ tailWord_7608804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608804).length < 2 ^ (prefixWord ++ tailWord_7608804).sum := by decide
  have hdescent : baseEnd_7608804 < baseStart_7608804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608811 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 1, 5]
def baseStart_7608811 : Nat := 118140960795 + 7608811 * 2 ^ 59
def prefixEnd_7608811 : Nat := 4983230072969 + 3 ^ 40 * 7608811 * 2
def baseEnd_7608811 : Nat := 1302325750739045075223407

theorem tailTrace_7608811 : CollatzResearch.WordTrace tailWord_7608811 prefixEnd_7608811 1302325750739045075223407 := by
  unfold tailWord_7608811
  simp only [CollatzResearch.WordTrace]
  refine ⟨277516136037584703306906287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185010757358389802204604191 277516136037584703306906287)
  ·
    refine ⟨416274204056377054960359431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277516136037584703306906287 416274204056377054960359431)
    ·
      refine ⟨624411306084565582440539147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416274204056377054960359431 624411306084565582440539147)
      ·
        refine ⟨936616959126848373660808721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624411306084565582440539147 936616959126848373660808721)
        ·
          refine ⟨702462719345136280245606541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936616959126848373660808721 702462719345136280245606541)
          ·
            refine ⟨263423519754426105092102453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702462719345136280245606541 263423519754426105092102453)
            ·
              refine ⟨24695954976977447352384605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263423519754426105092102453 24695954976977447352384605)
              ·
                refine ⟨9260983116366542757144227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24695954976977447352384605 9260983116366542757144227)
                ·
                  refine ⟨13891474674549814135716341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9260983116366542757144227 13891474674549814135716341)
                  ·
                    refine ⟨1302325750739045075223407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13891474674549814135716341 1302325750739045075223407)
                    ·
                      rfl

theorem cell23_7608811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 5].length) (baseStart_7608811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608811 prefixEnd_7608811 := by exact prefixLift 7608811
  have htrace : WordTrace (prefixWord ++ tailWord_7608811) baseStart_7608811 baseEnd_7608811 := by
    simpa [prefixWord, tailWord_7608811, baseEnd_7608811] using wordTrace_append hprefix tailTrace_7608811
  have hstable : (prefixWord ++ tailWord_7608811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608811).length < 2 ^ (prefixWord ++ tailWord_7608811).sum := by decide
  have hdescent : baseEnd_7608811 < baseStart_7608811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608825 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 1, 1, 3]
def baseStart_7608825 : Nat := 118140960795 + 7608825 * 2 ^ 59
def prefixEnd_7608825 : Nat := 4983230072969 + 3 ^ 40 * 7608825 * 2
def baseEnd_7608825 : Nat := 3906984440946298170895157

theorem tailTrace_7608825 : CollatzResearch.WordTrace tailWord_7608825 prefixEnd_7608825 3906984440946298170895157 := by
  unfold tailWord_7608825
  simp only [CollatzResearch.WordTrace]
  refine ⟨277516646659533983697915929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185011097773022655798610619 277516646659533983697915929)
  ·
    refine ⟨208137484994650487773436947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277516646659533983697915929 208137484994650487773436947)
    ·
      refine ⟨312206227491975731660155421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208137484994650487773436947 312206227491975731660155421)
      ·
        refine ⟨117077335309490899372558283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312206227491975731660155421 117077335309490899372558283)
        ·
          refine ⟨175616002964236349058837425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117077335309490899372558283 175616002964236349058837425)
          ·
            refine ⟨131712002223177261794128069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175616002964236349058837425 131712002223177261794128069)
            ·
              refine ⟨24696000416845736586399013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131712002223177261794128069 24696000416845736586399013)
              ·
                refine ⟨4630500078158575609949815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24696000416845736586399013 4630500078158575609949815)
                ·
                  refine ⟨6945750117237863414924723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630500078158575609949815 6945750117237863414924723)
                  ·
                    refine ⟨10418625175856795122387085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6945750117237863414924723 10418625175856795122387085)
                    ·
                      refine ⟨3906984440946298170895157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418625175856795122387085 3906984440946298170895157)
                      ·
                        rfl

theorem cell23_7608825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_7608825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608825 prefixEnd_7608825 := by exact prefixLift 7608825
  have htrace : WordTrace (prefixWord ++ tailWord_7608825) baseStart_7608825 baseEnd_7608825 := by
    simpa [prefixWord, tailWord_7608825, baseEnd_7608825] using wordTrace_append hprefix tailTrace_7608825
  have hstable : (prefixWord ++ tailWord_7608825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608825).length < 2 ^ (prefixWord ++ tailWord_7608825).sum := by decide
  have hdescent : baseEnd_7608825 < baseStart_7608825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608848 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2]
def baseStart_7608848 : Nat := 118140960795 + 7608848 * 2 ^ 59
def prefixEnd_7608848 : Nat := 4983230072969 + 3 ^ 40 * 7608848 * 2
def baseEnd_7608848 : Nat := 3906996251001351580907551

theorem tailTrace_7608848 : CollatzResearch.WordTrace tailWord_7608848 prefixEnd_7608848 3906996251001351580907551 := by
  unfold tailWord_7608848
  simp only [CollatzResearch.WordTrace]
  refine ⟨138758742769225329313001599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185011657025633772417335465 138758742769225329313001599)
  ·
    refine ⟨208138114153837993969502399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138758742769225329313001599 208138114153837993969502399)
    ·
      refine ⟨312207171230756990954253599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208138114153837993969502399 312207171230756990954253599)
      ·
        refine ⟨468310756846135486431380399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312207171230756990954253599 468310756846135486431380399)
        ·
          refine ⟨702466135269203229647070599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468310756846135486431380399 702466135269203229647070599)
          ·
            refine ⟨1053699202903804844470605899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702466135269203229647070599 1053699202903804844470605899)
            ·
              refine ⟨1580548804355707266705908849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053699202903804844470605899 1580548804355707266705908849)
              ·
                refine ⟨1185411603266780450029431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580548804355707266705908849 1185411603266780450029431637)
                ·
                  refine ⟨6945771112891291699391201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1185411603266780450029431637 6945771112891291699391201)
                  ·
                    refine ⟨5209328334668468774543401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945771112891291699391201 5209328334668468774543401)
                    ·
                      refine ⟨3906996251001351580907551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209328334668468774543401 3906996251001351580907551)
                      ·
                        rfl

theorem cell23_7608848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2].length) (baseStart_7608848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608848 prefixEnd_7608848 := by exact prefixLift 7608848
  have htrace : WordTrace (prefixWord ++ tailWord_7608848) baseStart_7608848 baseEnd_7608848 := by
    simpa [prefixWord, tailWord_7608848, baseEnd_7608848] using wordTrace_append hprefix tailTrace_7608848
  have hstable : (prefixWord ++ tailWord_7608848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608848).length < 2 ^ (prefixWord ++ tailWord_7608848).sum := by decide
  have hdescent : baseEnd_7608848 < baseStart_7608848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608882 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_7608882 : Nat := 118140960795 + 7608882 * 2 ^ 59
def prefixEnd_7608882 : Nat := 4983230072969 + 3 ^ 40 * 7608882 * 2
def baseEnd_7608882 : Nat := 3907013709343604447882395

theorem tailTrace_7608882 : CollatzResearch.WordTrace tailWord_7608882 prefixEnd_7608882 3907013709343604447882395 := by
  unfold tailWord_7608882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69379681405081870608185225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185012483746884988288493933 69379681405081870608185225)
  ·
    refine ⟨52034761053811402956138919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69379681405081870608185225 52034761053811402956138919)
    ·
      refine ⟨78052141580717104434208379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52034761053811402956138919 78052141580717104434208379)
      ·
        refine ⟨117078212371075656651312569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78052141580717104434208379 117078212371075656651312569)
        ·
          refine ⟨87808659278306742488484427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117078212371075656651312569 87808659278306742488484427)
          ·
            refine ⟨131712988917460113732726641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87808659278306742488484427 131712988917460113732726641)
            ·
              refine ⟨98784741688095085299544981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131712988917460113732726641 98784741688095085299544981)
              ·
                refine ⟨4630534766629457123416171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98784741688095085299544981 4630534766629457123416171)
                ·
                  refine ⟨6945802149944185685124257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630534766629457123416171 6945802149944185685124257)
                  ·
                    refine ⟨5209351612458139263843193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945802149944185685124257 5209351612458139263843193)
                    ·
                      refine ⟨3907013709343604447882395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209351612458139263843193 3907013709343604447882395)
                      ·
                        rfl

theorem cell23_7608882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_7608882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608882 prefixEnd_7608882 := by exact prefixLift 7608882
  have htrace : WordTrace (prefixWord ++ tailWord_7608882) baseStart_7608882 baseEnd_7608882 := by
    simpa [prefixWord, tailWord_7608882, baseEnd_7608882] using wordTrace_append hprefix tailTrace_7608882
  have hstable : (prefixWord ++ tailWord_7608882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608882).length < 2 ^ (prefixWord ++ tailWord_7608882).sum := by decide
  have hdescent : baseEnd_7608882 < baseStart_7608882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608892 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_7608892 : Nat := 118140960795 + 7608892 * 2 ^ 59
def prefixEnd_7608892 : Nat := 4983230072969 + 3 ^ 40 * 7608892 * 2
def baseEnd_7608892 : Nat := 1302339614716716469585783

theorem tailTrace_7608892 : CollatzResearch.WordTrace tailWord_7608892 prefixEnd_7608892 1302339614716716469585783 := by
  unfold tailWord_7608892
  simp only [CollatzResearch.WordTrace]
  refine ⟨138759545175145627070302465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185012726900194169427069953 138759545175145627070302465)
  ·
    refine ⟨104069658881359220302726849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138759545175145627070302465 104069658881359220302726849)
    ·
      refine ⟨78052244161019415227045137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104069658881359220302726849 78052244161019415227045137)
      ·
        refine ⟨58539183120764561420283853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78052244161019415227045137 58539183120764561420283853)
        ·
          refine ⟨21952193670286710532606445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58539183120764561420283853 21952193670286710532606445)
          ·
            refine ⟨8232072626357516449727417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21952193670286710532606445 8232072626357516449727417)
            ·
              refine ⟨6174054469768137337295563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232072626357516449727417 6174054469768137337295563)
              ·
                refine ⟨9261081704652206005943345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174054469768137337295563 9261081704652206005943345)
                ·
                  refine ⟨6945811278489154504457509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261081704652206005943345 6945811278489154504457509)
                  ·
                    refine ⟨1302339614716716469585783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945811278489154504457509 1302339614716716469585783)
                    ·
                      rfl

theorem cell23_7608892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_7608892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608892 prefixEnd_7608892 := by exact prefixLift 7608892
  have htrace : WordTrace (prefixWord ++ tailWord_7608892) baseStart_7608892 baseEnd_7608892 := by
    simpa [prefixWord, tailWord_7608892, baseEnd_7608892] using wordTrace_append hprefix tailTrace_7608892
  have hstable : (prefixWord ++ tailWord_7608892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608892).length < 2 ^ (prefixWord ++ tailWord_7608892).sum := by decide
  have hdescent : baseEnd_7608892 < baseStart_7608892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608902 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7608902 : Nat := 118140960795 + 7608902 * 2 ^ 59
def prefixEnd_7608902 : Nat := 4983230072969 + 3 ^ 40 * 7608902 * 2
def baseEnd_7608902 : Nat := 3907023978956694369632303

theorem tailTrace_7608902 : CollatzResearch.WordTrace tailWord_7608902 prefixEnd_7608902 3907023978956694369632303 := by
  unfold tailWord_7608902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672482971257969557764655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185012970053503350565645973 8672482971257969557764655)
  ·
    refine ⟨13008724456886954336646983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8672482971257969557764655 13008724456886954336646983)
    ·
      refine ⟨19513086685330431504970475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13008724456886954336646983 19513086685330431504970475)
      ·
        refine ⟨29269630027995647257455713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19513086685330431504970475 29269630027995647257455713)
        ·
          refine ⟨21952222520996735443091785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29269630027995647257455713 21952222520996735443091785)
          ·
            refine ⟨16464166890747551582318839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21952222520996735443091785 16464166890747551582318839)
            ·
              refine ⟨24696250336121327373478259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464166890747551582318839 24696250336121327373478259)
              ·
                refine ⟨37044375504181991060217389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24696250336121327373478259 37044375504181991060217389)
                ·
                  refine ⟨13891640814068246647581521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37044375504181991060217389 13891640814068246647581521)
                  ·
                    refine ⟨10418730610551184985686141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13891640814068246647581521 10418730610551184985686141)
                    ·
                      refine ⟨3907023978956694369632303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418730610551184985686141 3907023978956694369632303)
                      ·
                        rfl

theorem cell23_7608902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7608902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608902 prefixEnd_7608902 := by exact prefixLift 7608902
  have htrace : WordTrace (prefixWord ++ tailWord_7608902) baseStart_7608902 baseEnd_7608902 := by
    simpa [prefixWord, tailWord_7608902, baseEnd_7608902] using wordTrace_append hprefix tailTrace_7608902
  have hstable : (prefixWord ++ tailWord_7608902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608902).length < 2 ^ (prefixWord ++ tailWord_7608902).sum := by decide
  have hdescent : baseEnd_7608902 < baseStart_7608902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608926 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7608926 : Nat := 118140960795 + 7608926 * 2 ^ 59
def prefixEnd_7608926 : Nat := 4983230072969 + 3 ^ 40 * 7608926 * 2
def baseEnd_7608926 : Nat := 1302345434164134091910731

theorem tailTrace_7608926 : CollatzResearch.WordTrace tailWord_7608926 prefixEnd_7608926 1302345434164134091910731 := by
  unfold tailWord_7608926
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690041304021009743417829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185013553621445385298228421 34690041304021009743417829)
  ·
    refine ⟨6504382744503939326890843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34690041304021009743417829 6504382744503939326890843)
    ·
      refine ⟨9756574116755908990336265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504382744503939326890843 9756574116755908990336265)
      ·
        refine ⟨7317430587566931742752199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9756574116755908990336265 7317430587566931742752199)
        ·
          refine ⟨10976145881350397614128299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317430587566931742752199 10976145881350397614128299)
          ·
            refine ⟨16464218822025596421192449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976145881350397614128299 16464218822025596421192449)
            ·
              refine ⟨12348164116519197315894337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16464218822025596421192449 12348164116519197315894337)
              ·
                refine ⟨9261123087389397986920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12348164116519197315894337 9261123087389397986920753)
                ·
                  refine ⟨6945842315542048490190565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261123087389397986920753 6945842315542048490190565)
                  ·
                    refine ⟨1302345434164134091910731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945842315542048490190565 1302345434164134091910731)
                    ·
                      rfl

theorem cell23_7608926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7608926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608926 prefixEnd_7608926 := by exact prefixLift 7608926
  have htrace : WordTrace (prefixWord ++ tailWord_7608926) baseStart_7608926 baseEnd_7608926 := by
    simpa [prefixWord, tailWord_7608926, baseEnd_7608926] using wordTrace_append hprefix tailTrace_7608926
  have hstable : (prefixWord ++ tailWord_7608926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608926).length < 2 ^ (prefixWord ++ tailWord_7608926).sum := by decide
  have hdescent : baseEnd_7608926 < baseStart_7608926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608931 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 6]
def baseStart_7608931 : Nat := 118140960795 + 7608931 * 2 ^ 59
def prefixEnd_7608931 : Nat := 4983230072969 + 3 ^ 40 * 7608931 * 2
def baseEnd_7608931 : Nat := 1302346289965224918723223

theorem tailTrace_7608931 : CollatzResearch.WordTrace tailWord_7608931 prefixEnd_7608931 1302346289965224918723223 := by
  unfold tailWord_7608931
  simp only [CollatzResearch.WordTrace]
  refine ⟨277520512797149963801274647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185013675198099975867516431 277520512797149963801274647)
  ·
    refine ⟨416280769195724945701911971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277520512797149963801274647 416280769195724945701911971)
    ·
      refine ⟨624421153793587418552867957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416280769195724945701911971 624421153793587418552867957)
      ·
        refine ⟨58539483168148820489331371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624421153793587418552867957 58539483168148820489331371)
        ·
          refine ⟨87809224752223230733997057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58539483168148820489331371 87809224752223230733997057)
          ·
            refine ⟨65856918564167423050497793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87809224752223230733997057 65856918564167423050497793)
            ·
              refine ⟨49392688923125567287873345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65856918564167423050497793 49392688923125567287873345)
              ·
                refine ⟨37044516692344175465905009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49392688923125567287873345 37044516692344175465905009)
                ·
                  refine ⟨27783387519258131599428757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37044516692344175465905009 27783387519258131599428757)
                  ·
                    refine ⟨1302346289965224918723223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27783387519258131599428757 1302346289965224918723223)
                    ·
                      rfl

theorem cell23_7608931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_7608931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608931 prefixEnd_7608931 := by exact prefixLift 7608931
  have htrace : WordTrace (prefixWord ++ tailWord_7608931) baseStart_7608931 baseEnd_7608931 := by
    simpa [prefixWord, tailWord_7608931, baseEnd_7608931] using wordTrace_append hprefix tailTrace_7608931
  have hstable : (prefixWord ++ tailWord_7608931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608931).length < 2 ^ (prefixWord ++ tailWord_7608931).sum := by decide
  have hdescent : baseEnd_7608931 < baseStart_7608931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608933 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 1, 2, 2]
def baseStart_7608933 : Nat := 118140960795 + 7608933 * 2 ^ 59
def prefixEnd_7608933 : Nat := 4983230072969 + 3 ^ 40 * 7608933 * 2
def baseEnd_7608933 : Nat := 3907039896856983748344661

theorem tailTrace_7608933 : CollatzResearch.WordTrace tailWord_7608933 prefixEnd_7608933 3907039896856983748344661 := by
  unfold tailWord_7608933
  simp only [CollatzResearch.WordTrace]
  refine ⟨277520585743142718142847453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185013723828761812095231635 277520585743142718142847453)
  ·
    refine ⟨104070219653678519303567795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277520585743142718142847453 104070219653678519303567795)
    ·
      refine ⟨156105329480517778955351693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104070219653678519303567795 156105329480517778955351693)
      ·
        refine ⟨58539498555194167108256885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156105329480517778955351693 58539498555194167108256885)
        ·
          refine ⟨5488077989549453166399083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58539498555194167108256885 5488077989549453166399083)
          ·
            refine ⟨8232116984324179749598625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488077989549453166399083 8232116984324179749598625)
            ·
              refine ⟨6174087738243134812198969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232116984324179749598625 6174087738243134812198969)
              ·
                refine ⟨4630565803682351109149227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174087738243134812198969 4630565803682351109149227)
                ·
                  refine ⟨6945848705523526663723841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630565803682351109149227 6945848705523526663723841)
                  ·
                    refine ⟨5209386529142644997792881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6945848705523526663723841 5209386529142644997792881)
                    ·
                      refine ⟨3907039896856983748344661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209386529142644997792881 3907039896856983748344661)
                      ·
                        rfl

theorem cell23_7608933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_7608933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608933 prefixEnd_7608933 := by exact prefixLift 7608933
  have htrace : WordTrace (prefixWord ++ tailWord_7608933) baseStart_7608933 baseEnd_7608933 := by
    simpa [prefixWord, tailWord_7608933, baseEnd_7608933] using wordTrace_append hprefix tailTrace_7608933
  have hstable : (prefixWord ++ tailWord_7608933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608933).length < 2 ^ (prefixWord ++ tailWord_7608933).sum := by decide
  have hdescent : baseEnd_7608933 < baseStart_7608933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7608951 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_7608951 : Nat := 118140960795 + 7608951 * 2 ^ 59
def prefixEnd_7608951 : Nat := 4983230072969 + 3 ^ 40 * 7608951 * 2
def baseEnd_7608951 : Nat := 3907049139508764677919577

theorem tailTrace_7608951 : CollatzResearch.WordTrace tailWord_7608951 prefixEnd_7608951 3907049139508764677919577 := by
  unfold tailWord_7608951
  simp only [CollatzResearch.WordTrace]
  refine ⟨277521242257077507217002707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185014161504718338144668471 277521242257077507217002707)
  ·
    refine ⟨416281863385616260825504061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277521242257077507217002707 416281863385616260825504061)
    ·
      refine ⟨156105698769606097809564023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416281863385616260825504061 156105698769606097809564023)
      ·
        refine ⟨234158548154409146714346035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156105698769606097809564023 234158548154409146714346035)
        ·
          refine ⟨351237822231613720071519053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234158548154409146714346035 351237822231613720071519053)
          ·
            refine ⟨131714183336855145026819645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351237822231613720071519053 131714183336855145026819645)
            ·
              refine ⟨49392818751320679385057367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131714183336855145026819645 49392818751320679385057367)
              ·
                refine ⟨74089228126981019077586051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49392818751320679385057367 74089228126981019077586051)
                ·
                  refine ⟨111133842190471528616379077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74089228126981019077586051 111133842190471528616379077)
                  ·
                    refine ⟨20837595410713411615571077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111133842190471528616379077 20837595410713411615571077)
                    ·
                      refine ⟨3907049139508764677919577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20837595410713411615571077 3907049139508764677919577)
                      ·
                        rfl

theorem cell23_7608951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_7608951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7608951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7608951 prefixEnd_7608951 := by exact prefixLift 7608951
  have htrace : WordTrace (prefixWord ++ tailWord_7608951) baseStart_7608951 baseEnd_7608951 := by
    simpa [prefixWord, tailWord_7608951, baseEnd_7608951] using wordTrace_append hprefix tailTrace_7608951
  have hstable : (prefixWord ++ tailWord_7608951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7608951).length < 2 ^ (prefixWord ++ tailWord_7608951).sum := by decide
  have hdescent : baseEnd_7608951 < baseStart_7608951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7608951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609005 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_7609005 : Nat := 118140960795 + 7609005 * 2 ^ 59
def prefixEnd_7609005 : Nat := 4983230072969 + 3 ^ 40 * 7609005 * 2
def baseEnd_7609005 : Nat := 3907076867464107466644329

theorem tailTrace_7609005 : CollatzResearch.WordTrace tailWord_7609005 prefixEnd_7609005 3907076867464107466644329 := by
  unfold tailWord_7609005
  simp only [CollatzResearch.WordTrace]
  refine ⟨277523211798881874439468469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185015474532587916292978979 277523211798881874439468469)
  ·
    refine ⟨26017801106145175728700169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277523211798881874439468469 26017801106145175728700169)
    ·
      refine ⟨19513350829608881796525127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26017801106145175728700169 19513350829608881796525127)
      ·
        refine ⟨29270026244413322694787691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19513350829608881796525127 29270026244413322694787691)
        ·
          refine ⟨43905039366619984042181537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29270026244413322694787691 43905039366619984042181537)
          ·
            refine ⟨32928779524964988031636153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43905039366619984042181537 32928779524964988031636153)
            ·
              refine ⟨24696584643723741023727115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32928779524964988031636153 24696584643723741023727115)
              ·
                refine ⟨37044876965585611535590673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24696584643723741023727115 37044876965585611535590673)
                ·
                  refine ⟨27783657724189208651693005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37044876965585611535590673 27783657724189208651693005)
                  ·
                    refine ⟨10418871646570953244384877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27783657724189208651693005 10418871646570953244384877)
                    ·
                      refine ⟨3907076867464107466644329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10418871646570953244384877 3907076867464107466644329)
                      ·
                        rfl

theorem cell23_7609005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_7609005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609005 prefixEnd_7609005 := by exact prefixLift 7609005
  have htrace : WordTrace (prefixWord ++ tailWord_7609005) baseStart_7609005 baseEnd_7609005 := by
    simpa [prefixWord, tailWord_7609005, baseEnd_7609005] using wordTrace_append hprefix tailTrace_7609005
  have hstable : (prefixWord ++ tailWord_7609005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609005).length < 2 ^ (prefixWord ++ tailWord_7609005).sum := by decide
  have hdescent : baseEnd_7609005 < baseStart_7609005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609055 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 3, 4]
def baseStart_7609055 : Nat := 118140960795 + 7609055 * 2 ^ 59
def prefixEnd_7609055 : Nat := 4983230072969 + 3 ^ 40 * 7609055 * 2
def baseEnd_7609055 : Nat := 1302367513832277423673033

theorem tailTrace_7609055 : CollatzResearch.WordTrace tailWord_7609055 prefixEnd_7609055 1302367513832277423673033 := by
  unfold tailWord_7609055
  simp only [CollatzResearch.WordTrace]
  refine ⟨277525035448700732978788619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185016690299133821985859079 277525035448700732978788619)
  ·
    refine ⟨416287553173051099468182929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277525035448700732978788619 416287553173051099468182929)
    ·
      refine ⟨312215664879788324601137197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416287553173051099468182929 312215664879788324601137197)
      ·
        refine ⟨117080874329920621725426449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312215664879788324601137197 117080874329920621725426449)
        ·
          refine ⟨87810655747440466294069837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117080874329920621725426449 87810655747440466294069837)
          ·
            refine ⟨32928995905290174860276189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87810655747440466294069837 32928995905290174860276189)
            ·
              refine ⟨12348373464483815572603571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32928995905290174860276189 12348373464483815572603571)
              ·
                refine ⟨18522560196725723358905357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12348373464483815572603571 18522560196725723358905357)
                ·
                  refine ⟨6945960073772146259589509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18522560196725723358905357 6945960073772146259589509)
                  ·
                    refine ⟨1302367513832277423673033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6945960073772146259589509 1302367513832277423673033)
                    ·
                      rfl

theorem cell23_7609055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_7609055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609055 prefixEnd_7609055 := by exact prefixLift 7609055
  have htrace : WordTrace (prefixWord ++ tailWord_7609055) baseStart_7609055 baseEnd_7609055 := by
    simpa [prefixWord, tailWord_7609055, baseEnd_7609055] using wordTrace_append hprefix tailTrace_7609055
  have hstable : (prefixWord ++ tailWord_7609055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609055).length < 2 ^ (prefixWord ++ tailWord_7609055).sum := by decide
  have hdescent : baseEnd_7609055 < baseStart_7609055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609106 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7609106 : Nat := 118140960795 + 7609106 * 2 ^ 59
def prefixEnd_7609106 : Nat := 4983230072969 + 3 ^ 40 * 7609106 * 2
def baseEnd_7609106 : Nat := 1302376243003403857160455

theorem tailTrace_7609106 : CollatzResearch.WordTrace tailWord_7609106 prefixEnd_7609106 1302376243003403857160455 := by
  unfold tailWord_7609106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69381723892878992172223793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185017930381010645792596781 69381723892878992172223793)
  ·
    refine ⟨52036292919659244129167845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69381723892878992172223793 52036292919659244129167845)
    ·
      refine ⟨9756804922436108274218971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52036292919659244129167845 9756804922436108274218971)
      ·
        refine ⟨14635207383654162411328457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756804922436108274218971 14635207383654162411328457)
        ·
          refine ⟨10976405537740621808496343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14635207383654162411328457 10976405537740621808496343)
          ·
            refine ⟨16464608306610932712744515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976405537740621808496343 16464608306610932712744515)
            ·
              refine ⟨24696912459916399069116773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464608306610932712744515 24696912459916399069116773)
              ·
                refine ⟨4630671086234324825459395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24696912459916399069116773 4630671086234324825459395)
                ·
                  refine ⟨6946006629351487238189093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630671086234324825459395 6946006629351487238189093)
                  ·
                    refine ⟨1302376243003403857160455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946006629351487238189093 1302376243003403857160455)
                    ·
                      rfl

theorem cell23_7609106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7609106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609106 prefixEnd_7609106 := by exact prefixLift 7609106
  have htrace : WordTrace (prefixWord ++ tailWord_7609106) baseStart_7609106 baseEnd_7609106 := by
    simpa [prefixWord, tailWord_7609106, baseEnd_7609106] using wordTrace_append hprefix tailTrace_7609106
  have hstable : (prefixWord ++ tailWord_7609106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609106).length < 2 ^ (prefixWord ++ tailWord_7609106).sum := by decide
  have hdescent : baseEnd_7609106 < baseStart_7609106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609133 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7609133 : Nat := 118140960795 + 7609133 * 2 ^ 59
def prefixEnd_7609133 : Nat := 4983230072969 + 3 ^ 40 * 7609133 * 2
def baseEnd_7609133 : Nat := 3907142592987882965843741

theorem tailTrace_7609133 : CollatzResearch.WordTrace tailWord_7609133 prefixEnd_7609133 3907142592987882965843741 := by
  unfold tailWord_7609133
  simp only [CollatzResearch.WordTrace]
  refine ⟨277527880342418152300128053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185018586894945434866752035 277527880342418152300128053)
  ·
    refine ⟨26018238782101701778137005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277527880342418152300128053 26018238782101701778137005)
    ·
      refine ⟨9756839543288138166801377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26018238782101701778137005 9756839543288138166801377)
      ·
        refine ⟨7317629657466103625101033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9756839543288138166801377 7317629657466103625101033)
        ·
          refine ⟨5488222243099577718825775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7317629657466103625101033 5488222243099577718825775)
          ·
            refine ⟨8232333364649366578238663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488222243099577718825775 8232333364649366578238663)
            ·
              refine ⟨12348500046974049867357995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232333364649366578238663 12348500046974049867357995)
              ·
                refine ⟨18522750070461074801036993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12348500046974049867357995 18522750070461074801036993)
                ·
                  refine ⟨13892062552845806100777745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18522750070461074801036993 13892062552845806100777745)
                  ·
                    refine ⟨10419046914634354575583309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13892062552845806100777745 10419046914634354575583309)
                    ·
                      refine ⟨3907142592987882965843741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419046914634354575583309 3907142592987882965843741)
                      ·
                        rfl

theorem cell23_7609133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7609133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609133 prefixEnd_7609133 := by exact prefixLift 7609133
  have htrace : WordTrace (prefixWord ++ tailWord_7609133) baseStart_7609133 baseEnd_7609133 := by
    simpa [prefixWord, tailWord_7609133, baseEnd_7609133] using wordTrace_append hprefix tailTrace_7609133
  have hstable : (prefixWord ++ tailWord_7609133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609133).length < 2 ^ (prefixWord ++ tailWord_7609133).sum := by decide
  have hdescent : baseEnd_7609133 < baseStart_7609133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609139 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 2, 3, 2]
def baseStart_7609139 : Nat := 118140960795 + 7609139 * 2 ^ 59
def prefixEnd_7609139 : Nat := 4983230072969 + 3 ^ 40 * 7609139 * 2
def baseEnd_7609139 : Nat := 3907145673871809942368713

theorem tailTrace_7609139 : CollatzResearch.WordTrace tailWord_7609139 prefixEnd_7609139 3907145673871809942368713 := by
  unfold tailWord_7609139
  simp only [CollatzResearch.WordTrace]
  refine ⟨277528099180396415324846471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185018732786930943549897647 277528099180396415324846471)
  ·
    refine ⟨416292148770594622987269707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277528099180396415324846471 416292148770594622987269707)
    ·
      refine ⟨624438223155891934480904561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416292148770594622987269707 624438223155891934480904561)
      ·
        refine ⟨468328667366918950860678421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624438223155891934480904561 468328667366918950860678421)
        ·
          refine ⟨21952906282824325821594301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 468328667366918950860678421 21952906282824325821594301)
          ·
            refine ⟨8232339856059122183097863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21952906282824325821594301 8232339856059122183097863)
            ·
              refine ⟨12348509784088683274646795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232339856059122183097863 12348509784088683274646795)
              ·
                refine ⟨18522764676133024911970193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12348509784088683274646795 18522764676133024911970193)
                ·
                  refine ⟨13892073507099768683977645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18522764676133024911970193 13892073507099768683977645)
                  ·
                    refine ⟨5209527565162413256491617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13892073507099768683977645 5209527565162413256491617)
                    ·
                      refine ⟨3907145673871809942368713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209527565162413256491617 3907145673871809942368713)
                      ·
                        rfl

theorem cell23_7609139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3, 2].length) (baseStart_7609139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609139 prefixEnd_7609139 := by exact prefixLift 7609139
  have htrace : WordTrace (prefixWord ++ tailWord_7609139) baseStart_7609139 baseEnd_7609139 := by
    simpa [prefixWord, tailWord_7609139, baseEnd_7609139] using wordTrace_append hprefix tailTrace_7609139
  have hstable : (prefixWord ++ tailWord_7609139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609139).length < 2 ^ (prefixWord ++ tailWord_7609139).sum := by decide
  have hdescent : baseEnd_7609139 < baseStart_7609139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609146 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_7609146 : Nat := 118140960795 + 7609146 * 2 ^ 59
def prefixEnd_7609146 : Nat := 4983230072969 + 3 ^ 40 * 7609146 * 2
def baseEnd_7609146 : Nat := 3907149268236391414981181

theorem tailTrace_7609146 : CollatzResearch.WordTrace tailWord_7609146 prefixEnd_7609146 3907149268236391414981181 := by
  unfold tailWord_7609146
  simp only [CollatzResearch.WordTrace]
  refine ⟨69382088622842763880087823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185018902994247370346900861 69382088622842763880087823)
  ·
    refine ⟨104073132934264145820131735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69382088622842763880087823 104073132934264145820131735)
    ·
      refine ⟨156109699401396218730197603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104073132934264145820131735 156109699401396218730197603)
      ·
        refine ⟨234164549102094328095296405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156109699401396218730197603 234164549102094328095296405)
        ·
          refine ⟨10976463239160671629467019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234164549102094328095296405 10976463239160671629467019)
          ·
            refine ⟨16464694858741007444200529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976463239160671629467019 16464694858741007444200529)
            ·
              refine ⟨12348521144055755583150397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16464694858741007444200529 12348521144055755583150397)
              ·
                refine ⟨4630695429020908343681399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12348521144055755583150397 4630695429020908343681399)
                ·
                  refine ⟨6946043143531362515522099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630695429020908343681399 6946043143531362515522099)
                  ·
                    refine ⟨10419064715297043773283149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946043143531362515522099 10419064715297043773283149)
                    ·
                      refine ⟨3907149268236391414981181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419064715297043773283149 3907149268236391414981181)
                      ·
                        rfl

theorem cell23_7609146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_7609146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609146 prefixEnd_7609146 := by exact prefixLift 7609146
  have htrace : WordTrace (prefixWord ++ tailWord_7609146) baseStart_7609146 baseEnd_7609146 := by
    simpa [prefixWord, tailWord_7609146, baseEnd_7609146] using wordTrace_append hprefix tailTrace_7609146
  have hstable : (prefixWord ++ tailWord_7609146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609146).length < 2 ^ (prefixWord ++ tailWord_7609146).sum := by decide
  have hdescent : baseEnd_7609146 < baseStart_7609146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609148 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7609148 : Nat := 118140960795 + 7609148 * 2 ^ 59
def prefixEnd_7609148 : Nat := 4983230072969 + 3 ^ 40 * 7609148 * 2
def baseEnd_7609148 : Nat := 3907150295197700407156171

theorem tailTrace_7609148 : CollatzResearch.WordTrace tailWord_7609148 prefixEnd_7609148 3907150295197700407156171 := by
  unfold tailWord_7609148
  simp only [CollatzResearch.WordTrace]
  refine ⟨138764213718681904930962049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185018951624909206574616065 138764213718681904930962049)
  ·
    refine ⟨104073160289011428698221537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138764213718681904930962049 104073160289011428698221537)
    ·
      refine ⟨78054870216758571523666153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104073160289011428698221537 78054870216758571523666153)
      ·
        refine ⟨58541152662568928642749615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78054870216758571523666153 58541152662568928642749615)
        ·
          refine ⟨87811728993853392964124423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58541152662568928642749615 87811728993853392964124423)
          ·
            refine ⟨131717593490780089446186635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87811728993853392964124423 131717593490780089446186635)
            ·
              refine ⟨197576390236170134169279953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131717593490780089446186635 197576390236170134169279953)
              ·
                refine ⟨148182292677127600626959965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197576390236170134169279953 148182292677127600626959965)
                ·
                  refine ⟨55568359753922850235109987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148182292677127600626959965 55568359753922850235109987)
                  ·
                    refine ⟨83352539630884275352664981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55568359753922850235109987 83352539630884275352664981)
                    ·
                      refine ⟨3907150295197700407156171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83352539630884275352664981 3907150295197700407156171)
                      ·
                        rfl

theorem cell23_7609148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7609148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609148 prefixEnd_7609148 := by exact prefixLift 7609148
  have htrace : WordTrace (prefixWord ++ tailWord_7609148) baseStart_7609148 baseEnd_7609148 := by
    simpa [prefixWord, tailWord_7609148, baseEnd_7609148] using wordTrace_append hprefix tailTrace_7609148
  have hstable : (prefixWord ++ tailWord_7609148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609148).length < 2 ^ (prefixWord ++ tailWord_7609148).sum := by decide
  have hdescent : baseEnd_7609148 < baseStart_7609148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609172 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_7609172 : Nat := 118140960795 + 7609172 * 2 ^ 59
def prefixEnd_7609172 : Nat := 4983230072969 + 3 ^ 40 * 7609172 * 2
def baseEnd_7609172 : Nat := 3907162618733408313256061

theorem tailTrace_7609172 : CollatzResearch.WordTrace tailWord_7609172 prefixEnd_7609172 3907162618733408313256061 := by
  unfold tailWord_7609172
  simp only [CollatzResearch.WordTrace]
  refine ⟨138764651394638430980398885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185019535192851241307198513 138764651394638430980398885)
  ·
    refine ⟨26018372136494705808824791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138764651394638430980398885 26018372136494705808824791)
    ·
      refine ⟨39027558204742058713237187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26018372136494705808824791 39027558204742058713237187)
      ·
        refine ⟨58541337307113088069855781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39027558204742058713237187 58541337307113088069855781)
        ·
          refine ⟨10976500745083704013097959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58541337307113088069855781 10976500745083704013097959)
          ·
            refine ⟨16464751117625556019646939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976500745083704013097959 16464751117625556019646939)
            ·
              refine ⟨24697126676438334029470409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16464751117625556019646939 24697126676438334029470409)
              ·
                refine ⟨18522845007328750522102807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24697126676438334029470409 18522845007328750522102807)
                ·
                  refine ⟨27784267510993125783154211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18522845007328750522102807 27784267510993125783154211)
                  ·
                    refine ⟨41676401266489688674731317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27784267510993125783154211 41676401266489688674731317)
                    ·
                      refine ⟨3907162618733408313256061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41676401266489688674731317 3907162618733408313256061)
                      ·
                        rfl

theorem cell23_7609172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_7609172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609172 prefixEnd_7609172 := by exact prefixLift 7609172
  have htrace : WordTrace (prefixWord ++ tailWord_7609172) baseStart_7609172 baseEnd_7609172 := by
    simpa [prefixWord, tailWord_7609172, baseEnd_7609172] using wordTrace_append hprefix tailTrace_7609172
  have hstable : (prefixWord ++ tailWord_7609172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609172).length < 2 ^ (prefixWord ++ tailWord_7609172).sum := by decide
  have hdescent : baseEnd_7609172 < baseStart_7609172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609185 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_7609185 : Nat := 118140960795 + 7609185 * 2 ^ 59
def prefixEnd_7609185 : Nat := 4983230072969 + 3 ^ 40 * 7609185 * 2
def baseEnd_7609185 : Nat := 3907169293981916762393501

theorem tailTrace_7609185 : CollatzResearch.WordTrace tailWord_7609185 prefixEnd_7609185 3907169293981916762393501 := by
  unfold tailWord_7609185
  simp only [CollatzResearch.WordTrace]
  refine ⟨277529776938229765181021009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185019851292153176787347339 277529776938229765181021009)
  ·
    refine ⟨208147332703672323885765757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277529776938229765181021009 208147332703672323885765757)
    ·
      refine ⟨78055249763877121457162159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208147332703672323885765757 78055249763877121457162159)
      ·
        refine ⟨117082874645815682185743239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78055249763877121457162159 117082874645815682185743239)
        ·
          refine ⟨175624311968723523278614859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117082874645815682185743239 175624311968723523278614859)
          ·
            refine ⟨263436467953085284917922289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175624311968723523278614859 263436467953085284917922289)
            ·
              refine ⟨197577350964813963688441717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263436467953085284917922289 197577350964813963688441717)
              ·
                refine ⟨18522876652951309095791411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197577350964813963688441717 18522876652951309095791411)
                ·
                  refine ⟨27784314979426963643687117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18522876652951309095791411 27784314979426963643687117)
                  ·
                    refine ⟨10419118117285111366382669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27784314979426963643687117 10419118117285111366382669)
                    ·
                      refine ⟨3907169293981916762393501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419118117285111366382669 3907169293981916762393501)
                      ·
                        rfl

theorem cell23_7609185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_7609185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609185 prefixEnd_7609185 := by exact prefixLift 7609185
  have htrace : WordTrace (prefixWord ++ tailWord_7609185) baseStart_7609185 baseEnd_7609185 := by
    simpa [prefixWord, tailWord_7609185, baseEnd_7609185] using wordTrace_append hprefix tailTrace_7609185
  have hstable : (prefixWord ++ tailWord_7609185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609185).length < 2 ^ (prefixWord ++ tailWord_7609185).sum := by decide
  have hdescent : baseEnd_7609185 < baseStart_7609185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609192 : List Nat := [2, 1, 4, 2, 1, 4, 2, 7]
def baseStart_7609192 : Nat := 118140960795 + 7609192 * 2 ^ 59
def prefixEnd_7609192 : Nat := 4983230072969 + 3 ^ 40 * 7609192 * 2
def baseEnd_7609192 : Nat := 144710106975796230926147

theorem tailTrace_7609192 : CollatzResearch.WordTrace tailWord_7609192 prefixEnd_7609192 144710106975796230926147 := by
  unfold tailWord_7609192
  simp only [CollatzResearch.WordTrace]
  refine ⟨138765016124602202688262915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185020021499469603584350553 138765016124602202688262915)
  ·
    refine ⟨208147524186903304032394373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138765016124602202688262915 208147524186903304032394373)
    ·
      refine ⟨39027660785044369506073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208147524186903304032394373 39027660785044369506073945)
      ·
        refine ⟨29270745588783277129555459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39027660785044369506073945 29270745588783277129555459)
        ·
          refine ⟨43906118383174915694333189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29270745588783277129555459 43906118383174915694333189)
          ·
            refine ⟨8232397196845296692687473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43906118383174915694333189 8232397196845296692687473)
            ·
              refine ⟨6174297897633972519515605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232397196845296692687473 6174297897633972519515605)
              ·
                refine ⟨144710106975796230926147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6174297897633972519515605 144710106975796230926147)
                ·
                  rfl

theorem cell23_7609192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 7].length) (baseStart_7609192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609192 prefixEnd_7609192 := by exact prefixLift 7609192
  have htrace : WordTrace (prefixWord ++ tailWord_7609192) baseStart_7609192 baseEnd_7609192 := by
    simpa [prefixWord, tailWord_7609192, baseEnd_7609192] using wordTrace_append hprefix tailTrace_7609192
  have hstable : (prefixWord ++ tailWord_7609192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609192).length < 2 ^ (prefixWord ++ tailWord_7609192).sum := by decide
  have hdescent : baseEnd_7609192 < baseStart_7609192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609202 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7609202 : Nat := 118140960795 + 7609202 * 2 ^ 59
def prefixEnd_7609202 : Nat := 4983230072969 + 3 ^ 40 * 7609202 * 2
def baseEnd_7609202 : Nat := 3907178023153043195880923

theorem tailTrace_7609202 : CollatzResearch.WordTrace tailWord_7609202 prefixEnd_7609202 3907178023153043195880923 := by
  unfold tailWord_7609202
  simp only [CollatzResearch.WordTrace]
  refine ⟨69382599244792044271097465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185020264652778784722926573 69382599244792044271097465)
  ·
    refine ⟨52036949433594033203323099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69382599244792044271097465 52036949433594033203323099)
    ·
      refine ⟨78055424150391049804984649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52036949433594033203323099 78055424150391049804984649)
      ·
        refine ⟨58541568112793287353738487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78055424150391049804984649 58541568112793287353738487)
        ·
          refine ⟨87812352169189931030607731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58541568112793287353738487 87812352169189931030607731)
          ·
            refine ⟨131718528253784896545911597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87812352169189931030607731 131718528253784896545911597)
            ·
              refine ⟨49394448095169336204716849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131718528253784896545911597 49394448095169336204716849)
              ·
                refine ⟨37045836071377002153537637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49394448095169336204716849 37045836071377002153537637)
                ·
                  refine ⟨6946094263383187903788307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37045836071377002153537637 6946094263383187903788307)
                  ·
                    refine ⟨10419141395074781855682461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946094263383187903788307 10419141395074781855682461)
                    ·
                      refine ⟨3907178023153043195880923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419141395074781855682461 3907178023153043195880923)
                      ·
                        rfl

theorem cell23_7609202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7609202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609202 prefixEnd_7609202 := by exact prefixLift 7609202
  have htrace : WordTrace (prefixWord ++ tailWord_7609202) baseStart_7609202 baseEnd_7609202 := by
    simpa [prefixWord, tailWord_7609202, baseEnd_7609202] using wordTrace_append hprefix tailTrace_7609202
  have hstable : (prefixWord ++ tailWord_7609202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609202).length < 2 ^ (prefixWord ++ tailWord_7609202).sum := by decide
  have hdescent : baseEnd_7609202 < baseStart_7609202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609245 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7609245 : Nat := 118140960795 + 7609245 * 2 ^ 59
def prefixEnd_7609245 : Nat := 4983230072969 + 3 ^ 40 * 7609245 * 2
def baseEnd_7609245 : Nat := 3907200102821186527643225

theorem tailTrace_7609245 : CollatzResearch.WordTrace tailWord_7609245 prefixEnd_7609245 3907200102821186527643225 := by
  unfold tailWord_7609245
  simp only [CollatzResearch.WordTrace]
  refine ⟨277531965318012395428205189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185021310212008263618803459 277531965318012395428205189)
  ·
    refine ⟨52037243497127324142788473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277531965318012395428205189 52037243497127324142788473)
    ·
      refine ⟨39027932622845493107091355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52037243497127324142788473 39027932622845493107091355)
      ·
        refine ⟨58541898934268239660637033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39027932622845493107091355 58541898934268239660637033)
        ·
          refine ⟨43906424200701179745477775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58541898934268239660637033 43906424200701179745477775)
          ·
            refine ⟨65859636301051769618216663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43906424200701179745477775 65859636301051769618216663)
            ·
              refine ⟨98789454451577654427324995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65859636301051769618216663 98789454451577654427324995)
              ·
                refine ⟨148184181677366481640987493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98789454451577654427324995 148184181677366481640987493)
                ·
                  refine ⟨27784534064506215307685155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148184181677366481640987493 27784534064506215307685155)
                  ·
                    refine ⟨41676801096759322961527733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27784534064506215307685155 41676801096759322961527733)
                    ·
                      refine ⟨3907200102821186527643225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41676801096759322961527733 3907200102821186527643225)
                      ·
                        rfl

theorem cell23_7609245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7609245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609245 prefixEnd_7609245 := by exact prefixLift 7609245
  have htrace : WordTrace (prefixWord ++ tailWord_7609245) baseStart_7609245 baseEnd_7609245 := by
    simpa [prefixWord, tailWord_7609245, baseEnd_7609245] using wordTrace_append hprefix tailTrace_7609245
  have hstable : (prefixWord ++ tailWord_7609245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609245).length < 2 ^ (prefixWord ++ tailWord_7609245).sum := by decide
  have hdescent : baseEnd_7609245 < baseStart_7609245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609292 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7609292 : Nat := 118140960795 + 7609292 * 2 ^ 59
def prefixEnd_7609292 : Nat := 4983230072969 + 3 ^ 40 * 7609292 * 2
def baseEnd_7609292 : Nat := 3907224236411947843755509

theorem tailTrace_7609292 : CollatzResearch.WordTrace tailWord_7609292 prefixEnd_7609292 3907224236411947843755509 := by
  unfold tailWord_7609292
  simp only [CollatzResearch.WordTrace]
  refine ⟨138766839774421061227583065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185022453032561414970110753 138766839774421061227583065)
  ·
    refine ⟨104075129830815795920687299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138766839774421061227583065 104075129830815795920687299)
    ·
      refine ⟨156112694746223693881030949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104075129830815795920687299 156112694746223693881030949)
      ·
        refine ⟨29271130264916942602693303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156112694746223693881030949 29271130264916942602693303)
        ·
          refine ⟨43906695397375413904039955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29271130264916942602693303 43906695397375413904039955)
          ·
            refine ⟨65860043096063120856059933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43906695397375413904039955 65860043096063120856059933)
            ·
              refine ⟨24697516161023670321022475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65860043096063120856059933 24697516161023670321022475)
              ·
                refine ⟨37046274241535505481533713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24697516161023670321022475 37046274241535505481533713)
                ·
                  refine ⟨27784705681151629111150285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37046274241535505481533713 27784705681151629111150285)
                  ·
                    refine ⟨10419264630431860916681357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27784705681151629111150285 10419264630431860916681357)
                    ·
                      refine ⟨3907224236411947843755509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419264630431860916681357 3907224236411947843755509)
                      ·
                        rfl

theorem cell23_7609292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7609292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609292 prefixEnd_7609292 := by exact prefixLift 7609292
  have htrace : WordTrace (prefixWord ++ tailWord_7609292) baseStart_7609292 baseEnd_7609292 := by
    simpa [prefixWord, tailWord_7609292, baseEnd_7609292] using wordTrace_append hprefix tailTrace_7609292
  have hstable : (prefixWord ++ tailWord_7609292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609292).length < 2 ^ (prefixWord ++ tailWord_7609292).sum := by decide
  have hdescent : baseEnd_7609292 < baseStart_7609292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609352 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_7609352 : Nat := 118140960795 + 7609352 * 2 ^ 59
def prefixEnd_7609352 : Nat := 4983230072969 + 3 ^ 40 * 7609352 * 2
def baseEnd_7609352 : Nat := 3907255045251217609005233

theorem tailTrace_7609352 : CollatzResearch.WordTrace tailWord_7609352 prefixEnd_7609352 3907255045251217609005233 := by
  unfold tailWord_7609352
  simp only [CollatzResearch.WordTrace]
  refine ⟨138767933964312376351175155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185023911952416501801566873 138767933964312376351175155)
  ·
    refine ⟨208151900946468564526762733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138767933964312376351175155 208151900946468564526762733)
    ·
      refine ⟨78056962854925711697536025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208151900946468564526762733 78056962854925711697536025)
      ·
        refine ⟨58542722141194283773152019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78056962854925711697536025 58542722141194283773152019)
        ·
          refine ⟨87814083211791425659728029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58542722141194283773152019 87814083211791425659728029)
          ·
            refine ⟨32930281204421784622398011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87814083211791425659728029 32930281204421784622398011)
            ·
              refine ⟨49395421806632676933597017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32930281204421784622398011 49395421806632676933597017)
              ·
                refine ⟨37046566354974507700197763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49395421806632676933597017 37046566354974507700197763)
                ·
                  refine ⟨55569849532461761550296645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37046566354974507700197763 55569849532461761550296645)
                  ·
                    refine ⟨10419346787336580290680621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55569849532461761550296645 10419346787336580290680621)
                    ·
                      refine ⟨3907255045251217609005233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419346787336580290680621 3907255045251217609005233)
                      ·
                        rfl

theorem cell23_7609352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_7609352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609352 prefixEnd_7609352 := by exact prefixLift 7609352
  have htrace : WordTrace (prefixWord ++ tailWord_7609352) baseStart_7609352 baseEnd_7609352 := by
    simpa [prefixWord, tailWord_7609352, baseEnd_7609352] using wordTrace_append hprefix tailTrace_7609352
  have hstable : (prefixWord ++ tailWord_7609352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609352).length < 2 ^ (prefixWord ++ tailWord_7609352).sum := by decide
  have hdescent : baseEnd_7609352 < baseStart_7609352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609386 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7609386 : Nat := 118140960795 + 7609386 * 2 ^ 59
def prefixEnd_7609386 : Nat := 4983230072969 + 3 ^ 40 * 7609386 * 2
def baseEnd_7609386 : Nat := 3907272503593470475980077

theorem tailTrace_7609386 : CollatzResearch.WordTrace tailWord_7609386 prefixEnd_7609386 3907272503593470475980077 := by
  unfold tailWord_7609386
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384277002625394127272003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185024738673667717672725341 69384277002625394127272003)
  ·
    refine ⟨104076415503938091190908005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69384277002625394127272003 104076415503938091190908005)
    ·
      refine ⟨19514327906988392098295251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104076415503938091190908005 19514327906988392098295251)
      ·
        refine ⟨29271491860482588147442877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19514327906988392098295251 29271491860482588147442877)
        ·
          refine ⟨10976809447680970555291079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29271491860482588147442877 10976809447680970555291079)
          ·
            refine ⟨16465214171521455832936619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10976809447680970555291079 16465214171521455832936619)
            ·
              refine ⟨24697821257282183749404929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16465214171521455832936619 24697821257282183749404929)
              ·
                refine ⟨18523365942961637812053697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24697821257282183749404929 18523365942961637812053697)
                ·
                  refine ⟨13892524457221228359040273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18523365942961637812053697 13892524457221228359040273)
                  ·
                    refine ⟨10419393342915921269280205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13892524457221228359040273 10419393342915921269280205)
                    ·
                      refine ⟨3907272503593470475980077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419393342915921269280205 3907272503593470475980077)
                      ·
                        rfl

theorem cell23_7609386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7609386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609386 prefixEnd_7609386 := by exact prefixLift 7609386
  have htrace : WordTrace (prefixWord ++ tailWord_7609386) baseStart_7609386 baseEnd_7609386 := by
    simpa [prefixWord, tailWord_7609386, baseEnd_7609386] using wordTrace_append hprefix tailTrace_7609386
  have hstable : (prefixWord ++ tailWord_7609386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609386).length < 2 ^ (prefixWord ++ tailWord_7609386).sum := by decide
  have hdescent : baseEnd_7609386 < baseStart_7609386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609395 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_7609395 : Nat := 118140960795 + 7609395 * 2 ^ 59
def prefixEnd_7609395 : Nat := 4983230072969 + 3 ^ 40 * 7609395 * 2
def baseEnd_7609395 : Nat := 3907277124919360940767535

theorem tailTrace_7609395 : CollatzResearch.WordTrace tailWord_7609395 prefixEnd_7609395 3907277124919360940767535 := by
  unfold tailWord_7609395
  simp only [CollatzResearch.WordTrace]
  refine ⟨277537436267468971046165639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185024957511645980697443759 277537436267468971046165639)
  ·
    refine ⟨416306154401203456569248459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277537436267468971046165639 416306154401203456569248459)
    ·
      refine ⟨624459231601805184853872689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416306154401203456569248459 624459231601805184853872689)
      ·
        refine ⟨468344423701353888640404517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624459231601805184853872689 468344423701353888640404517)
        ·
          refine ⟨87814579444003854120075847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468344423701353888640404517 87814579444003854120075847)
          ·
            refine ⟨131721869166005781180113771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87814579444003854120075847 131721869166005781180113771)
            ·
              refine ⟨197582803749008671770170657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131721869166005781180113771 197582803749008671770170657)
              ·
                refine ⟨148187102811756503827627993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197582803749008671770170657 148187102811756503827627993)
                ·
                  refine ⟨111140327108817377870720995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148187102811756503827627993 111140327108817377870720995)
                  ·
                    refine ⟨166710490663226066806081493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111140327108817377870720995 166710490663226066806081493)
                    ·
                      refine ⟨3907277124919360940767535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166710490663226066806081493 3907277124919360940767535)
                      ·
                        rfl

theorem cell23_7609395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_7609395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609395 prefixEnd_7609395 := by exact prefixLift 7609395
  have htrace : WordTrace (prefixWord ++ tailWord_7609395) baseStart_7609395 baseEnd_7609395 := by
    simpa [prefixWord, tailWord_7609395, baseEnd_7609395] using wordTrace_append hprefix tailTrace_7609395
  have hstable : (prefixWord ++ tailWord_7609395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609395).length < 2 ^ (prefixWord ++ tailWord_7609395).sum := by decide
  have hdescent : baseEnd_7609395 < baseStart_7609395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609406 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_7609406 : Nat := 118140960795 + 7609406 * 2 ^ 59
def prefixEnd_7609406 : Nat := 4983230072969 + 3 ^ 40 * 7609406 * 2
def baseEnd_7609406 : Nat := 434142530356284488636665

theorem tailTrace_7609406 : CollatzResearch.WordTrace tailWord_7609406 prefixEnd_7609406 434142530356284488636665 := by
  unfold tailWord_7609406
  simp only [CollatzResearch.WordTrace]
  refine ⟨34692229683803639990602009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185025224980286079949877381 34692229683803639990602009)
  ·
    refine ⟨26019172262852729992951507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34692229683803639990602009 26019172262852729992951507)
    ·
      refine ⟨39028758394279094989427261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26019172262852729992951507 39028758394279094989427261)
      ·
        refine ⟨14635784397854660621035223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39028758394279094989427261 14635784397854660621035223)
        ·
          refine ⟨21953676596781990931552835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14635784397854660621035223 21953676596781990931552835)
          ·
            refine ⟨32930514895172986397329253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953676596781990931552835 32930514895172986397329253)
            ·
              refine ⟨6174471542844934949499235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32930514895172986397329253 6174471542844934949499235)
              ·
                refine ⟨9261707314267402424248853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174471542844934949499235 9261707314267402424248853)
                ·
                  refine ⟨434142530356284488636665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9261707314267402424248853 434142530356284488636665)
                  ·
                    rfl

theorem cell23_7609406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_7609406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609406 prefixEnd_7609406 := by exact prefixLift 7609406
  have htrace : WordTrace (prefixWord ++ tailWord_7609406) baseStart_7609406 baseEnd_7609406 := by
    simpa [prefixWord, tailWord_7609406, baseEnd_7609406] using wordTrace_append hprefix tailTrace_7609406
  have hstable : (prefixWord ++ tailWord_7609406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609406).length < 2 ^ (prefixWord ++ tailWord_7609406).sum := by decide
  have hdescent : baseEnd_7609406 < baseStart_7609406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609426 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_7609426 : Nat := 118140960795 + 7609426 * 2 ^ 59
def prefixEnd_7609426 : Nat := 4983230072969 + 3 ^ 40 * 7609426 * 2
def baseEnd_7609426 : Nat := 3907293042819650319479893

theorem tailTrace_7609426 : CollatzResearch.WordTrace tailWord_7609426 prefixEnd_7609426 3907293042819650319479893 := by
  unfold tailWord_7609426
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384641732589165835136033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185025711286904442227029421 69384641732589165835136033)
  ·
    refine ⟨52038481299441874376352025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69384641732589165835136033 52038481299441874376352025)
    ·
      refine ⟨39028860974581405782264019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52038481299441874376352025 39028860974581405782264019)
      ·
        refine ⟨58543291461872108673396029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39028860974581405782264019 58543291461872108673396029)
        ·
          refine ⟨21953734298202040752523511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58543291461872108673396029 21953734298202040752523511)
          ·
            refine ⟨32930601447303061128785267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953734298202040752523511 32930601447303061128785267)
            ·
              refine ⟨49395902170954591693177901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32930601447303061128785267 49395902170954591693177901)
              ·
                refine ⟨18523463314107971884941713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49395902170954591693177901 18523463314107971884941713)
                ·
                  refine ⟨13892597485580978913706285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18523463314107971884941713 13892597485580978913706285)
                  ·
                    refine ⟨5209724057092867092639857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13892597485580978913706285 5209724057092867092639857)
                    ·
                      refine ⟨3907293042819650319479893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209724057092867092639857 3907293042819650319479893)
                      ·
                        rfl

theorem cell23_7609426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_7609426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609426 prefixEnd_7609426 := by exact prefixLift 7609426
  have htrace : WordTrace (prefixWord ++ tailWord_7609426) baseStart_7609426 baseEnd_7609426 := by
    simpa [prefixWord, tailWord_7609426, baseEnd_7609426] using wordTrace_append hprefix tailTrace_7609426
  have hstable : (prefixWord ++ tailWord_7609426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609426).length < 2 ^ (prefixWord ++ tailWord_7609426).sum := by decide
  have hdescent : baseEnd_7609426 < baseStart_7609426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609432 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_7609432 : Nat := 118140960795 + 7609432 * 2 ^ 59
def prefixEnd_7609432 : Nat := 4983230072969 + 3 ^ 40 * 7609432 * 2
def baseEnd_7609432 : Nat := 1302432041234525765334955

theorem tailTrace_7609432 : CollatzResearch.WordTrace tailWord_7609432 prefixEnd_7609432 1302432041234525765334955 := by
  unfold tailWord_7609432
  simp only [CollatzResearch.WordTrace]
  refine ⟨138769392884167463182631275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185025857178889950910175033 138769392884167463182631275)
  ·
    refine ⟨208154089326251194773946913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138769392884167463182631275 208154089326251194773946913)
    ·
      refine ⟨156115566994688396080460185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208154089326251194773946913 156115566994688396080460185)
      ·
        refine ⟨117086675246016297060345139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156115566994688396080460185 117086675246016297060345139)
        ·
          refine ⟨175630012869024445590517709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117086675246016297060345139 175630012869024445590517709)
          ·
            refine ⟨65861254825884167096444141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175630012869024445590517709 65861254825884167096444141)
            ·
              refine ⟨24697970559706562661166553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65861254825884167096444141 24697970559706562661166553)
              ·
                refine ⟨18523477919779921995874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24697970559706562661166553 18523477919779921995874915)
                ·
                  refine ⟨27785216879669882993812373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18523477919779921995874915 27785216879669882993812373)
                  ·
                    refine ⟨1302432041234525765334955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27785216879669882993812373 1302432041234525765334955)
                    ·
                      rfl

theorem cell23_7609432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_7609432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609432 prefixEnd_7609432 := by exact prefixLift 7609432
  have htrace : WordTrace (prefixWord ++ tailWord_7609432) baseStart_7609432 baseEnd_7609432 := by
    simpa [prefixWord, tailWord_7609432, baseEnd_7609432] using wordTrace_append hprefix tailTrace_7609432
  have hstable : (prefixWord ++ tailWord_7609432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609432).length < 2 ^ (prefixWord ++ tailWord_7609432).sum := by decide
  have hdescent : baseEnd_7609432 < baseStart_7609432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609436 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7609436 : Nat := 118140960795 + 7609436 * 2 ^ 59
def prefixEnd_7609436 : Nat := 4983230072969 + 3 ^ 40 * 7609436 * 2
def baseEnd_7609436 : Nat := 1302432725875398426784949

theorem tailTrace_7609436 : CollatzResearch.WordTrace tailWord_7609436 prefixEnd_7609436 1302432725875398426784949 := by
  unfold tailWord_7609436
  simp only [CollatzResearch.WordTrace]
  refine ⟨138769465830160217524204081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185025954440213623365605441 138769465830160217524204081)
  ·
    refine ⟨104077099372620163143153061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138769465830160217524204081 104077099372620163143153061)
    ·
      refine ⟨19514456132366280589341199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104077099372620163143153061 19514456132366280589341199)
      ·
        refine ⟨29271684198549420884011799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19514456132366280589341199 29271684198549420884011799)
        ·
          refine ⟨43907526297824131326017699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29271684198549420884011799 43907526297824131326017699)
          ·
            refine ⟨65861289446736196989026549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43907526297824131326017699 65861289446736196989026549)
            ·
              refine ⟨6174495885631518467721239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65861289446736196989026549 6174495885631518467721239)
              ·
                refine ⟨9261743828447277701581859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174495885631518467721239 9261743828447277701581859)
                ·
                  refine ⟨13892615742670916552372789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9261743828447277701581859 13892615742670916552372789)
                  ·
                    refine ⟨1302432725875398426784949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13892615742670916552372789 1302432725875398426784949)
                    ·
                      rfl

theorem cell23_7609436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7609436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609436 prefixEnd_7609436 := by exact prefixLift 7609436
  have htrace : WordTrace (prefixWord ++ tailWord_7609436) baseStart_7609436 baseEnd_7609436 := by
    simpa [prefixWord, tailWord_7609436, baseEnd_7609436] using wordTrace_append hprefix tailTrace_7609436
  have hstable : (prefixWord ++ tailWord_7609436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609436).length < 2 ^ (prefixWord ++ tailWord_7609436).sum := by decide
  have hdescent : baseEnd_7609436 < baseStart_7609436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609449 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 2, 4]
def baseStart_7609449 : Nat := 118140960795 + 7609449 * 2 ^ 59
def prefixEnd_7609449 : Nat := 4983230072969 + 3 ^ 40 * 7609449 * 2
def baseEnd_7609449 : Nat := 1302434950958234576497429

theorem tailTrace_7609449 : CollatzResearch.WordTrace tailWord_7609449 prefixEnd_7609449 1302434950958234576497429 := by
  unfold tailWord_7609449
  simp only [CollatzResearch.WordTrace]
  refine ⟨277539405809273338268631401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185026270539515558845754267 277539405809273338268631401)
  ·
    refine ⟨208154554356955003701473551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277539405809273338268631401 208154554356955003701473551)
    ·
      refine ⟨312231831535432505552210327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208154554356955003701473551 312231831535432505552210327)
      ·
        refine ⟨468347747303148758328315491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312231831535432505552210327 468347747303148758328315491)
        ·
          refine ⟨702521620954723137492473237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468347747303148758328315491 702521620954723137492473237)
          ·
            refine ⟨32930700982252647069959683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 702521620954723137492473237 32930700982252647069959683)
            ·
              refine ⟨49396051473378970604939525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32930700982252647069959683 49396051473378970604939525)
              ·
                refine ⟨9261759651258556988426161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49396051473378970604939525 9261759651258556988426161)
                ·
                  refine ⟨6946319738443917741319621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261759651258556988426161 6946319738443917741319621)
                  ·
                    refine ⟨1302434950958234576497429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946319738443917741319621 1302434950958234576497429)
                    ·
                      rfl

theorem cell23_7609449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 4].length) (baseStart_7609449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609449 prefixEnd_7609449 := by exact prefixLift 7609449
  have htrace : WordTrace (prefixWord ++ tailWord_7609449) baseStart_7609449 baseEnd_7609449 := by
    simpa [prefixWord, tailWord_7609449, baseEnd_7609449] using wordTrace_append hprefix tailTrace_7609449
  have hstable : (prefixWord ++ tailWord_7609449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609449).length < 2 ^ (prefixWord ++ tailWord_7609449).sum := by decide
  have hdescent : baseEnd_7609449 < baseStart_7609449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609450 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_7609450 : Nat := 118140960795 + 7609450 * 2 ^ 59
def prefixEnd_7609450 : Nat := 4983230072969 + 3 ^ 40 * 7609450 * 2
def baseEnd_7609450 : Nat := 3907305366355358225579783

theorem tailTrace_7609450 : CollatzResearch.WordTrace tailWord_7609450 prefixEnd_7609450 3907305366355358225579783 := by
  unfold tailWord_7609450
  simp only [CollatzResearch.WordTrace]
  refine ⟨69384860570567428859854451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185026294854846476959611869 69384860570567428859854451)
  ·
    refine ⟨104077290855851143289781677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69384860570567428859854451 104077290855851143289781677)
    ·
      refine ⟨39028984070944178733668129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104077290855851143289781677 39028984070944178733668129)
      ·
        refine ⟨29271738053208134050251097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39028984070944178733668129 29271738053208134050251097)
        ·
          refine ⟨21953803539906100537688323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271738053208134050251097 21953803539906100537688323)
          ·
            refine ⟨32930705309859150806532485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21953803539906100537688323 32930705309859150806532485)
            ·
              refine ⟨6174507245598590776224841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32930705309859150806532485 6174507245598590776224841)
              ·
                refine ⟨4630880434198943082168631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6174507245598590776224841 4630880434198943082168631)
                ·
                  refine ⟨6946320651298414623252947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630880434198943082168631 6946320651298414623252947)
                  ·
                    refine ⟨10419480976947621934879421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946320651298414623252947 10419480976947621934879421)
                    ·
                      refine ⟨3907305366355358225579783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419480976947621934879421 3907305366355358225579783)
                      ·
                        rfl

theorem cell23_7609450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_7609450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609450 prefixEnd_7609450 := by exact prefixLift 7609450
  have htrace : WordTrace (prefixWord ++ tailWord_7609450) baseStart_7609450 baseEnd_7609450 := by
    simpa [prefixWord, tailWord_7609450, baseEnd_7609450] using wordTrace_append hprefix tailTrace_7609450
  have hstable : (prefixWord ++ tailWord_7609450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609450).length < 2 ^ (prefixWord ++ tailWord_7609450).sum := by decide
  have hdescent : baseEnd_7609450 < baseStart_7609450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609452 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_7609452 : Nat := 118140960795 + 7609452 * 2 ^ 59
def prefixEnd_7609452 : Nat := 4983230072969 + 3 ^ 40 * 7609452 * 2
def baseEnd_7609452 : Nat := 3907306393316667217754773

theorem tailTrace_7609452 : CollatzResearch.WordTrace tailWord_7609452 prefixEnd_7609452 3907306393316667217754773 := by
  unfold tailWord_7609452
  simp only [CollatzResearch.WordTrace]
  refine ⟨138769757614131234890495305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185026343485508313187327073 138769757614131234890495305)
  ·
    refine ⟨104077318210598426167871479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138769757614131234890495305 104077318210598426167871479)
    ·
      refine ⟨156115977315897639251807219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104077318210598426167871479 156115977315897639251807219)
      ·
        refine ⟨234173965973846458877710829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156115977315897639251807219 234173965973846458877710829)
        ·
          refine ⟨87815237240192422079141561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234173965973846458877710829 87815237240192422079141561)
          ·
            refine ⟨65861427930144316559356171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87815237240192422079141561 65861427930144316559356171)
            ·
              refine ⟨98792141895216474839034257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65861427930144316559356171 98792141895216474839034257)
              ·
                refine ⟨74094106421412356129275693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98792141895216474839034257 74094106421412356129275693)
                ·
                  refine ⟨27785289908029633548478385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74094106421412356129275693 27785289908029633548478385)
                  ·
                    refine ⟨20838967431022225161358789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27785289908029633548478385 20838967431022225161358789)
                    ·
                      refine ⟨3907306393316667217754773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20838967431022225161358789 3907306393316667217754773)
                      ·
                        rfl

theorem cell23_7609452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_7609452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609452 prefixEnd_7609452 := by exact prefixLift 7609452
  have htrace : WordTrace (prefixWord ++ tailWord_7609452) baseStart_7609452 baseEnd_7609452 := by
    simpa [prefixWord, tailWord_7609452, baseEnd_7609452] using wordTrace_append hprefix tailTrace_7609452
  have hstable : (prefixWord ++ tailWord_7609452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609452).length < 2 ^ (prefixWord ++ tailWord_7609452).sum := by decide
  have hdescent : baseEnd_7609452 < baseStart_7609452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609456 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2]
def baseStart_7609456 : Nat := 118140960795 + 7609456 * 2 ^ 59
def prefixEnd_7609456 : Nat := 4983230072969 + 3 ^ 40 * 7609456 * 2
def baseEnd_7609456 : Nat := 3907308447239285202104755

theorem tailTrace_7609456 : CollatzResearch.WordTrace tailWord_7609456 prefixEnd_7609456 3907308447239285202104755 := by
  unfold tailWord_7609456
  simp only [CollatzResearch.WordTrace]
  refine ⟨138769830560123989232068111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185026440746831985642757481 138769830560123989232068111)
  ·
    refine ⟨208154745840185983848102167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138769830560123989232068111 208154745840185983848102167)
    ·
      refine ⟨312232118760278975772153251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208154745840185983848102167 312232118760278975772153251)
      ·
        refine ⟨468348178140418463658229877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312232118760278975772153251 468348178140418463658229877)
        ·
          refine ⟨43907641700664230967959051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468348178140418463658229877 43907641700664230967959051)
          ·
            refine ⟨65861462550996346451938577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43907641700664230967959051 65861462550996346451938577)
            ·
              refine ⟨49396096913247259838953933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65861462550996346451938577 49396096913247259838953933)
              ·
                refine ⟨18523536342467722439607725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49396096913247259838953933 18523536342467722439607725)
                ·
                  refine ⟨6946326128425395914852897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18523536342467722439607725 6946326128425395914852897)
                  ·
                    refine ⟨5209744596319046936139673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946326128425395914852897 5209744596319046936139673)
                    ·
                      refine ⟨3907308447239285202104755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209744596319046936139673 3907308447239285202104755)
                      ·
                        rfl

theorem cell23_7609456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2].length) (baseStart_7609456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609456 prefixEnd_7609456 := by exact prefixLift 7609456
  have htrace : WordTrace (prefixWord ++ tailWord_7609456) baseStart_7609456 baseEnd_7609456 := by
    simpa [prefixWord, tailWord_7609456, baseEnd_7609456] using wordTrace_append hprefix tailTrace_7609456
  have hstable : (prefixWord ++ tailWord_7609456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609456).length < 2 ^ (prefixWord ++ tailWord_7609456).sum := by decide
  have hdescent : baseEnd_7609456 < baseStart_7609456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609469 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_7609469 : Nat := 118140960795 + 7609469 * 2 ^ 59
def prefixEnd_7609469 : Nat := 4983230072969 + 3 ^ 40 * 7609469 * 2
def baseEnd_7609469 : Nat := 3907315122487793651242195

theorem tailTrace_7609469 : CollatzResearch.WordTrace tailWord_7609469 prefixEnd_7609469 3907315122487793651242195 := by
  unfold tailWord_7609469
  simp only [CollatzResearch.WordTrace]
  refine ⟨277540135269200881684359461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185026756846133921122906307 277540135269200881684359461)
  ·
    refine ⟨52038775362975165315817399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277540135269200881684359461 52038775362975165315817399)
    ·
      refine ⟨78058163044462747973726099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52038775362975165315817399 78058163044462747973726099)
      ·
        refine ⟨117087244566694121960589149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78058163044462747973726099 117087244566694121960589149)
        ·
          refine ⟨43907716712510295735220931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117087244566694121960589149 43907716712510295735220931)
          ·
            refine ⟨65861575068765443602831397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43907716712510295735220931 65861575068765443602831397)
            ·
              refine ⟨12349045325393520675530887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65861575068765443602831397 12349045325393520675530887)
              ·
                refine ⟨18523567988090281013296331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349045325393520675530887 18523567988090281013296331)
                ·
                  refine ⟨27785351982135421519944497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18523567988090281013296331 27785351982135421519944497)
                  ·
                    refine ⟨20839013986601566139958373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27785351982135421519944497 20839013986601566139958373)
                    ·
                      refine ⟨3907315122487793651242195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20839013986601566139958373 3907315122487793651242195)
                      ·
                        rfl

theorem cell23_7609469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_7609469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609469 prefixEnd_7609469 := by exact prefixLift 7609469
  have htrace : WordTrace (prefixWord ++ tailWord_7609469) baseStart_7609469 baseEnd_7609469 := by
    simpa [prefixWord, tailWord_7609469, baseEnd_7609469] using wordTrace_append hprefix tailTrace_7609469
  have hstable : (prefixWord ++ tailWord_7609469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609469).length < 2 ^ (prefixWord ++ tailWord_7609469).sum := by decide
  have hdescent : baseEnd_7609469 < baseStart_7609469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609473 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_7609473 : Nat := 118140960795 + 7609473 * 2 ^ 59
def prefixEnd_7609473 : Nat := 4983230072969 + 3 ^ 40 * 7609473 * 2
def baseEnd_7609473 : Nat := 3907317176410411635592177

theorem tailTrace_7609473 : CollatzResearch.WordTrace tailWord_7609473 prefixEnd_7609473 3907317176410411635592177 := by
  unfold tailWord_7609473
  simp only [CollatzResearch.WordTrace]
  refine ⟨277540281161186390367505073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185026854107457593578336715 277540281161186390367505073)
  ·
    refine ⟨208155210870889792775628805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277540281161186390367505073 208155210870889792775628805)
    ·
      refine ⟨39029102038291836145430401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208155210870889792775628805 39029102038291836145430401)
      ·
        refine ⟨29271826528718877109072801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39029102038291836145430401 29271826528718877109072801)
        ·
          refine ⟨21953869896539157831804601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29271826528718877109072801 21953869896539157831804601)
          ·
            refine ⟨16465402422404368373853451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21953869896539157831804601 16465402422404368373853451)
            ·
              refine ⟨24698103633606552560780177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16465402422404368373853451 24698103633606552560780177)
              ·
                refine ⟨18523577725204914420585133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24698103633606552560780177 18523577725204914420585133)
                ·
                  refine ⟨6946341646951842907719425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18523577725204914420585133 6946341646951842907719425)
                  ·
                    refine ⟨5209756235213882180789569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946341646951842907719425 5209756235213882180789569)
                    ·
                      refine ⟨3907317176410411635592177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209756235213882180789569 3907317176410411635592177)
                      ·
                        rfl

theorem cell23_7609473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_7609473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609473 prefixEnd_7609473 := by exact prefixLift 7609473
  have htrace : WordTrace (prefixWord ++ tailWord_7609473) baseStart_7609473 baseEnd_7609473 := by
    simpa [prefixWord, tailWord_7609473, baseEnd_7609473] using wordTrace_append hprefix tailTrace_7609473
  have hstable : (prefixWord ++ tailWord_7609473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609473).length < 2 ^ (prefixWord ++ tailWord_7609473).sum := by decide
  have hdescent : baseEnd_7609473 < baseStart_7609473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609490 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_7609490 : Nat := 118140960795 + 7609490 * 2 ^ 59
def prefixEnd_7609490 : Nat := 4983230072969 + 3 ^ 40 * 7609490 * 2
def baseEnd_7609490 : Nat := 3907325905581538069079599

theorem tailTrace_7609490 : CollatzResearch.WordTrace tailWord_7609490 prefixEnd_7609490 3907325905581538069079599 := by
  unfold tailWord_7609490
  simp only [CollatzResearch.WordTrace]
  refine ⟨69385225300531200567718481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185027267468083201513915949 69385225300531200567718481)
  ·
    refine ⟨52038918975398400425788861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69385225300531200567718481 52038918975398400425788861)
    ·
      refine ⟨19514594615774400159670823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52038918975398400425788861 19514594615774400159670823)
      ·
        refine ⟨29271891923661600239506235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19514594615774400159670823 29271891923661600239506235)
        ·
          refine ⟨43907837885492400359259353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29271891923661600239506235 43907837885492400359259353)
          ·
            refine ⟨32930878414119300269444515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43907837885492400359259353 32930878414119300269444515)
            ·
              refine ⟨49396317621178950404166773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32930878414119300269444515 49396317621178950404166773)
              ·
                refine ⟨4630904776985526600390635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49396317621178950404166773 4630904776985526600390635)
                ·
                  refine ⟨6946357165478289900585953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4630904776985526600390635 6946357165478289900585953)
                  ·
                    refine ⟨5209767874108717425439465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946357165478289900585953 5209767874108717425439465)
                    ·
                      refine ⟨3907325905581538069079599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209767874108717425439465 3907325905581538069079599)
                      ·
                        rfl

theorem cell23_7609490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_7609490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609490 prefixEnd_7609490 := by exact prefixLift 7609490
  have htrace : WordTrace (prefixWord ++ tailWord_7609490) baseStart_7609490 baseEnd_7609490 := by
    simpa [prefixWord, tailWord_7609490, baseEnd_7609490] using wordTrace_append hprefix tailTrace_7609490
  have hstable : (prefixWord ++ tailWord_7609490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609490).length < 2 ^ (prefixWord ++ tailWord_7609490).sum := by decide
  have hdescent : baseEnd_7609490 < baseStart_7609490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 7, 3, 2]
def baseStart_7609499 : Nat := 118140960795 + 7609499 * 2 ^ 59
def prefixEnd_7609499 : Nat := 4983230072969 + 3 ^ 40 * 7609499 * 2
def baseEnd_7609499 : Nat := 3907330526907428533867057

theorem tailTrace_7609499 : CollatzResearch.WordTrace tailWord_7609499 prefixEnd_7609499 3907330526907428533867057 := by
  unfold tailWord_7609499
  simp only [CollatzResearch.WordTrace]
  refine ⟨277541229459092196807951551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185027486306061464538634367 277541229459092196807951551)
  ·
    refine ⟨416311844188638295211927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277541229459092196807951551 416311844188638295211927327)
    ·
      refine ⟨624467766282957442817890991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416311844188638295211927327 624467766282957442817890991)
      ·
        refine ⟨936701649424436164226836487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624467766282957442817890991 936701649424436164226836487)
        ·
          refine ⟨1405052474136654246340254731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936701649424436164226836487 1405052474136654246340254731)
          ·
            refine ⟨2107578711204981369510382097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405052474136654246340254731 2107578711204981369510382097)
            ·
              refine ⟨1580684033403736027132786573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107578711204981369510382097 1580684033403736027132786573)
              ·
                refine ⟨592756512526401010174794965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580684033403736027132786573 592756512526401010174794965)
                ·
                  refine ⟨13892730762337523675971757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 592756512526401010174794965 13892730762337523675971757)
                  ·
                    refine ⟨5209774035876571378489409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13892730762337523675971757 5209774035876571378489409)
                    ·
                      refine ⟨3907330526907428533867057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209774035876571378489409 3907330526907428533867057)
                      ·
                        rfl

theorem cell23_7609499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3, 2].length) (baseStart_7609499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609499 prefixEnd_7609499 := by exact prefixLift 7609499
  have htrace : WordTrace (prefixWord ++ tailWord_7609499) baseStart_7609499 baseEnd_7609499 := by
    simpa [prefixWord, tailWord_7609499, baseEnd_7609499] using wordTrace_append hprefix tailTrace_7609499
  have hstable : (prefixWord ++ tailWord_7609499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609499).length < 2 ^ (prefixWord ++ tailWord_7609499).sum := by decide
  have hdescent : baseEnd_7609499 < baseStart_7609499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7609562 : Nat := 118140960795 + 7609562 * 2 ^ 59
def prefixEnd_7609562 : Nat := 4983230072969 + 3 ^ 40 * 7609562 * 2
def baseEnd_7609562 : Nat := 3907362876188661787379267

theorem tailTrace_7609562 : CollatzResearch.WordTrace tailWord_7609562 prefixEnd_7609562 3907362876188661787379267 := by
  unfold tailWord_7609562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69385881814465989641873735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185029018171909305711663293 69385881814465989641873735)
  ·
    refine ⟨104078822721698984462810603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69385881814465989641873735 104078822721698984462810603)
    ·
      refine ⟨156118234082548476694215905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104078822721698984462810603 156118234082548476694215905)
      ·
        refine ⟨117088675561911357520661929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156118234082548476694215905 117088675561911357520661929)
        ·
          refine ⟨87816506671433518140496447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117088675561911357520661929 87816506671433518140496447)
          ·
            refine ⟨131724760007150277210744671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87816506671433518140496447 131724760007150277210744671)
            ·
              refine ⟨197587140010725415816117007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131724760007150277210744671 197587140010725415816117007)
              ·
                refine ⟨296380710016088123724175511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197587140010725415816117007 296380710016088123724175511)
                ·
                  refine ⟨444571065024132185586263267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296380710016088123724175511 444571065024132185586263267)
                  ·
                    refine ⟨666856597536198278379394901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444571065024132185586263267 666856597536198278379394901)
                    ·
                      refine ⟨3907362876188661787379267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 666856597536198278379394901 3907362876188661787379267)
                      ·
                        rfl

theorem cell23_7609562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7609562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609562 prefixEnd_7609562 := by exact prefixLift 7609562
  have htrace : WordTrace (prefixWord ++ tailWord_7609562) baseStart_7609562 baseEnd_7609562 := by
    simpa [prefixWord, tailWord_7609562, baseEnd_7609562] using wordTrace_append hprefix tailTrace_7609562
  have hstable : (prefixWord ++ tailWord_7609562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609562).length < 2 ^ (prefixWord ++ tailWord_7609562).sum := by decide
  have hdescent : baseEnd_7609562 < baseStart_7609562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609569 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 7]
def baseStart_7609569 : Nat := 118140960795 + 7609569 * 2 ^ 59
def prefixEnd_7609569 : Nat := 4983230072969 + 3 ^ 40 * 7609569 * 2
def baseEnd_7609569 : Nat := 434151830061471473332415

theorem tailTrace_7609569 : CollatzResearch.WordTrace tailWord_7609569 prefixEnd_7609569 434151830061471473332415 := by
  unfold tailWord_7609569
  simp only [CollatzResearch.WordTrace]
  refine ⟨277543782568838598762999761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185029188379225732508666507 277543782568838598762999761)
  ·
    refine ⟨208157836926628949072249821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277543782568838598762999761 208157836926628949072249821)
    ·
      refine ⟨78059188847485855902093683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208157836926628949072249821 78059188847485855902093683)
      ·
        refine ⟨117088783271228783853140525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78059188847485855902093683 117088783271228783853140525)
        ·
          refine ⟨43908293726710793944927697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117088783271228783853140525 43908293726710793944927697)
          ·
            refine ⟨32931220295033095458695773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43908293726710793944927697 32931220295033095458695773)
            ·
              refine ⟨12349207610637410797010915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32931220295033095458695773 12349207610637410797010915)
              ·
                refine ⟨18523811415956116195516373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349207610637410797010915 18523811415956116195516373)
                ·
                  refine ⟨434151830061471473332415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18523811415956116195516373 434151830061471473332415)
                  ·
                    rfl

theorem cell23_7609569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 7].length) (baseStart_7609569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609569 prefixEnd_7609569 := by exact prefixLift 7609569
  have htrace : WordTrace (prefixWord ++ tailWord_7609569) baseStart_7609569 baseEnd_7609569 := by
    simpa [prefixWord, tailWord_7609569, baseEnd_7609569] using wordTrace_append hprefix tailTrace_7609569
  have hstable : (prefixWord ++ tailWord_7609569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609569).length < 2 ^ (prefixWord ++ tailWord_7609569).sum := by decide
  have hdescent : baseEnd_7609569 < baseStart_7609569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609580 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_7609580 : Nat := 118140960795 + 7609580 * 2 ^ 59
def prefixEnd_7609580 : Nat := 4983230072969 + 3 ^ 40 * 7609580 * 2
def baseEnd_7609580 : Nat := 3907372118840442716954185

theorem tailTrace_7609580 : CollatzResearch.WordTrace tailWord_7609580 prefixEnd_7609580 3907372118840442716954185 := by
  unfold tailWord_7609580
  simp only [CollatzResearch.WordTrace]
  refine ⟨138772091885899373820825097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185029455847865831761100129 138772091885899373820825097)
  ·
    refine ⟨104079068914424530365618823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138772091885899373820825097 104079068914424530365618823)
    ·
      refine ⟨156118603371636795548428235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104079068914424530365618823 156118603371636795548428235)
      ·
        refine ⟨234177905057455193322642353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156118603371636795548428235 234177905057455193322642353)
        ·
          refine ⟨175633428793091394991981765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234177905057455193322642353 175633428793091394991981765)
          ·
            refine ⟨32931267898704636560996581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175633428793091394991981765 32931267898704636560996581)
            ·
              refine ⟨6174612731007119355186859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32931267898704636560996581 6174612731007119355186859)
              ·
                refine ⟨9261919096510679032780289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174612731007119355186859 9261919096510679032780289)
                ·
                  refine ⟨6946439322383009274585217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9261919096510679032780289 6946439322383009274585217)
                  ·
                    refine ⟨5209829491787256955938913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946439322383009274585217 5209829491787256955938913)
                    ·
                      refine ⟨3907372118840442716954185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209829491787256955938913 3907372118840442716954185)
                      ·
                        rfl

theorem cell23_7609580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_7609580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609580 prefixEnd_7609580 := by exact prefixLift 7609580
  have htrace : WordTrace (prefixWord ++ tailWord_7609580) baseStart_7609580 baseEnd_7609580 := by
    simpa [prefixWord, tailWord_7609580, baseEnd_7609580] using wordTrace_append hprefix tailTrace_7609580
  have hstable : (prefixWord ++ tailWord_7609580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609580).length < 2 ^ (prefixWord ++ tailWord_7609580).sum := by decide
  have hdescent : baseEnd_7609580 < baseStart_7609580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609599 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 2, 5]
def baseStart_7609599 : Nat := 118140960795 + 7609599 * 2 ^ 59
def prefixEnd_7609599 : Nat := 4983230072969 + 3 ^ 40 * 7609599 * 2
def baseEnd_7609599 : Nat := 1302460624990959380872199

theorem tailTrace_7609599 : CollatzResearch.WordTrace tailWord_7609599 prefixEnd_7609599 1302460624990959380872199 := by
  unfold tailWord_7609599
  simp only [CollatzResearch.WordTrace]
  refine ⟨277544876758729913886591851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185029917839153275924394567 277544876758729913886591851)
  ·
    refine ⟨416317315138094870829887777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277544876758729913886591851 416317315138094870829887777)
    ·
      refine ⟨312237986353571153122415833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416317315138094870829887777 312237986353571153122415833)
      ·
        refine ⟨234178489765178364841811875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312237986353571153122415833 234178489765178364841811875)
        ·
          refine ⟨351267734647767547262717813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234178489765178364841811875 351267734647767547262717813)
          ·
            refine ⟨32931350123228207555879795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351267734647767547262717813 32931350123228207555879795)
            ·
              refine ⟨49397025184842311333819693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32931350123228207555879795 49397025184842311333819693)
              ·
                refine ⟨18523884444315866750182385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49397025184842311333819693 18523884444315866750182385)
                ·
                  refine ⟨13892913333236900062636789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18523884444315866750182385 13892913333236900062636789)
                  ·
                    refine ⟨1302460624990959380872199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13892913333236900062636789 1302460624990959380872199)
                    ·
                      rfl

theorem cell23_7609599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_7609599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609599 prefixEnd_7609599 := by exact prefixLift 7609599
  have htrace : WordTrace (prefixWord ++ tailWord_7609599) baseStart_7609599 baseEnd_7609599 := by
    simpa [prefixWord, tailWord_7609599, baseEnd_7609599] using wordTrace_append hprefix tailTrace_7609599
  have hstable : (prefixWord ++ tailWord_7609599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609599).length < 2 ^ (prefixWord ++ tailWord_7609599).sum := by decide
  have hdescent : baseEnd_7609599 < baseStart_7609599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609630 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7609630 : Nat := 118140960795 + 7609630 * 2 ^ 59
def prefixEnd_7609630 : Nat := 4983230072969 + 3 ^ 40 * 7609630 * 2
def baseEnd_7609630 : Nat := 3907397792873167521328955

theorem tailTrace_7609630 : CollatzResearch.WordTrace tailWord_7609630 prefixEnd_7609630 3907397792873167521328955 := by
  unfold tailWord_7609630
  simp only [CollatzResearch.WordTrace]
  refine ⟨34693250927702200772621293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185030671614411737453980229 34693250927702200772621293)
  ·
    refine ⟨13009969097888325289732985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34693250927702200772621293 13009969097888325289732985)
    ·
      refine ⟨9757476823416243967299739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13009969097888325289732985 9757476823416243967299739)
      ·
        refine ⟨14636215235124365950949609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9757476823416243967299739 14636215235124365950949609)
        ·
          refine ⟨10977161426343274463212207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14636215235124365950949609 10977161426343274463212207)
          ·
            refine ⟨16465742139514911694818311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10977161426343274463212207 16465742139514911694818311)
            ·
              refine ⟨24698613209272367542227467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16465742139514911694818311 24698613209272367542227467)
              ·
                refine ⟨37047919813908551313341201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24698613209272367542227467 37047919813908551313341201)
                ·
                  refine ⟨27785939860431413485005901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37047919813908551313341201 27785939860431413485005901)
                  ·
                    refine ⟨10419727447661780056877213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27785939860431413485005901 10419727447661780056877213)
                    ·
                      refine ⟨3907397792873167521328955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419727447661780056877213 3907397792873167521328955)
                      ·
                        rfl

theorem cell23_7609630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7609630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609630 prefixEnd_7609630 := by exact prefixLift 7609630
  have htrace : WordTrace (prefixWord ++ tailWord_7609630) baseStart_7609630 baseEnd_7609630 := by
    simpa [prefixWord, tailWord_7609630, baseEnd_7609630] using wordTrace_append hprefix tailTrace_7609630
  have hstable : (prefixWord ++ tailWord_7609630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609630).length < 2 ^ (prefixWord ++ tailWord_7609630).sum := by decide
  have hdescent : baseEnd_7609630 < baseStart_7609630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609653 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_7609653 : Nat := 118140960795 + 7609653 * 2 ^ 59
def prefixEnd_7609653 : Nat := 4983230072969 + 3 ^ 40 * 7609653 * 2
def baseEnd_7609653 : Nat := 3907409602928220931341349

theorem tailTrace_7609653 : CollatzResearch.WordTrace tailWord_7609653 prefixEnd_7609653 3907409602928220931341349 := by
  unfold tailWord_7609653
  simp only [CollatzResearch.WordTrace]
  refine ⟨277546846300534281109057613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185031230867022854072705075 277546846300534281109057613)
  ·
    refine ⟨104080067362700355415896605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277546846300534281109057613 104080067362700355415896605)
    ·
      refine ⟨39030025261012633280961227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104080067362700355415896605 39030025261012633280961227)
      ·
        refine ⟨58545037891518949921441841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39030025261012633280961227 58545037891518949921441841)
        ·
          refine ⟨43908778418639212441081381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58545037891518949921441841 43908778418639212441081381)
          ·
            refine ⟨8232895953494852332702759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43908778418639212441081381 8232895953494852332702759)
            ·
              refine ⟨12349343930242278499054139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232895953494852332702759 12349343930242278499054139)
              ·
                refine ⟨18524015895363417748581209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349343930242278499054139 18524015895363417748581209)
                ·
                  refine ⟨13893011921522563311435907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18524015895363417748581209 13893011921522563311435907)
                  ·
                    refine ⟨20839517882283844967153861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13893011921522563311435907 20839517882283844967153861)
                    ·
                      refine ⟨3907409602928220931341349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20839517882283844967153861 3907409602928220931341349)
                      ·
                        rfl

theorem cell23_7609653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_7609653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609653 prefixEnd_7609653 := by exact prefixLift 7609653
  have htrace : WordTrace (prefixWord ++ tailWord_7609653) baseStart_7609653 baseEnd_7609653 := by
    simpa [prefixWord, tailWord_7609653, baseEnd_7609653] using wordTrace_append hprefix tailTrace_7609653
  have hstable : (prefixWord ++ tailWord_7609653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609653).length < 2 ^ (prefixWord ++ tailWord_7609653).sum := by decide
  have hdescent : baseEnd_7609653 < baseStart_7609653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609663 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 1, 4]
def baseStart_7609663 : Nat := 118140960795 + 7609663 * 2 ^ 59
def prefixEnd_7609663 : Nat := 4983230072969 + 3 ^ 40 * 7609663 * 2
def baseEnd_7609663 : Nat := 1302471579244921964072101

theorem tailTrace_7609663 : CollatzResearch.WordTrace tailWord_7609663 prefixEnd_7609663 1302471579244921964072101 := by
  unfold tailWord_7609663
  simp only [CollatzResearch.WordTrace]
  refine ⟨277547211030498052816921643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185031474020332035211281095 277547211030498052816921643)
  ·
    refine ⟨416320816545747079225382465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277547211030498052816921643 416320816545747079225382465)
    ·
      refine ⟨312240612409310309419036849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416320816545747079225382465 312240612409310309419036849)
      ·
        refine ⟨234180459306982732064277637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312240612409310309419036849 234180459306982732064277637)
        ·
          refine ⟨43908836120059262262052057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234180459306982732064277637 43908836120059262262052057)
          ·
            refine ⟨32931627090044446696539043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43908836120059262262052057 32931627090044446696539043)
            ·
              refine ⟨49397440635066670044808565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32931627090044446696539043 49397440635066670044808565)
              ·
                refine ⟨4631010059537500316700803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49397440635066670044808565 4631010059537500316700803)
                ·
                  refine ⟨6946515089306250475051205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631010059537500316700803 6946515089306250475051205)
                  ·
                    refine ⟨1302471579244921964072101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946515089306250475051205 1302471579244921964072101)
                    ·
                      rfl

theorem cell23_7609663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_7609663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609663 prefixEnd_7609663 := by exact prefixLift 7609663
  have htrace : WordTrace (prefixWord ++ tailWord_7609663) baseStart_7609663 baseEnd_7609663 := by
    simpa [prefixWord, tailWord_7609663, baseEnd_7609663] using wordTrace_append hprefix tailTrace_7609663
  have hstable : (prefixWord ++ tailWord_7609663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609663).length < 2 ^ (prefixWord ++ tailWord_7609663).sum := by decide
  have hdescent : baseEnd_7609663 < baseStart_7609663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609669 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_7609669 : Nat := 118140960795 + 7609669 * 2 ^ 59
def prefixEnd_7609669 : Nat := 4983230072969 + 3 ^ 40 * 7609669 * 2
def baseEnd_7609669 : Nat := 3907417818618692868741275

theorem tailTrace_7609669 : CollatzResearch.WordTrace tailWord_7609669 prefixEnd_7609669 3907417818618692868741275 := by
  unfold tailWord_7609669
  simp only [CollatzResearch.WordTrace]
  refine ⟨277547429868476315841640061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185031619912317543894426707 277547429868476315841640061)
  ·
    refine ⟨104080286200678618440615023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277547429868476315841640061 104080286200678618440615023)
    ·
      refine ⟨156120429301017927660922535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104080286200678618440615023 156120429301017927660922535)
      ·
        refine ⟨234180643951526891491383803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156120429301017927660922535 234180643951526891491383803)
        ·
          refine ⟨351270965927290337237075705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234180643951526891491383803 351270965927290337237075705)
          ·
            refine ⟨263453224445467752927806779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351270965927290337237075705 263453224445467752927806779)
            ·
              refine ⟨395179836668201629391710169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263453224445467752927806779 395179836668201629391710169)
              ·
                refine ⟨296384877501151222043782627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395179836668201629391710169 296384877501151222043782627)
                ·
                  refine ⟨444577316251726833065673941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296384877501151222043782627 444577316251726833065673941)
                  ·
                    refine ⟨10419780849649847649976733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 444577316251726833065673941 10419780849649847649976733)
                    ·
                      refine ⟨3907417818618692868741275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419780849649847649976733 3907417818618692868741275)
                      ·
                        rfl

theorem cell23_7609669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_7609669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609669 prefixEnd_7609669 := by exact prefixLift 7609669
  have htrace : WordTrace (prefixWord ++ tailWord_7609669) baseStart_7609669 baseEnd_7609669 := by
    simpa [prefixWord, tailWord_7609669, baseEnd_7609669] using wordTrace_append hprefix tailTrace_7609669
  have hstable : (prefixWord ++ tailWord_7609669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609669).length < 2 ^ (prefixWord ++ tailWord_7609669).sum := by decide
  have hdescent : baseEnd_7609669 < baseStart_7609669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609676 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 6]
def baseStart_7609676 : Nat := 118140960795 + 7609676 * 2 ^ 59
def prefixEnd_7609676 : Nat := 4983230072969 + 3 ^ 40 * 7609676 * 2
def baseEnd_7609676 : Nat := 434157934775919371261527

theorem tailTrace_7609676 : CollatzResearch.WordTrace tailWord_7609676 prefixEnd_7609676 434157934775919371261527 := by
  unfold tailWord_7609676
  simp only [CollatzResearch.WordTrace]
  refine ⟨138773842589725478018572441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185031790119633970691429921 138773842589725478018572441)
  ·
    refine ⟨104080381942294108513929331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138773842589725478018572441 104080381942294108513929331)
    ·
      refine ⟨156120572913441162770893997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104080381942294108513929331 156120572913441162770893997)
      ·
        refine ⟨58545214842540436039085249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156120572913441162770893997 58545214842540436039085249)
        ·
          refine ⟨43908911131905327029313937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58545214842540436039085249 43908911131905327029313937)
          ·
            refine ⟨32931683348928995271985453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43908911131905327029313937 32931683348928995271985453)
            ·
              refine ⟨12349381255848373226994545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32931683348928995271985453 12349381255848373226994545)
              ·
                refine ⟨9262035941886279920245909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12349381255848373226994545 9262035941886279920245909)
                ·
                  refine ⟨434157934775919371261527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9262035941886279920245909 434157934775919371261527)
                  ·
                    rfl

theorem cell23_7609676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_7609676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609676 prefixEnd_7609676 := by exact prefixLift 7609676
  have htrace : WordTrace (prefixWord ++ tailWord_7609676) baseStart_7609676 baseEnd_7609676 := by
    simpa [prefixWord, tailWord_7609676, baseEnd_7609676] using wordTrace_append hprefix tailTrace_7609676
  have hstable : (prefixWord ++ tailWord_7609676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609676).length < 2 ^ (prefixWord ++ tailWord_7609676).sum := by decide
  have hdescent : baseEnd_7609676 < baseStart_7609676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609689 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_7609689 : Nat := 118140960795 + 7609689 * 2 ^ 59
def prefixEnd_7609689 : Nat := 4983230072969 + 3 ^ 40 * 7609689 * 2
def baseEnd_7609689 : Nat := 1302476029410594263497061

theorem tailTrace_7609689 : CollatzResearch.WordTrace tailWord_7609689 prefixEnd_7609689 1302476029410594263497061 := by
  unfold tailWord_7609689
  simp only [CollatzResearch.WordTrace]
  refine ⟨277548159328403859257368121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185032106218935906171578747 277548159328403859257368121)
  ·
    refine ⟨208161119496302894443026091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277548159328403859257368121 208161119496302894443026091)
    ·
      refine ⟨312241679244454341664539137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208161119496302894443026091 312241679244454341664539137)
      ·
        refine ⟨234181259433340756248404353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312241679244454341664539137 234181259433340756248404353)
        ·
          refine ⟨175635944575005567186303265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234181259433340756248404353 175635944575005567186303265)
          ·
            refine ⟨131726958431254175389727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175635944575005567186303265 131726958431254175389727449)
            ·
              refine ⟨98795218823440631542295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131726958431254175389727449 98795218823440631542295587)
              ·
                refine ⟨148192828235160947313443381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98795218823440631542295587 148192828235160947313443381)
                ·
                  refine ⟨13893077647046338810635317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148192828235160947313443381 13893077647046338810635317)
                  ·
                    refine ⟨1302476029410594263497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13893077647046338810635317 1302476029410594263497061)
                    ·
                      rfl

theorem cell23_7609689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_7609689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609689 prefixEnd_7609689 := by exact prefixLift 7609689
  have htrace : WordTrace (prefixWord ++ tailWord_7609689) baseStart_7609689 baseEnd_7609689 := by
    simpa [prefixWord, tailWord_7609689, baseEnd_7609689] using wordTrace_append hprefix tailTrace_7609689
  have hstable : (prefixWord ++ tailWord_7609689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609689).length < 2 ^ (prefixWord ++ tailWord_7609689).sum := by decide
  have hdescent : baseEnd_7609689 < baseStart_7609689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609719 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 6]
def baseStart_7609719 : Nat := 118140960795 + 7609719 * 2 ^ 59
def prefixEnd_7609719 : Nat := 4983230072969 + 3 ^ 40 * 7609719 * 2
def baseEnd_7609719 : Nat := 1302481164217139224372015

theorem tailTrace_7609719 : CollatzResearch.WordTrace tailWord_7609719 prefixEnd_7609719 1302481164217139224372015 := by
  unfold tailWord_7609719
  simp only [CollatzResearch.WordTrace]
  refine ⟨277549253518295174380960211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185032835678863449587306807 277549253518295174380960211)
  ·
    refine ⟨416323880277442761571440317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277549253518295174380960211 416323880277442761571440317)
    ·
      refine ⟨156121455104041035589290119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416323880277442761571440317 156121455104041035589290119)
      ·
        refine ⟨234182182656061553383935179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156121455104041035589290119 234182182656061553383935179)
        ·
          refine ⟨351273273984092330075902769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234182182656061553383935179 351273273984092330075902769)
          ·
            refine ⟨263454955488069247556927077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351273273984092330075902769 263454955488069247556927077)
            ·
              refine ⟨49397804154012983916923827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263454955488069247556927077 49397804154012983916923827)
              ·
                refine ⟨74096706231019475875385741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49397804154012983916923827 74096706231019475875385741)
                ·
                  refine ⟨27786264836632303453269653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74096706231019475875385741 27786264836632303453269653)
                  ·
                    refine ⟨1302481164217139224372015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27786264836632303453269653 1302481164217139224372015)
                    ·
                      rfl

theorem cell23_7609719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_7609719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609719 prefixEnd_7609719 := by exact prefixLift 7609719
  have htrace : WordTrace (prefixWord ++ tailWord_7609719) baseStart_7609719 baseEnd_7609719 := by
    simpa [prefixWord, tailWord_7609719, baseEnd_7609719] using wordTrace_append hprefix tailTrace_7609719
  have hstable : (prefixWord ++ tailWord_7609719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609719).length < 2 ^ (prefixWord ++ tailWord_7609719).sum := by decide
  have hdescent : baseEnd_7609719 < baseStart_7609719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609737 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 3, 1, 3]
def baseStart_7609737 : Nat := 118140960795 + 7609737 * 2 ^ 59
def prefixEnd_7609737 : Nat := 4983230072969 + 3 ^ 40 * 7609737 * 2
def baseEnd_7609737 : Nat := 3907452735303198602690963

theorem tailTrace_7609737 : CollatzResearch.WordTrace tailWord_7609737 prefixEnd_7609737 3907452735303198602690963 := by
  unfold tailWord_7609737
  simp only [CollatzResearch.WordTrace]
  refine ⟨277549910032229963455115465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185033273354819975636743643 277549910032229963455115465)
  ·
    refine ⟨208162432524172472591336599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277549910032229963455115465 208162432524172472591336599)
    ·
      refine ⟨312243648786258708887004899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208162432524172472591336599 312243648786258708887004899)
      ·
        refine ⟨468365473179388063330507349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312243648786258708887004899 468365473179388063330507349)
        ·
          refine ⟨5488657888820953867154383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 468365473179388063330507349 5488657888820953867154383)
          ·
            refine ⟨8232986833231430800731575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488657888820953867154383 8232986833231430800731575)
            ·
              refine ⟨12349480249847146201097363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232986833231430800731575 12349480249847146201097363)
              ·
                refine ⟨18524220374770719301646045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349480249847146201097363 18524220374770719301646045)
                ·
                  refine ⟨6946582640539019738117267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18524220374770719301646045 6946582640539019738117267)
                  ·
                    refine ⟨10419873960808529607175901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946582640539019738117267 10419873960808529607175901)
                    ·
                      refine ⟨3907452735303198602690963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10419873960808529607175901 3907452735303198602690963)
                      ·
                        rfl

theorem cell23_7609737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 1, 3].length) (baseStart_7609737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609737 prefixEnd_7609737 := by exact prefixLift 7609737
  have htrace : WordTrace (prefixWord ++ tailWord_7609737) baseStart_7609737 baseEnd_7609737 := by
    simpa [prefixWord, tailWord_7609737, baseEnd_7609737] using wordTrace_append hprefix tailTrace_7609737
  have hstable : (prefixWord ++ tailWord_7609737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609737).length < 2 ^ (prefixWord ++ tailWord_7609737).sum := by decide
  have hdescent : baseEnd_7609737 < baseStart_7609737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609739 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_7609739 : Nat := 118140960795 + 7609739 * 2 ^ 59
def prefixEnd_7609739 : Nat := 4983230072969 + 3 ^ 40 * 7609739 * 2
def baseEnd_7609739 : Nat := 3907453762264507594865953

theorem tailTrace_7609739 : CollatzResearch.WordTrace tailWord_7609739 prefixEnd_7609739 3907453762264507594865953 := by
  unfold tailWord_7609739
  simp only [CollatzResearch.WordTrace]
  refine ⟨277549982978222717796688271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185033321985481811864458847 277549982978222717796688271)
  ·
    refine ⟨416324974467334076695032407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277549982978222717796688271 416324974467334076695032407)
    ·
      refine ⟨624487461701001115042548611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416324974467334076695032407 624487461701001115042548611)
      ·
        refine ⟨936731192551501672563822917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624487461701001115042548611 936731192551501672563822917)
        ·
          refine ⟨175637098603406563605716797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 936731192551501672563822917 175637098603406563605716797)
          ·
            refine ⟨65863911976277461352143799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175637098603406563605716797 65863911976277461352143799)
            ·
              refine ⟨98795867964416192028215699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65863911976277461352143799 98795867964416192028215699)
              ·
                refine ⟨148193801946624288042323549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98795867964416192028215699 148193801946624288042323549)
                ·
                  refine ⟨55572675729984108015871331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148193801946624288042323549 55572675729984108015871331)
                  ·
                    refine ⟨83359013594976162023806997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55572675729984108015871331 83359013594976162023806997)
                    ·
                      refine ⟨3907453762264507594865953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83359013594976162023806997 3907453762264507594865953)
                      ·
                        rfl

theorem cell23_7609739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_7609739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609739 prefixEnd_7609739 := by exact prefixLift 7609739
  have htrace : WordTrace (prefixWord ++ tailWord_7609739) baseStart_7609739 baseEnd_7609739 := by
    simpa [prefixWord, tailWord_7609739, baseEnd_7609739] using wordTrace_append hprefix tailTrace_7609739
  have hstable : (prefixWord ++ tailWord_7609739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609739).length < 2 ^ (prefixWord ++ tailWord_7609739).sum := by decide
  have hdescent : baseEnd_7609739 < baseStart_7609739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609749 : List Nat := [1, 3, 2, 1, 1, 2, 3, 10]
def baseStart_7609749 : Nat := 118140960795 + 7609749 * 2 ^ 59
def prefixEnd_7609749 : Nat := 4983230072969 + 3 ^ 40 * 7609749 * 2
def baseEnd_7609749 : Nat := 144720699891520465027441

theorem tailTrace_7609749 : CollatzResearch.WordTrace tailWord_7609749 prefixEnd_7609749 144720699891520465027441 := by
  unfold tailWord_7609749
  simp only [CollatzResearch.WordTrace]
  refine ⟨277550347708186489504552301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185033565138790993003034867 277550347708186489504552301)
  ·
    refine ⟨104081380390569933564207113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277550347708186489504552301 104081380390569933564207113)
    ·
      refine ⟨78061035292927450173155335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104081380390569933564207113 78061035292927450173155335)
      ·
        refine ⟨117091552939391175259733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78061035292927450173155335 117091552939391175259733003)
        ·
          refine ⟨175637329409086762889599505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117091552939391175259733003 175637329409086762889599505)
          ·
            refine ⟨131727997056815072167199629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175637329409086762889599505 131727997056815072167199629)
            ·
              refine ⟨49397998896305652062699861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131727997056815072167199629 49397998896305652062699861)
              ·
                refine ⟨144720699891520465027441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49397998896305652062699861 144720699891520465027441)
                ·
                  rfl

theorem cell23_7609749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 10].length) (baseStart_7609749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609749 prefixEnd_7609749 := by exact prefixLift 7609749
  have htrace : WordTrace (prefixWord ++ tailWord_7609749) baseStart_7609749 baseEnd_7609749 := by
    simpa [prefixWord, tailWord_7609749, baseEnd_7609749] using wordTrace_append hprefix tailTrace_7609749
  have hstable : (prefixWord ++ tailWord_7609749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609749).length < 2 ^ (prefixWord ++ tailWord_7609749).sum := by decide
  have hdescent : baseEnd_7609749 < baseStart_7609749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609753 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 2, 4]
def baseStart_7609753 : Nat := 118140960795 + 7609753 * 2 ^ 59
def prefixEnd_7609753 : Nat := 4983230072969 + 3 ^ 40 * 7609753 * 2
def baseEnd_7609753 : Nat := 1302486983664556846696963

theorem tailTrace_7609753 : CollatzResearch.WordTrace tailWord_7609753 prefixEnd_7609753 1302486983664556846696963 := by
  unfold tailWord_7609753
  simp only [CollatzResearch.WordTrace]
  refine ⟨277550493600171998187697913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185033662400114665458465275 277550493600171998187697913)
  ·
    refine ⟨208162870200128998640773435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277550493600171998187697913 208162870200128998640773435)
    ·
      refine ⟨312244305300193497961160153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208162870200128998640773435 312244305300193497961160153)
      ·
        refine ⟨234183228975145123470870115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312244305300193497961160153 234183228975145123470870115)
        ·
          refine ⟨351274843462717685206305173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234183228975145123470870115 351274843462717685206305173)
          ·
            refine ⟨16466008287314891494045555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351274843462717685206305173 16466008287314891494045555)
            ·
              refine ⟨24699012430972337241068333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16466008287314891494045555 24699012430972337241068333)
              ·
                refine ⟨9262129661614626465400625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24699012430972337241068333 9262129661614626465400625)
                ·
                  refine ⟨6946597246210969849050469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262129661614626465400625 6946597246210969849050469)
                  ·
                    refine ⟨1302486983664556846696963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946597246210969849050469 1302486983664556846696963)
                    ·
                      rfl

theorem cell23_7609753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 4].length) (baseStart_7609753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609753 prefixEnd_7609753 := by exact prefixLift 7609753
  have htrace : WordTrace (prefixWord ++ tailWord_7609753) baseStart_7609753 baseEnd_7609753 := by
    simpa [prefixWord, tailWord_7609753, baseEnd_7609753] using wordTrace_append hprefix tailTrace_7609753
  have hstable : (prefixWord ++ tailWord_7609753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609753).length < 2 ^ (prefixWord ++ tailWord_7609753).sum := by decide
  have hdescent : baseEnd_7609753 < baseStart_7609753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609773 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7609773 : Nat := 118140960795 + 7609773 * 2 ^ 59
def prefixEnd_7609773 : Nat := 4983230072969 + 3 ^ 40 * 7609773 * 2
def baseEnd_7609773 : Nat := 3907471220606760461840797

theorem tailTrace_7609773 : CollatzResearch.WordTrace tailWord_7609773 prefixEnd_7609773 3907471220606760461840797 := by
  unfold tailWord_7609773
  simp only [CollatzResearch.WordTrace]
  refine ⟨277551223060099541603425973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185034148706733027735617315 277551223060099541603425973)
  ·
    refine ⟨26020427161884332025321185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277551223060099541603425973 26020427161884332025321185)
    ·
      refine ⟨19515320371413249018990889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26020427161884332025321185 19515320371413249018990889)
      ·
        refine ⟨14636490278559936764243167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19515320371413249018990889 14636490278559936764243167)
        ·
          refine ⟨21954735417839905146364751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14636490278559936764243167 21954735417839905146364751)
          ·
            refine ⟨32932103126759857719547127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21954735417839905146364751 32932103126759857719547127)
            ·
              refine ⟨49398154690139786579320691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32932103126759857719547127 49398154690139786579320691)
              ·
                refine ⟨74097232035209679868981037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49398154690139786579320691 74097232035209679868981037)
                ·
                  refine ⟨27786462013203629950867889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74097232035209679868981037 27786462013203629950867889)
                  ·
                    refine ⟨20839846509902722463150917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27786462013203629950867889 20839846509902722463150917)
                    ·
                      refine ⟨3907471220606760461840797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20839846509902722463150917 3907471220606760461840797)
                      ·
                        rfl

theorem cell23_7609773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7609773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609773 prefixEnd_7609773 := by exact prefixLift 7609773
  have htrace : WordTrace (prefixWord ++ tailWord_7609773) baseStart_7609773 baseEnd_7609773 := by
    simpa [prefixWord, tailWord_7609773, baseEnd_7609773] using wordTrace_append hprefix tailTrace_7609773
  have hstable : (prefixWord ++ tailWord_7609773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609773).length < 2 ^ (prefixWord ++ tailWord_7609773).sum := by decide
  have hdescent : baseEnd_7609773 < baseStart_7609773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609777 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_7609777 : Nat := 118140960795 + 7609777 * 2 ^ 59
def prefixEnd_7609777 : Nat := 4983230072969 + 3 ^ 40 * 7609777 * 2
def baseEnd_7609777 : Nat := 3907473274529378446190779

theorem tailTrace_7609777 : CollatzResearch.WordTrace tailWord_7609777 prefixEnd_7609777 3907473274529378446190779 := by
  unfold tailWord_7609777
  simp only [CollatzResearch.WordTrace]
  refine ⟨277551368952085050286571585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185034245968056700191047723 277551368952085050286571585)
  ·
    refine ⟨208163526714063787714928689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277551368952085050286571585 208163526714063787714928689)
    ·
      refine ⟨156122645035547840786196517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208163526714063787714928689 156122645035547840786196517)
      ·
        refine ⟨29272995944165220147411847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156122645035547840786196517 29272995944165220147411847)
        ·
          refine ⟨43909493916247830221117771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29272995944165220147411847 43909493916247830221117771)
          ·
            refine ⟨65864240874371745331676657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43909493916247830221117771 65864240874371745331676657)
            ·
              refine ⟨49398180655778808998757493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65864240874371745331676657 49398180655778808998757493)
              ·
                refine ⟨4631079436479263343633515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49398180655778808998757493 4631079436479263343633515)
                ·
                  refine ⟨6946619154718895015450273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631079436479263343633515 6946619154718895015450273)
                  ·
                    refine ⟨5209964366039171261587705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946619154718895015450273 5209964366039171261587705)
                    ·
                      refine ⟨3907473274529378446190779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209964366039171261587705 3907473274529378446190779)
                      ·
                        rfl

theorem cell23_7609777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_7609777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609777 prefixEnd_7609777 := by exact prefixLift 7609777
  have htrace : WordTrace (prefixWord ++ tailWord_7609777) baseStart_7609777 baseEnd_7609777 := by
    simpa [prefixWord, tailWord_7609777, baseEnd_7609777] using wordTrace_append hprefix tailTrace_7609777
  have hstable : (prefixWord ++ tailWord_7609777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609777).length < 2 ^ (prefixWord ++ tailWord_7609777).sum := by decide
  have hdescent : baseEnd_7609777 < baseStart_7609777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609779 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 7]
def baseStart_7609779 : Nat := 118140960795 + 7609779 * 2 ^ 59
def prefixEnd_7609779 : Nat := 4983230072969 + 3 ^ 40 * 7609779 * 2
def baseEnd_7609779 : Nat := 1302491433830229146121923

theorem tailTrace_7609779 : CollatzResearch.WordTrace tailWord_7609779 prefixEnd_7609779 1302491433830229146121923 := by
  unfold tailWord_7609779
  simp only [CollatzResearch.WordTrace]
  refine ⟨277551441898077804628144391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185034294598718536418762927 277551441898077804628144391)
  ·
    refine ⟨416327162847116706942216587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277551441898077804628144391 416327162847116706942216587)
    ·
      refine ⟨624490744270675060413324881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416327162847116706942216587 624490744270675060413324881)
      ·
        refine ⟨468368058203006295309993661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624490744270675060413324881 468368058203006295309993661)
        ·
          refine ⟨175638021826127360741247623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468368058203006295309993661 175638021826127360741247623)
          ·
            refine ⟨263457032739191041111871435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175638021826127360741247623 263457032739191041111871435)
            ·
              refine ⟨395185549108786561667807153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263457032739191041111871435 395185549108786561667807153)
              ·
                refine ⟨296389161831589921250855365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395185549108786561667807153 296389161831589921250855365)
                ·
                  refine ⟨55572967843423110234535381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296389161831589921250855365 55572967843423110234535381)
                  ·
                    refine ⟨1302491433830229146121923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55572967843423110234535381 1302491433830229146121923)
                    ·
                      rfl

theorem cell23_7609779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_7609779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609779 prefixEnd_7609779 := by exact prefixLift 7609779
  have htrace : WordTrace (prefixWord ++ tailWord_7609779) baseStart_7609779 baseEnd_7609779 := by
    simpa [prefixWord, tailWord_7609779, baseEnd_7609779] using wordTrace_append hprefix tailTrace_7609779
  have hstable : (prefixWord ++ tailWord_7609779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609779).length < 2 ^ (prefixWord ++ tailWord_7609779).sum := by decide
  have hdescent : baseEnd_7609779 < baseStart_7609779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609803 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 3, 3, 2]
def baseStart_7609803 : Nat := 118140960795 + 7609803 * 2 ^ 59
def prefixEnd_7609803 : Nat := 4983230072969 + 3 ^ 40 * 7609803 * 2
def baseEnd_7609803 : Nat := 3907486625026395344465659

theorem tailTrace_7609803 : CollatzResearch.WordTrace tailWord_7609803 prefixEnd_7609803 3907486625026395344465659 := by
  unfold tailWord_7609803
  simp only [CollatzResearch.WordTrace]
  refine ⟨277552317249990856727018063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185034878166660571151345375 277552317249990856727018063)
  ·
    refine ⟨416328475874986285090527095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277552317249990856727018063 416328475874986285090527095)
    ·
      refine ⟨624492713812479427635790643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416328475874986285090527095 624492713812479427635790643)
      ·
        refine ⟨936739070718719141453685965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624492713812479427635790643 936739070718719141453685965)
        ·
          refine ⟨351277151519519678045132237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 936739070718719141453685965 351277151519519678045132237)
          ·
            refine ⟨131728931819819879266924589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351277151519519678045132237 131728931819819879266924589)
            ·
              refine ⟨49398349432432454725096721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131728931819819879266924589 49398349432432454725096721)
              ·
                refine ⟨37048762074324341043822541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49398349432432454725096721 37048762074324341043822541)
                ·
                  refine ⟨13893285777871627891433453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37048762074324341043822541 13893285777871627891433453)
                  ·
                    refine ⟨5209982166701860459287545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13893285777871627891433453 5209982166701860459287545)
                    ·
                      refine ⟨3907486625026395344465659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5209982166701860459287545 3907486625026395344465659)
                      ·
                        rfl

theorem cell23_7609803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3, 2].length) (baseStart_7609803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609803 prefixEnd_7609803 := by exact prefixLift 7609803
  have htrace : WordTrace (prefixWord ++ tailWord_7609803) baseStart_7609803 baseEnd_7609803 := by
    simpa [prefixWord, tailWord_7609803, baseEnd_7609803] using wordTrace_append hprefix tailTrace_7609803
  have hstable : (prefixWord ++ tailWord_7609803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609803).length < 2 ^ (prefixWord ++ tailWord_7609803).sum := by decide
  have hdescent : baseEnd_7609803 < baseStart_7609803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609836 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_7609836 : Nat := 118140960795 + 7609836 * 2 ^ 59
def prefixEnd_7609836 : Nat := 4983230072969 + 3 ^ 40 * 7609836 * 2
def baseEnd_7609836 : Nat := 3907503569887993715353007

theorem tailTrace_7609836 : CollatzResearch.WordTrace tailWord_7609836 prefixEnd_7609836 3907503569887993715353007 := by
  unfold tailWord_7609836
  simp only [CollatzResearch.WordTrace]
  refine ⟨138776760429435651681484681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185035680572580868908646241 138776760429435651681484681)
  ·
    refine ⟨104082570322076738761113511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138776760429435651681484681 104082570322076738761113511)
    ·
      refine ⟨156123855483115108141670267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104082570322076738761113511 156123855483115108141670267)
      ·
        refine ⟨234185783224672662212505401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156123855483115108141670267 234185783224672662212505401)
        ·
          refine ⟨175639337418504496659379051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234185783224672662212505401 175639337418504496659379051)
          ·
            refine ⟨263459006127756744989068577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175639337418504496659379051 263459006127756744989068577)
            ·
              refine ⟨197594254595817558741801433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263459006127756744989068577 197594254595817558741801433)
              ·
                refine ⟨148195690946863169056351075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197594254595817558741801433 148195690946863169056351075)
                ·
                  refine ⟨222293536420294753584526613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148195690946863169056351075 222293536420294753584526613)
                  ·
                    refine ⟨10420009519701316574274685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222293536420294753584526613 10420009519701316574274685)
                    ·
                      refine ⟨3907503569887993715353007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420009519701316574274685 3907503569887993715353007)
                      ·
                        rfl

theorem cell23_7609836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_7609836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609836 prefixEnd_7609836 := by exact prefixLift 7609836
  have htrace : WordTrace (prefixWord ++ tailWord_7609836) baseStart_7609836 baseEnd_7609836 := by
    simpa [prefixWord, tailWord_7609836, baseEnd_7609836] using wordTrace_append hprefix tailTrace_7609836
  have hstable : (prefixWord ++ tailWord_7609836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609836).length < 2 ^ (prefixWord ++ tailWord_7609836).sum := by decide
  have hdescent : baseEnd_7609836 < baseStart_7609836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609850 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2]
def baseStart_7609850 : Nat := 118140960795 + 7609850 * 2 ^ 59
def prefixEnd_7609850 : Nat := 4983230072969 + 3 ^ 40 * 7609850 * 2
def baseEnd_7609850 : Nat := 3907510758617156660577943

theorem tailTrace_7609850 : CollatzResearch.WordTrace tailWord_7609850 prefixEnd_7609850 3907510758617156660577943 := by
  unfold tailWord_7609850
  simp only [CollatzResearch.WordTrace]
  refine ⟨69388507870205145938494751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185036020987213722502652669 69388507870205145938494751)
  ·
    refine ⟨104082761805307718907742127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69388507870205145938494751 104082761805307718907742127)
    ·
      refine ⟨156124142707961578361613191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104082761805307718907742127 156124142707961578361613191)
      ·
        refine ⟨234186214061942367542419787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156124142707961578361613191 234186214061942367542419787)
        ·
          refine ⟨351279321092913551313629681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234186214061942367542419787 351279321092913551313629681)
          ·
            refine ⟨263459490819685163485222261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351279321092913551313629681 263459490819685163485222261)
            ·
              refine ⟨24699327264345484076739587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263459490819685163485222261 24699327264345484076739587)
              ·
                refine ⟨37048990896518226115109381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24699327264345484076739587 37048990896518226115109381)
                ·
                  refine ⟨6946685793097167396583009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37048990896518226115109381 6946685793097167396583009)
                  ·
                    refine ⟨5210014344822875547437257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946685793097167396583009 5210014344822875547437257)
                    ·
                      refine ⟨3907510758617156660577943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210014344822875547437257 3907510758617156660577943)
                      ·
                        rfl

theorem cell23_7609850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_7609850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609850 prefixEnd_7609850 := by exact prefixLift 7609850
  have htrace : WordTrace (prefixWord ++ tailWord_7609850) baseStart_7609850 baseEnd_7609850 := by
    simpa [prefixWord, tailWord_7609850, baseEnd_7609850] using wordTrace_append hprefix tailTrace_7609850
  have hstable : (prefixWord ++ tailWord_7609850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609850).length < 2 ^ (prefixWord ++ tailWord_7609850).sum := by decide
  have hdescent : baseEnd_7609850 < baseStart_7609850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609863 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7609863 : Nat := 118140960795 + 7609863 * 2 ^ 59
def prefixEnd_7609863 : Nat := 4983230072969 + 3 ^ 40 * 7609863 * 2
def baseEnd_7609863 : Nat := 3907517433865665109715383

theorem tailTrace_7609863 : CollatzResearch.WordTrace tailWord_7609863 prefixEnd_7609863 3907517433865665109715383 := by
  unfold tailWord_7609863
  simp only [CollatzResearch.WordTrace]
  refine ⟨277554505629773486974202243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185036337086515657982801495 277554505629773486974202243)
  ·
    refine ⟨416331758444660230461303365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277554505629773486974202243 416331758444660230461303365)
    ·
      refine ⟨78062204708373793211494381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416331758444660230461303365 78062204708373793211494381)
      ·
        refine ⟨29273326765640172454310393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78062204708373793211494381 29273326765640172454310393)
        ·
          refine ⟨21954995074230129340732795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29273326765640172454310393 21954995074230129340732795)
          ·
            refine ⟨32932492611345194011099193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21954995074230129340732795 32932492611345194011099193)
            ·
              refine ⟨24699369458508895508324395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32932492611345194011099193 24699369458508895508324395)
              ·
                refine ⟨37049054187763343262486593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24699369458508895508324395 37049054187763343262486593)
                ·
                  refine ⟨27786790640822507446864945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37049054187763343262486593 27786790640822507446864945)
                  ·
                    refine ⟨20840092980616880585148709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27786790640822507446864945 20840092980616880585148709)
                    ·
                      refine ⟨3907517433865665109715383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20840092980616880585148709 3907517433865665109715383)
                      ·
                        rfl

theorem cell23_7609863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7609863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609863 prefixEnd_7609863 := by exact prefixLift 7609863
  have htrace : WordTrace (prefixWord ++ tailWord_7609863) baseStart_7609863 baseEnd_7609863 := by
    simpa [prefixWord, tailWord_7609863, baseEnd_7609863] using wordTrace_append hprefix tailTrace_7609863
  have hstable : (prefixWord ++ tailWord_7609863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609863).length < 2 ^ (prefixWord ++ tailWord_7609863).sum := by decide
  have hdescent : baseEnd_7609863 < baseStart_7609863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609867 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 4, 2]
def baseStart_7609867 : Nat := 118140960795 + 7609867 * 2 ^ 59
def prefixEnd_7609867 : Nat := 4983230072969 + 3 ^ 40 * 7609867 * 2
def baseEnd_7609867 : Nat := 3907519487788283094065365

theorem tailTrace_7609867 : CollatzResearch.WordTrace tailWord_7609867 prefixEnd_7609867 3907519487788283094065365 := by
  unfold tailWord_7609867
  simp only [CollatzResearch.WordTrace]
  refine ⟨277554651521758995657347855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185036434347839330438231903 277554651521758995657347855)
  ·
    refine ⟨416331977282638493486021783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277554651521758995657347855 416331977282638493486021783)
    ·
      refine ⟨624497965923957740229032675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416331977282638493486021783 624497965923957740229032675)
      ·
        refine ⟨936746948885936610343549013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624497965923957740229032675 936746948885936610343549013)
        ·
          refine ⟨10977503307257069652463465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 936746948885936610343549013 10977503307257069652463465)
          ·
            refine ⟨8233127480442802239347599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10977503307257069652463465 8233127480442802239347599)
            ·
              refine ⟨12349691220664203359021399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233127480442802239347599 12349691220664203359021399)
              ·
                refine ⟨18524536830996305038532099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349691220664203359021399 18524536830996305038532099)
                ·
                  refine ⟨27786805246494457557798149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18524536830996305038532099 27786805246494457557798149)
                  ·
                    refine ⟨5210025983717710792087153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27786805246494457557798149 5210025983717710792087153)
                    ·
                      refine ⟨3907519487788283094065365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210025983717710792087153 3907519487788283094065365)
                      ·
                        rfl

theorem cell23_7609867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4, 2].length) (baseStart_7609867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609867 prefixEnd_7609867 := by exact prefixLift 7609867
  have htrace : WordTrace (prefixWord ++ tailWord_7609867) baseStart_7609867 baseEnd_7609867 := by
    simpa [prefixWord, tailWord_7609867, baseEnd_7609867] using wordTrace_append hprefix tailTrace_7609867
  have hstable : (prefixWord ++ tailWord_7609867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609867).length < 2 ^ (prefixWord ++ tailWord_7609867).sum := by decide
  have hdescent : baseEnd_7609867 < baseStart_7609867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609890 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_7609890 : Nat := 118140960795 + 7609890 * 2 ^ 59
def prefixEnd_7609890 : Nat := 4983230072969 + 3 ^ 40 * 7609890 * 2
def baseEnd_7609890 : Nat := 434170144204815167119751

theorem tailTrace_7609890 : CollatzResearch.WordTrace tailWord_7609890 prefixEnd_7609890 434170144204815167119751 := by
  unfold tailWord_7609890
  simp only [CollatzResearch.WordTrace]
  refine ⟨69388872600168917646358781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185036993600450447056956749 69388872600168917646358781)
  ·
    refine ⟨26020827225063344117384543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69388872600168917646358781 26020827225063344117384543)
    ·
      refine ⟨39031240837595016176076815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26020827225063344117384543 39031240837595016176076815)
      ·
        refine ⟨58546861256392524264115223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39031240837595016176076815 58546861256392524264115223)
        ·
          refine ⟨87820291884588786396172835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58546861256392524264115223 87820291884588786396172835)
          ·
            refine ⟨131730437826883179594259253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87820291884588786396172835 131730437826883179594259253)
            ·
              refine ⟨12349728546270298086961805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131730437826883179594259253 12349728546270298086961805)
              ·
                refine ⟨4631148204851361782610677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12349728546270298086961805 4631148204851361782610677)
                ·
                  refine ⟨434170144204815167119751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4631148204851361782610677 434170144204815167119751)
                  ·
                    rfl

theorem cell23_7609890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_7609890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609890 prefixEnd_7609890 := by exact prefixLift 7609890
  have htrace : WordTrace (prefixWord ++ tailWord_7609890) baseStart_7609890 baseEnd_7609890 := by
    simpa [prefixWord, tailWord_7609890, baseEnd_7609890] using wordTrace_append hprefix tailTrace_7609890
  have hstable : (prefixWord ++ tailWord_7609890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609890).length < 2 ^ (prefixWord ++ tailWord_7609890).sum := by decide
  have hdescent : baseEnd_7609890 < baseStart_7609890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609893 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 7, 2]
def baseStart_7609893 : Nat := 118140960795 + 7609893 * 2 ^ 59
def prefixEnd_7609893 : Nat := 4983230072969 + 3 ^ 40 * 7609893 * 2
def baseEnd_7609893 : Nat := 3907532838285299992340245

theorem tailTrace_7609893 : CollatzResearch.WordTrace tailWord_7609893 prefixEnd_7609893 3907532838285299992340245 := by
  unfold tailWord_7609893
  simp only [CollatzResearch.WordTrace]
  refine ⟨277555599819664802097794333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185037066546443201398529555 277555599819664802097794333)
  ·
    refine ⟨104083349932374300786672875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277555599819664802097794333 104083349932374300786672875)
    ·
      refine ⟨156125024898561451180009313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104083349932374300786672875 156125024898561451180009313)
      ·
        refine ⟨117093768673921088385006985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156125024898561451180009313 117093768673921088385006985)
        ·
          refine ⟨87820326505440816288755239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117093768673921088385006985 87820326505440816288755239)
          ·
            refine ⟨131730489758161224433132859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87820326505440816288755239 131730489758161224433132859)
            ·
              refine ⟨197595734637241836649699289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131730489758161224433132859 197595734637241836649699289)
              ·
                refine ⟨148196800977931377487274467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197595734637241836649699289 148196800977931377487274467)
                ·
                  refine ⟨222295201466897066230911701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148196800977931377487274467 222295201466897066230911701)
                  ·
                    refine ⟨5210043784380399989786993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222295201466897066230911701 5210043784380399989786993)
                    ·
                      refine ⟨3907532838285299992340245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210043784380399989786993 3907532838285299992340245)
                      ·
                        rfl

theorem cell23_7609893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_7609893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609893 prefixEnd_7609893 := by exact prefixLift 7609893
  have htrace : WordTrace (prefixWord ++ tailWord_7609893) baseStart_7609893 baseEnd_7609893 := by
    simpa [prefixWord, tailWord_7609893, baseEnd_7609893] using wordTrace_append hprefix tailTrace_7609893
  have hstable : (prefixWord ++ tailWord_7609893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609893).length < 2 ^ (prefixWord ++ tailWord_7609893).sum := by decide
  have hdescent : baseEnd_7609893 < baseStart_7609893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609913 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7609913 : Nat := 118140960795 + 7609913 * 2 ^ 59
def prefixEnd_7609913 : Nat := 4983230072969 + 3 ^ 40 * 7609913 * 2
def baseEnd_7609913 : Nat := 3907543107898389914090153

theorem tailTrace_7609913 : CollatzResearch.WordTrace tailWord_7609913 prefixEnd_7609913 3907543107898389914090153 := by
  unfold tailWord_7609913
  simp only [CollatzResearch.WordTrace]
  refine ⟨277556329279592345513522393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185037552853061563675681595 277556329279592345513522393)
  ·
    refine ⟨208167246959694259135141795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277556329279592345513522393 208167246959694259135141795)
    ·
      refine ⟨312250870439541388702712693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208167246959694259135141795 312250870439541388702712693)
      ·
        refine ⟨29273519103707005190879315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312250870439541388702712693 29273519103707005190879315)
        ·
          refine ⟨43910278655560507786318973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29273519103707005190879315 43910278655560507786318973)
          ·
            refine ⟨16466354495835190419869615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43910278655560507786318973 16466354495835190419869615)
            ·
              refine ⟨24699531743752785629804423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16466354495835190419869615 24699531743752785629804423)
              ·
                refine ⟨37049297615629178444706635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24699531743752785629804423 37049297615629178444706635)
                ·
                  refine ⟨55573946423443767667059953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37049297615629178444706635 55573946423443767667059953)
                  ·
                    refine ⟨41680459817582825750294965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55573946423443767667059953 41680459817582825750294965)
                    ·
                      refine ⟨3907543107898389914090153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41680459817582825750294965 3907543107898389914090153)
                      ·
                        rfl

theorem cell23_7609913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7609913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609913 prefixEnd_7609913 := by exact prefixLift 7609913
  have htrace : WordTrace (prefixWord ++ tailWord_7609913) baseStart_7609913 baseEnd_7609913 := by
    simpa [prefixWord, tailWord_7609913, baseEnd_7609913] using wordTrace_append hprefix tailTrace_7609913
  have hstable : (prefixWord ++ tailWord_7609913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609913).length < 2 ^ (prefixWord ++ tailWord_7609913).sum := by decide
  have hdescent : baseEnd_7609913 < baseStart_7609913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609940 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_7609940 : Nat := 118140960795 + 7609940 * 2 ^ 59
def prefixEnd_7609940 : Nat := 4983230072969 + 3 ^ 40 * 7609940 * 2
def baseEnd_7609940 : Nat := 3907556971876061308452529

theorem tailTrace_7609940 : CollatzResearch.WordTrace tailWord_7609940 prefixEnd_7609940 3907556971876061308452529 := by
  unfold tailWord_7609940
  simp only [CollatzResearch.WordTrace]
  refine ⟨138778657025247264562377637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185038209366996352749836849 138778657025247264562377637)
  ·
    refine ⟨26020998192233862105445807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138778657025247264562377637 26020998192233862105445807)
    ·
      refine ⟨39031497288350793158168711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26020998192233862105445807 39031497288350793158168711)
      ·
        refine ⟨58547245932526189737253067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39031497288350793158168711 58547245932526189737253067)
        ·
          refine ⟨87820868898789284605879601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58547245932526189737253067 87820868898789284605879601)
          ·
            refine ⟨65865651674091963454409701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87820868898789284605879601 65865651674091963454409701)
            ·
              refine ⟨12349809688892243147701819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65865651674091963454409701 12349809688892243147701819)
              ·
                refine ⟨18524714533338364721552729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12349809688892243147701819 18524714533338364721552729)
                ·
                  refine ⟨13893535900003773541164547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18524714533338364721552729 13893535900003773541164547)
                  ·
                    refine ⟨20840303850005660311746821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13893535900003773541164547 20840303850005660311746821)
                    ·
                      refine ⟨3907556971876061308452529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20840303850005660311746821 3907556971876061308452529)
                      ·
                        rfl

theorem cell23_7609940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_7609940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609940 prefixEnd_7609940 := by exact prefixLift 7609940
  have htrace : WordTrace (prefixWord ++ tailWord_7609940) baseStart_7609940 baseEnd_7609940 := by
    simpa [prefixWord, tailWord_7609940, baseEnd_7609940] using wordTrace_append hprefix tailTrace_7609940
  have hstable : (prefixWord ++ tailWord_7609940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609940).length < 2 ^ (prefixWord ++ tailWord_7609940).sum := by decide
  have hdescent : baseEnd_7609940 < baseStart_7609940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609946 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_7609946 : Nat := 118140960795 + 7609946 * 2 ^ 59
def prefixEnd_7609946 : Nat := 4983230072969 + 3 ^ 40 * 7609946 * 2
def baseEnd_7609946 : Nat := 434173339195554253886389

theorem tailTrace_7609946 : CollatzResearch.WordTrace tailWord_7609946 prefixEnd_7609946 434173339195554253886389 := by
  unfold tailWord_7609946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69389383222118198037368423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185038355258981861432982461 69389383222118198037368423)
  ·
    refine ⟨104084074833177297056052635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69389383222118198037368423 104084074833177297056052635)
    ·
      refine ⟨156126112249765945584078953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104084074833177297056052635 156126112249765945584078953)
      ·
        refine ⟨117094584187324459188059215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156126112249765945584078953 117094584187324459188059215)
        ·
          refine ⟨175641876280986688782088823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117094584187324459188059215 175641876280986688782088823)
          ·
            refine ⟨263462814421480033173133235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175641876280986688782088823 263462814421480033173133235)
            ·
              refine ⟨395194221632220049759699853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263462814421480033173133235 395194221632220049759699853)
              ·
                refine ⟨148197833112082518659887445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395194221632220049759699853 148197833112082518659887445)
                ·
                  refine ⟨434173339195554253886389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148197833112082518659887445 434173339195554253886389)
                  ·
                    rfl

theorem cell23_7609946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_7609946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609946 prefixEnd_7609946 := by exact prefixLift 7609946
  have htrace : WordTrace (prefixWord ++ tailWord_7609946) baseStart_7609946 baseEnd_7609946 := by
    simpa [prefixWord, tailWord_7609946, baseEnd_7609946] using wordTrace_append hprefix tailTrace_7609946
  have hstable : (prefixWord ++ tailWord_7609946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609946).length < 2 ^ (prefixWord ++ tailWord_7609946).sum := by decide
  have hdescent : baseEnd_7609946 < baseStart_7609946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609976 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_7609976 : Nat := 118140960795 + 7609976 * 2 ^ 59
def prefixEnd_7609976 : Nat := 4983230072969 + 3 ^ 40 * 7609976 * 2
def baseEnd_7609976 : Nat := 1302525152393207722534121

theorem tailTrace_7609976 : CollatzResearch.WordTrace tailWord_7609976 prefixEnd_7609976 1302525152393207722534121 := by
  unfold tailWord_7609976
  simp only [CollatzResearch.WordTrace]
  refine ⟨138779313539182053636532891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185039084718909404848710521 138779313539182053636532891)
  ·
    refine ⟨208168970308773080454799337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138779313539182053636532891 208168970308773080454799337)
    ·
      refine ⟨156126727731579810341099503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208168970308773080454799337 156126727731579810341099503)
      ·
        refine ⟨234190091597369715511649255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156126727731579810341099503 234190091597369715511649255)
        ·
          refine ⟨351285137396054573267473883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234190091597369715511649255 351285137396054573267473883)
          ·
            refine ⟨526927706094081859901210825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351285137396054573267473883 526927706094081859901210825)
            ·
              refine ⟨395195779570561394925908119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526927706094081859901210825 395195779570561394925908119)
              ·
                refine ⟨592793669355842092388862179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395195779570561394925908119 592793669355842092388862179)
                ·
                  refine ⟨889190504033763138583293269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592793669355842092388862179 889190504033763138583293269)
                  ·
                    refine ⟨1302525152393207722534121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 889190504033763138583293269 1302525152393207722534121)
                    ·
                      rfl

theorem cell23_7609976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_7609976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609976 prefixEnd_7609976 := by exact prefixLift 7609976
  have htrace : WordTrace (prefixWord ++ tailWord_7609976) baseStart_7609976 baseEnd_7609976 := by
    simpa [prefixWord, tailWord_7609976, baseEnd_7609976] using wordTrace_append hprefix tailTrace_7609976
  have hstable : (prefixWord ++ tailWord_7609976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609976).length < 2 ^ (prefixWord ++ tailWord_7609976).sum := by decide
  have hdescent : baseEnd_7609976 < baseStart_7609976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7609993 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_7609993 : Nat := 118140960795 + 7609993 * 2 ^ 59
def prefixEnd_7609993 : Nat := 4983230072969 + 3 ^ 40 * 7609993 * 2
def baseEnd_7609993 : Nat := 1302528062116916533696595

theorem tailTrace_7609993 : CollatzResearch.WordTrace tailWord_7609993 prefixEnd_7609993 1302528062116916533696595 := by
  unfold tailWord_7609993
  simp only [CollatzResearch.WordTrace]
  refine ⟨277559247119302519176434633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185039498079535012784289755 277559247119302519176434633)
  ·
    refine ⟨208169435339476889382325975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277559247119302519176434633 208169435339476889382325975)
    ·
      refine ⟨312254153009215334073488963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208169435339476889382325975 312254153009215334073488963)
      ·
        refine ⟨468381229513823001110233445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312254153009215334073488963 468381229513823001110233445)
        ·
          refine ⟨87821480533841812708168771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468381229513823001110233445 87821480533841812708168771)
          ·
            refine ⟨131732220800762719062253157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87821480533841812708168771 131732220800762719062253157)
            ·
              refine ⟨24699791400143009824172467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131732220800762719062253157 24699791400143009824172467)
              ·
                refine ⟨37049687100214514736258701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24699791400143009824172467 37049687100214514736258701)
                ·
                  refine ⟨13893632662580443026097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37049687100214514736258701 13893632662580443026097013)
                  ·
                    refine ⟨1302528062116916533696595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13893632662580443026097013 1302528062116916533696595)
                    ·
                      rfl

theorem cell23_7609993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_7609993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7609993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7609993 prefixEnd_7609993 := by exact prefixLift 7609993
  have htrace : WordTrace (prefixWord ++ tailWord_7609993) baseStart_7609993 baseEnd_7609993 := by
    simpa [prefixWord, tailWord_7609993, baseEnd_7609993] using wordTrace_append hprefix tailTrace_7609993
  have hstable : (prefixWord ++ tailWord_7609993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7609993).length < 2 ^ (prefixWord ++ tailWord_7609993).sum := by decide
  have hdescent : baseEnd_7609993 < baseStart_7609993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7609993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610040 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_7610040 : Nat := 118140960795 + 7610040 * 2 ^ 59
def prefixEnd_7610040 : Nat := 4983230072969 + 3 ^ 40 * 7610040 * 2
def baseEnd_7610040 : Nat := 1302536106647170305734023

theorem tailTrace_7610040 : CollatzResearch.WordTrace tailWord_7610040 prefixEnd_7610040 1302536106647170305734023 := by
  unfold tailWord_7610040
  simp only [CollatzResearch.WordTrace]
  refine ⟨138780480675066123101697787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185040640900088164135597049 138780480675066123101697787)
  ·
    refine ⟨208170721012599184652546681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138780480675066123101697787 208170721012599184652546681)
    ·
      refine ⟨156128040759449388489410011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208170721012599184652546681 156128040759449388489410011)
      ·
        refine ⟨234192061139174082734115017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156128040759449388489410011 234192061139174082734115017)
        ·
          refine ⟨175644045854380562050586263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234192061139174082734115017 175644045854380562050586263)
          ·
            refine ⟨263466068781570843075879395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175644045854380562050586263 263466068781570843075879395)
            ·
              refine ⟨395199103172356264613819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263466068781570843075879395 395199103172356264613819093)
              ·
                refine ⟨9262478980602099951886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 395199103172356264613819093 9262478980602099951886385)
                ·
                  refine ⟨6946859235451574963914789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262478980602099951886385 6946859235451574963914789)
                  ·
                    refine ⟨1302536106647170305734023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946859235451574963914789 1302536106647170305734023)
                    ·
                      rfl

theorem cell23_7610040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_7610040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610040 prefixEnd_7610040 := by exact prefixLift 7610040
  have htrace : WordTrace (prefixWord ++ tailWord_7610040) baseStart_7610040 baseEnd_7610040 := by
    simpa [prefixWord, tailWord_7610040, baseEnd_7610040] using wordTrace_append hprefix tailTrace_7610040
  have hstable : (prefixWord ++ tailWord_7610040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610040).length < 2 ^ (prefixWord ++ tailWord_7610040).sum := by decide
  have hdescent : baseEnd_7610040 < baseStart_7610040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610047 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 3, 2, 2]
def baseStart_7610047 : Nat := 118140960795 + 7610047 * 2 ^ 59
def prefixEnd_7610047 : Nat := 4983230072969 + 3 ^ 40 * 7610047 * 2
def baseEnd_7610047 : Nat := 3907611914306092389814537

theorem tailTrace_7610047 : CollatzResearch.WordTrace tailWord_7610047 prefixEnd_7610047 3907611914306092389814537 := by
  unfold tailWord_7610047
  simp only [CollatzResearch.WordTrace]
  refine ⟨277561216661106886398900395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185040811107404590932600263 277561216661106886398900395)
  ·
    refine ⟨416341824991660329598350593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277561216661106886398900395 416341824991660329598350593)
    ·
      refine ⟨312256368743745247198762945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416341824991660329598350593 312256368743745247198762945)
      ·
        refine ⟨234192276557808935399072209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312256368743745247198762945 234192276557808935399072209)
        ·
          refine ⟨175644207418356701549304157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234192276557808935399072209 175644207418356701549304157)
          ·
            refine ⟨65866577781883763080989059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175644207418356701549304157 65866577781883763080989059)
            ·
              refine ⟨98799866672825644621483589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65866577781883763080989059 98799866672825644621483589)
              ·
                refine ⟨18524975001154808366528173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98799866672825644621483589 18524975001154808366528173)
                ·
                  refine ⟨6946865625433053137448065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18524975001154808366528173 6946865625433053137448065)
                  ·
                    refine ⟨5210149219074789853086049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946865625433053137448065 5210149219074789853086049)
                    ·
                      refine ⟨3907611914306092389814537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210149219074789853086049 3907611914306092389814537)
                      ·
                        rfl

theorem cell23_7610047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_7610047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610047 prefixEnd_7610047 := by exact prefixLift 7610047
  have htrace : WordTrace (prefixWord ++ tailWord_7610047) baseStart_7610047 baseEnd_7610047 := by
    simpa [prefixWord, tailWord_7610047, baseEnd_7610047] using wordTrace_append hprefix tailTrace_7610047
  have hstable : (prefixWord ++ tailWord_7610047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610047).length < 2 ^ (prefixWord ++ tailWord_7610047).sum := by decide
  have hdescent : baseEnd_7610047 < baseStart_7610047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610058 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_7610058 : Nat := 118140960795 + 7610058 * 2 ^ 59
def prefixEnd_7610058 : Nat := 4983230072969 + 3 ^ 40 * 7610058 * 2
def baseEnd_7610058 : Nat := 3907617562593291846776987

theorem tailTrace_7610058 : CollatzResearch.WordTrace tailWord_7610058 prefixEnd_7610058 3907617562593291846776987 := by
  unfold tailWord_7610058
  simp only [CollatzResearch.WordTrace]
  refine ⟨69390404466016758819387707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185041078576044690185033885 69390404466016758819387707)
  ·
    refine ⟨104085606699025138229081561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69390404466016758819387707 104085606699025138229081561)
    ·
      refine ⟨78064205024268853671811171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104085606699025138229081561 78064205024268853671811171)
      ·
        refine ⟨117096307536403280507716757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78064205024268853671811171 117096307536403280507716757)
        ·
          refine ⟨5488889415768903773799223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117096307536403280507716757 5488889415768903773799223)
          ·
            refine ⟨8233334123653355660698835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5488889415768903773799223 8233334123653355660698835)
            ·
              refine ⟨12350001185480033491048253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233334123653355660698835 12350001185480033491048253)
              ·
                refine ⟨4631250444555012559143095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12350001185480033491048253 4631250444555012559143095)
                ·
                  refine ⟨6946875666832518838714643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631250444555012559143095 6946875666832518838714643)
                  ·
                    refine ⟨10420313500248778258071965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6946875666832518838714643 10420313500248778258071965)
                    ·
                      refine ⟨3907617562593291846776987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420313500248778258071965 3907617562593291846776987)
                      ·
                        rfl

theorem cell23_7610058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_7610058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610058 prefixEnd_7610058 := by exact prefixLift 7610058
  have htrace : WordTrace (prefixWord ++ tailWord_7610058) baseStart_7610058 baseEnd_7610058 := by
    simpa [prefixWord, tailWord_7610058, baseEnd_7610058] using wordTrace_append hprefix tailTrace_7610058
  have hstable : (prefixWord ++ tailWord_7610058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610058).length < 2 ^ (prefixWord ++ tailWord_7610058).sum := by decide
  have hdescent : baseEnd_7610058 < baseStart_7610058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610064 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 1, 2, 2]
def baseStart_7610064 : Nat := 118140960795 + 7610064 * 2 ^ 59
def prefixEnd_7610064 : Nat := 4983230072969 + 3 ^ 40 * 7610064 * 2
def baseEnd_7610064 : Nat := 3907620643477218823301959

theorem tailTrace_7610064 : CollatzResearch.WordTrace tailWord_7610064 prefixEnd_7610064 3907620643477218823301959 := by
  unfold tailWord_7610064
  simp only [CollatzResearch.WordTrace]
  refine ⟨138780918351022649151134623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185041224468030198868179497 138780918351022649151134623)
  ·
    refine ⟨208171377526533973726701935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138780918351022649151134623 208171377526533973726701935)
    ·
      refine ⟨312257066289800960590052903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208171377526533973726701935 312257066289800960590052903)
      ·
        refine ⟨468385599434701440885079355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312257066289800960590052903 468385599434701440885079355)
        ·
          refine ⟨702578399152052161327619033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468385599434701440885079355 702578399152052161327619033)
          ·
            refine ⟨526933799364039120995714275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702578399152052161327619033 526933799364039120995714275)
            ·
              refine ⟨790400699046058681493571413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526933799364039120995714275 790400699046058681493571413)
              ·
                refine ⟨4631254095973000086876395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 790400699046058681493571413 4631254095973000086876395)
                ·
                  refine ⟨6946881143959500130314593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631254095973000086876395 6946881143959500130314593)
                  ·
                    refine ⟨5210160857969625097735945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946881143959500130314593 5210160857969625097735945)
                    ·
                      refine ⟨3907620643477218823301959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210160857969625097735945 3907620643477218823301959)
                      ·
                        rfl

theorem cell23_7610064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 2, 2].length) (baseStart_7610064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610064 prefixEnd_7610064 := by exact prefixLift 7610064
  have htrace : WordTrace (prefixWord ++ tailWord_7610064) baseStart_7610064 baseEnd_7610064 := by
    simpa [prefixWord, tailWord_7610064, baseEnd_7610064] using wordTrace_append hprefix tailTrace_7610064
  have hstable : (prefixWord ++ tailWord_7610064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610064).length < 2 ^ (prefixWord ++ tailWord_7610064).sum := by decide
  have hdescent : baseEnd_7610064 < baseStart_7610064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610081 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_7610081 : Nat := 118140960795 + 7610081 * 2 ^ 59
def prefixEnd_7610081 : Nat := 4983230072969 + 3 ^ 40 * 7610081 * 2
def baseEnd_7610081 : Nat := 3907629372648345256789381

theorem tailTrace_7610081 : CollatzResearch.WordTrace tailWord_7610081 prefixEnd_7610081 3907629372648345256789381 := by
  unfold tailWord_7610081
  simp only [CollatzResearch.WordTrace]
  refine ⟨277562456742983710205638097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185041637828655806803758731 277562456742983710205638097)
  ·
    refine ⟨208171842557237782654228573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277562456742983710205638097 208171842557237782654228573)
    ·
      refine ⟨78064440958964168495335715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208171842557237782654228573 78064440958964168495335715)
      ·
        refine ⟨117096661438446252743003573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78064440958964168495335715 117096661438446252743003573)
        ·
          refine ⟨10977812009854336194656585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117096661438446252743003573 10977812009854336194656585)
          ·
            refine ⟨8233359007390752145992439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10977812009854336194656585 8233359007390752145992439)
            ·
              refine ⟨12350038511086128218988659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233359007390752145992439 12350038511086128218988659)
              ·
                refine ⟨18525057766629192328482989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350038511086128218988659 18525057766629192328482989)
                ·
                  refine ⟨6946896662485947123181121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18525057766629192328482989 6946896662485947123181121)
                  ·
                    refine ⟨5210172496864460342385841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946896662485947123181121 5210172496864460342385841)
                    ·
                      refine ⟨3907629372648345256789381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210172496864460342385841 3907629372648345256789381)
                      ·
                        rfl

theorem cell23_7610081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_7610081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610081 prefixEnd_7610081 := by exact prefixLift 7610081
  have htrace : WordTrace (prefixWord ++ tailWord_7610081) baseStart_7610081 baseEnd_7610081 := by
    simpa [prefixWord, tailWord_7610081, baseEnd_7610081] using wordTrace_append hprefix tailTrace_7610081
  have hstable : (prefixWord ++ tailWord_7610081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610081).length < 2 ^ (prefixWord ++ tailWord_7610081).sum := by decide
  have hdescent : baseEnd_7610081 < baseStart_7610081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610087 : List Nat := [1, 1, 5, 4, 1, 1, 2, 8]
def baseStart_7610087 : Nat := 118140960795 + 7610087 * 2 ^ 59
def prefixEnd_7610087 : Nat := 4983230072969 + 3 ^ 40 * 7610087 * 2
def baseEnd_7610087 : Nat := 144727127908602675307939

theorem tailTrace_7610087 : CollatzResearch.WordTrace tailWord_7610087 prefixEnd_7610087 144727127908602675307939 := by
  unfold tailWord_7610087
  simp only [CollatzResearch.WordTrace]
  refine ⟨277562675580961973230356515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185041783720641315486904343 277562675580961973230356515)
  ·
    refine ⟨416344013371442959845534773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277562675580961973230356515 416344013371442959845534773)
    ·
      refine ⟨39032251253572777485518885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416344013371442959845534773 39032251253572777485518885)
      ·
        refine ⟨7318547110044895778534791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39032251253572777485518885 7318547110044895778534791)
        ·
          refine ⟨10977820665067343667802187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318547110044895778534791 10977820665067343667802187)
          ·
            refine ⟨16466730997601015501703281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10977820665067343667802187 16466730997601015501703281)
            ·
              refine ⟨12350048248200761626277461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16466730997601015501703281 12350048248200761626277461)
              ·
                refine ⟨144727127908602675307939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12350048248200761626277461 144727127908602675307939)
                ·
                  rfl

theorem cell23_7610087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 8].length) (baseStart_7610087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610087 prefixEnd_7610087 := by exact prefixLift 7610087
  have htrace : WordTrace (prefixWord ++ tailWord_7610087) baseStart_7610087 baseEnd_7610087 := by
    simpa [prefixWord, tailWord_7610087, baseEnd_7610087] using wordTrace_append hprefix tailTrace_7610087
  have hstable : (prefixWord ++ tailWord_7610087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610087).length < 2 ^ (prefixWord ++ tailWord_7610087).sum := by decide
  have hdescent : baseEnd_7610087 < baseStart_7610087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610107 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 1, 3, 2]
def baseStart_7610107 : Nat := 118140960795 + 7610107 * 2 ^ 59
def prefixEnd_7610107 : Nat := 4983230072969 + 3 ^ 40 * 7610107 * 2
def baseEnd_7610107 : Nat := 3907642723145362155064261

theorem tailTrace_7610107 : CollatzResearch.WordTrace tailWord_7610107 prefixEnd_7610107 3907642723145362155064261 := by
  unfold tailWord_7610107
  simp only [CollatzResearch.WordTrace]
  refine ⟨277563405040889516646084575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185042270027259677764056383 277563405040889516646084575)
  ·
    refine ⟨416345107561334274969126863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277563405040889516646084575 416345107561334274969126863)
    ·
      refine ⟨624517661342001412453690295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416345107561334274969126863 624517661342001412453690295)
      ·
        refine ⟨936776492013002118680535443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624517661342001412453690295 936776492013002118680535443)
        ·
          refine ⟨1405164738019503178020803165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936776492013002118680535443 1405164738019503178020803165)
          ·
            refine ⟨526936776757313691757801187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1405164738019503178020803165 526936776757313691757801187)
            ·
              refine ⟨790405165135970537636701781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526936776757313691757801187 790405165135970537636701781)
              ·
                refine ⟨9262560528937154737930099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 790405165135970537636701781 9262560528937154737930099)
                ·
                  refine ⟨13893840793405732106895149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9262560528937154737930099 13893840793405732106895149)
                  ·
                    refine ⟨5210190297527149540085681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13893840793405732106895149 5210190297527149540085681)
                    ·
                      refine ⟨3907642723145362155064261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210190297527149540085681 3907642723145362155064261)
                      ·
                        rfl

theorem cell23_7610107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3, 2].length) (baseStart_7610107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610107 prefixEnd_7610107 := by exact prefixLift 7610107
  have htrace : WordTrace (prefixWord ++ tailWord_7610107) baseStart_7610107 baseEnd_7610107 := by
    simpa [prefixWord, tailWord_7610107, baseEnd_7610107] using wordTrace_append hprefix tailTrace_7610107
  have hstable : (prefixWord ++ tailWord_7610107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610107).length < 2 ^ (prefixWord ++ tailWord_7610107).sum := by decide
  have hdescent : baseEnd_7610107 < baseStart_7610107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610125 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7610125 : Nat := 118140960795 + 7610125 * 2 ^ 59
def prefixEnd_7610125 : Nat := 4983230072969 + 3 ^ 40 * 7610125 * 2
def baseEnd_7610125 : Nat := 1302550655265714361546393

theorem tailTrace_7610125 : CollatzResearch.WordTrace tailWord_7610125 prefixEnd_7610125 1302550655265714361546393 := by
  unfold tailWord_7610125
  simp only [CollatzResearch.WordTrace]
  refine ⟨277564061554824305720239829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185042707703216203813493219 277564061554824305720239829)
  ·
    refine ⟨6505407692691194665318121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277564061554824305720239829 6505407692691194665318121)
    ·
      refine ⟨4879055769518395998988591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6505407692691194665318121 4879055769518395998988591)
      ·
        refine ⟨7318583654277593998482887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879055769518395998988591 7318583654277593998482887)
        ·
          refine ⟨10977875481416390997724331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318583654277593998482887 10977875481416390997724331)
          ·
            refine ⟨16466813222124586496586497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10977875481416390997724331 16466813222124586496586497)
            ·
              refine ⟨12350109916593439872439873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16466813222124586496586497 12350109916593439872439873)
              ·
                refine ⟨9262582437445079904329905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350109916593439872439873 9262582437445079904329905)
                ·
                  refine ⟨6946936828083809928247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262582437445079904329905 6946936828083809928247429)
                  ·
                    refine ⟨1302550655265714361546393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6946936828083809928247429 1302550655265714361546393)
                    ·
                      rfl

theorem cell23_7610125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7610125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610125 prefixEnd_7610125 := by exact prefixLift 7610125
  have htrace : WordTrace (prefixWord ++ tailWord_7610125) baseStart_7610125 baseEnd_7610125 := by
    simpa [prefixWord, tailWord_7610125, baseEnd_7610125] using wordTrace_append hprefix tailTrace_7610125
  have hstable : (prefixWord ++ tailWord_7610125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610125).length < 2 ^ (prefixWord ++ tailWord_7610125).sum := by decide
  have hdescent : baseEnd_7610125 < baseStart_7610125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610132 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7610132 : Nat := 118140960795 + 7610132 * 2 ^ 59
def prefixEnd_7610132 : Nat := 4983230072969 + 3 ^ 40 * 7610132 * 2
def baseEnd_7610132 : Nat := 3907655560161724557251647

theorem tailTrace_7610132 : CollatzResearch.WordTrace tailWord_7610132 prefixEnd_7610132 3907655560161724557251647 := by
  unfold tailWord_7610132
  simp only [CollatzResearch.WordTrace]
  refine ⟨138782158432899472957872325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185042877910532630610496433 138782158432899472957872325)
  ·
    refine ⟨26021654706168651179601061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138782158432899472957872325 26021654706168651179601061)
    ·
      refine ⟨4879060257406622096175199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26021654706168651179601061 4879060257406622096175199)
      ·
        refine ⟨7318590386109933144262799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879060257406622096175199 7318590386109933144262799)
        ·
          refine ⟨10977885579164899716394199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7318590386109933144262799 10977885579164899716394199)
          ·
            refine ⟨16466828368747349574591299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10977885579164899716394199 16466828368747349574591299)
            ·
              refine ⟨24700242553121024361886949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16466828368747349574591299 24700242553121024361886949)
              ·
                refine ⟨4631295478710192067853803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24700242553121024361886949 4631295478710192067853803)
                ·
                  refine ⟨6946943218065288101780705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631295478710192067853803 6946943218065288101780705)
                  ·
                    refine ⟨5210207413548966076335529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946943218065288101780705 5210207413548966076335529)
                    ·
                      refine ⟨3907655560161724557251647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210207413548966076335529 3907655560161724557251647)
                      ·
                        rfl

theorem cell23_7610132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7610132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610132 prefixEnd_7610132 := by exact prefixLift 7610132
  have htrace : WordTrace (prefixWord ++ tailWord_7610132) baseStart_7610132 baseEnd_7610132 := by
    simpa [prefixWord, tailWord_7610132, baseEnd_7610132] using wordTrace_append hprefix tailTrace_7610132
  have hstable : (prefixWord ++ tailWord_7610132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610132).length < 2 ^ (prefixWord ++ tailWord_7610132).sum := by decide
  have hdescent : baseEnd_7610132 < baseStart_7610132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610137 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 8, 2, 2]
def baseStart_7610137 : Nat := 118140960795 + 7610137 * 2 ^ 59
def prefixEnd_7610137 : Nat := 4983230072969 + 3 ^ 40 * 7610137 * 2
def baseEnd_7610137 : Nat := 3907658127564997037689123

theorem tailTrace_7610137 : CollatzResearch.WordTrace tailWord_7610137 prefixEnd_7610137 3907658127564997037689123 := by
  unfold tailWord_7610137
  simp only [CollatzResearch.WordTrace]
  refine ⟨277564499230780831769676665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185042999487187221179784443 277564499230780831769676665)
  ·
    refine ⟨208173374423085623827257499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277564499230780831769676665 208173374423085623827257499)
    ·
      refine ⟨312260061634628435740886249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208173374423085623827257499 312260061634628435740886249)
      ·
        refine ⟨234195046225971326805664687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312260061634628435740886249 234195046225971326805664687)
        ·
          refine ⟨351292569338956990208497031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234195046225971326805664687 351292569338956990208497031)
          ·
            refine ⟨526938854008435485312745547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351292569338956990208497031 526938854008435485312745547)
            ·
              refine ⟨790408281012653227969118321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526938854008435485312745547 790408281012653227969118321)
              ·
                refine ⟨592806210759489920976838741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790408281012653227969118321 592806210759489920976838741)
                ·
                  refine ⟨6946947782337772511447329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 592806210759489920976838741 6946947782337772511447329)
                  ·
                    refine ⟨5210210836753329383585497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946947782337772511447329 5210210836753329383585497)
                    ·
                      refine ⟨3907658127564997037689123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210210836753329383585497 3907658127564997037689123)
                      ·
                        rfl

theorem cell23_7610137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_7610137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610137 prefixEnd_7610137 := by exact prefixLift 7610137
  have htrace : WordTrace (prefixWord ++ tailWord_7610137) baseStart_7610137 baseEnd_7610137 := by
    simpa [prefixWord, tailWord_7610137, baseEnd_7610137] using wordTrace_append hprefix tailTrace_7610137
  have hstable : (prefixWord ++ tailWord_7610137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610137).length < 2 ^ (prefixWord ++ tailWord_7610137).sum := by decide
  have hdescent : baseEnd_7610137 < baseStart_7610137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610140 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7610140 : Nat := 118140960795 + 7610140 * 2 ^ 59
def prefixEnd_7610140 : Nat := 4983230072969 + 3 ^ 40 * 7610140 * 2
def baseEnd_7610140 : Nat := 3907659668006960525951609

theorem tailTrace_7610140 : CollatzResearch.WordTrace tailWord_7610140 prefixEnd_7610140 3907659668006960525951609 := by
  unfold tailWord_7610140
  simp only [CollatzResearch.WordTrace]
  refine ⟨138782304324884981641017937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185043072433179975521357249 138782304324884981641017937)
  ·
    refine ⟨104086728243663736230763453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138782304324884981641017937 104086728243663736230763453)
    ·
      refine ⟨39032523091373901086536295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104086728243663736230763453 39032523091373901086536295)
      ·
        refine ⟨58548784637060851629804443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39032523091373901086536295 58548784637060851629804443)
        ·
          refine ⟨87823176955591277444706665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58548784637060851629804443 87823176955591277444706665)
          ·
            refine ⟨65867382716693458083529999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87823176955591277444706665 65867382716693458083529999)
            ·
              refine ⟨98801074075040187125294999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65867382716693458083529999 98801074075040187125294999)
              ·
                refine ⟨148201611112560280687942499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98801074075040187125294999 148201611112560280687942499)
                ·
                  refine ⟨222302416668840421031913749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148201611112560280687942499 222302416668840421031913749)
                  ·
                    refine ⟨10420425781351894735870957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222302416668840421031913749 10420425781351894735870957)
                    ·
                      refine ⟨3907659668006960525951609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420425781351894735870957 3907659668006960525951609)
                      ·
                        rfl

theorem cell23_7610140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7610140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610140 prefixEnd_7610140 := by exact prefixLift 7610140
  have htrace : WordTrace (prefixWord ++ tailWord_7610140) baseStart_7610140 baseEnd_7610140 := by
    simpa [prefixWord, tailWord_7610140, baseEnd_7610140] using wordTrace_append hprefix tailTrace_7610140
  have hstable : (prefixWord ++ tailWord_7610140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610140).length < 2 ^ (prefixWord ++ tailWord_7610140).sum := by decide
  have hdescent : baseEnd_7610140 < baseStart_7610140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610188 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7610188 : Nat := 118140960795 + 7610188 * 2 ^ 59
def prefixEnd_7610188 : Nat := 4983230072969 + 3 ^ 40 * 7610188 * 2
def baseEnd_7610188 : Nat := 3907684315078376338151389

theorem tailTrace_7610188 : CollatzResearch.WordTrace tailWord_7610188 prefixEnd_7610188 3907684315078376338151389 := by
  unfold tailWord_7610188
  simp only [CollatzResearch.WordTrace]
  refine ⟨138783179676798033739891609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185044239569064044986522145 138783179676798033739891609)
  ·
    refine ⟨104087384757598525304918707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138783179676798033739891609 104087384757598525304918707)
    ·
      refine ⟨156131077136397787957378061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104087384757598525304918707 156131077136397787957378061)
      ·
        refine ⟨58549153926149170484016773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156131077136397787957378061 58549153926149170484016773)
        ·
          refine ⟨10977966361152969465753145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58549153926149170484016773 10977966361152969465753145)
          ·
            refine ⟨8233474770864727099314859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10977966361152969465753145 8233474770864727099314859)
            ·
              refine ⟨12350212156297090648972289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233474770864727099314859 12350212156297090648972289)
              ·
                refine ⟨9262659117222817986729217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350212156297090648972289 9262659117222817986729217)
                ·
                  refine ⟨6946994337917113490046913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262659117222817986729217 6946994337917113490046913)
                  ·
                    refine ⟨5210245753437835117535185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6946994337917113490046913 5210245753437835117535185)
                    ·
                      refine ⟨3907684315078376338151389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210245753437835117535185 3907684315078376338151389)
                      ·
                        rfl

theorem cell23_7610188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7610188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610188 prefixEnd_7610188 := by exact prefixLift 7610188
  have htrace : WordTrace (prefixWord ++ tailWord_7610188) baseStart_7610188 baseEnd_7610188 := by
    simpa [prefixWord, tailWord_7610188, baseEnd_7610188] using wordTrace_append hprefix tailTrace_7610188
  have hstable : (prefixWord ++ tailWord_7610188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610188).length < 2 ^ (prefixWord ++ tailWord_7610188).sum := by decide
  have hdescent : baseEnd_7610188 < baseStart_7610188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610290 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_7610290 : Nat := 118140960795 + 7610290 * 2 ^ 59
def prefixEnd_7610290 : Nat := 4983230072969 + 3 ^ 40 * 7610290 * 2
def baseEnd_7610290 : Nat := 3907736690105134939075919

theorem tailTrace_7610290 : CollatzResearch.WordTrace tailWord_7610290 prefixEnd_7610290 3907736690105134939075919 := by
  unfold tailWord_7610290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392519899806634724999081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185046719732817692599997549 69392519899806634724999081)
  ·
    refine ⟨52044389924854976043749311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69392519899806634724999081 52044389924854976043749311)
    ·
      refine ⟨78066584887282464065623967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52044389924854976043749311 78066584887282464065623967)
      ·
        refine ⟨117099877330923696098435951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78066584887282464065623967 117099877330923696098435951)
        ·
          refine ⟨175649815996385544147653927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117099877330923696098435951 175649815996385544147653927)
          ·
            refine ⟨263474723994578316221480891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175649815996385544147653927 263474723994578316221480891)
            ·
              refine ⟨395212085991867474332221337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263474723994578316221480891 395212085991867474332221337)
              ·
                refine ⟨296409064493900605749166003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395212085991867474332221337 296409064493900605749166003)
                ·
                  refine ⟨444613596740850908623749005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296409064493900605749166003 444613596740850908623749005)
                  ·
                    refine ⟨166730098777819090733905877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444613596740850908623749005 166730098777819090733905877)
                    ·
                      refine ⟨3907736690105134939075919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166730098777819090733905877 3907736690105134939075919)
                      ·
                        rfl

theorem cell23_7610290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_7610290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610290 prefixEnd_7610290 := by exact prefixLift 7610290
  have htrace : WordTrace (prefixWord ++ tailWord_7610290) baseStart_7610290 baseEnd_7610290 := by
    simpa [prefixWord, tailWord_7610290, baseEnd_7610290] using wordTrace_append hprefix tailTrace_7610290
  have hstable : (prefixWord ++ tailWord_7610290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610290).length < 2 ^ (prefixWord ++ tailWord_7610290).sum := by decide
  have hdescent : baseEnd_7610290 < baseStart_7610290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610304 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2]
def baseStart_7610304 : Nat := 118140960795 + 7610304 * 2 ^ 59
def prefixEnd_7610304 : Nat := 4983230072969 + 3 ^ 40 * 7610304 * 2
def baseEnd_7610304 : Nat := 3907743878834297884300855

theorem tailTrace_7610304 : CollatzResearch.WordTrace tailWord_7610304 prefixEnd_7610304 3907743878834297884300855 := by
  unfold tailWord_7610304
  simp only [CollatzResearch.WordTrace]
  refine ⟨138785295110587909645502983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185047060147450546194003977 138785295110587909645502983)
  ·
    refine ⟨208177942665881864468254475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138785295110587909645502983 208177942665881864468254475)
    ·
      refine ⟨312266913998822796702381713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208177942665881864468254475 312266913998822796702381713)
      ·
        refine ⟨234200185499117097526786285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312266913998822796702381713 234200185499117097526786285)
        ·
          refine ⟨87825069562168911572544857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234200185499117097526786285 87825069562168911572544857)
          ·
            refine ⟨65868802171626683679408643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87825069562168911572544857 65868802171626683679408643)
            ·
              refine ⟨98803203257440025519112965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65868802171626683679408643 98803203257440025519112965)
              ·
                refine ⟨18525600610770004784833681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98803203257440025519112965 18525600610770004784833681)
                ·
                  refine ⟨13894200458077503588625261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18525600610770004784833681 13894200458077503588625261)
                  ·
                    refine ⟨5210325171779063845734473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13894200458077503588625261 5210325171779063845734473)
                    ·
                      refine ⟨3907743878834297884300855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210325171779063845734473 3907743878834297884300855)
                      ·
                        rfl

theorem cell23_7610304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_7610304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610304 prefixEnd_7610304 := by exact prefixLift 7610304
  have htrace : WordTrace (prefixWord ++ tailWord_7610304) baseStart_7610304 baseEnd_7610304 := by
    simpa [prefixWord, tailWord_7610304, baseEnd_7610304] using wordTrace_append hprefix tailTrace_7610304
  have hstable : (prefixWord ++ tailWord_7610304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610304).length < 2 ^ (prefixWord ++ tailWord_7610304).sum := by decide
  have hdescent : baseEnd_7610304 < baseStart_7610304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610327 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 6]
def baseStart_7610327 : Nat := 118140960795 + 7610327 * 2 ^ 59
def prefixEnd_7610327 : Nat := 4983230072969 + 3 ^ 40 * 7610327 * 2
def baseEnd_7610327 : Nat := 1302585229629783764771083

theorem tailTrace_7610327 : CollatzResearch.WordTrace tailWord_7610327 prefixEnd_7610327 1302585229629783764771083 := by
  unfold tailWord_7610327
  simp only [CollatzResearch.WordTrace]
  refine ⟨277571429100092494219093235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185047619400061662812728823 277571429100092494219093235)
  ·
    refine ⟨416357143650138741328639853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277571429100092494219093235 416357143650138741328639853)
    ·
      refine ⟨156133928868802027998239945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416357143650138741328639853 156133928868802027998239945)
      ·
        refine ⟨117100446651601520998679959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156133928868802027998239945 117100446651601520998679959)
        ·
          refine ⟨175650669977402281498019939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117100446651601520998679959 175650669977402281498019939)
          ·
            refine ⟨263476004966103422247029909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175650669977402281498019939 263476004966103422247029909)
            ·
              refine ⟨12350437732786097917829527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263476004966103422247029909 12350437732786097917829527)
              ·
                refine ⟨18525656599179146876744291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350437732786097917829527 18525656599179146876744291)
                ·
                  refine ⟨27788484898768720315116437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18525656599179146876744291 27788484898768720315116437)
                  ·
                    refine ⟨1302585229629783764771083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27788484898768720315116437 1302585229629783764771083)
                    ·
                      rfl

theorem cell23_7610327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_7610327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610327 prefixEnd_7610327 := by exact prefixLift 7610327
  have htrace : WordTrace (prefixWord ++ tailWord_7610327) baseStart_7610327 baseEnd_7610327 := by
    simpa [prefixWord, tailWord_7610327, baseEnd_7610327] using wordTrace_append hprefix tailTrace_7610327
  have hstable : (prefixWord ++ tailWord_7610327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610327).length < 2 ^ (prefixWord ++ tailWord_7610327).sum := by decide
  have hdescent : baseEnd_7610327 < baseStart_7610327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610332 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7610332 : Nat := 118140960795 + 7610332 * 2 ^ 59
def prefixEnd_7610332 : Nat := 4983230072969 + 3 ^ 40 * 7610332 * 2
def baseEnd_7610332 : Nat := 3907758256292623774750727

theorem tailTrace_7610332 : CollatzResearch.WordTrace tailWord_7610332 prefixEnd_7610332 3907758256292623774750727 := by
  unfold tailWord_7610332
  simp only [CollatzResearch.WordTrace]
  refine ⟨138785805732537190036512625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185047740976716253382016833 138785805732537190036512625)
  ·
    refine ⟨104089354299402892527384469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138785805732537190036512625 104089354299402892527384469)
    ·
      refine ⟨4879188482784510587221147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104089354299402892527384469 4879188482784510587221147)
      ·
        refine ⟨7318782724176765880831721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879188482784510587221147 7318782724176765880831721)
        ·
          refine ⟨5489087043132574410623791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7318782724176765880831721 5489087043132574410623791)
          ·
            refine ⟨8233630564698861615935687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489087043132574410623791 8233630564698861615935687)
            ·
              refine ⟨12350445847048292423903531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233630564698861615935687 12350445847048292423903531)
              ·
                refine ⟨18525668770572438635855297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350445847048292423903531 18525668770572438635855297)
                ·
                  refine ⟨13894251577929328976891473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18525668770572438635855297 13894251577929328976891473)
                  ·
                    refine ⟨10420688683446996732668605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13894251577929328976891473 10420688683446996732668605)
                    ·
                      refine ⟨3907758256292623774750727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420688683446996732668605 3907758256292623774750727)
                      ·
                        rfl

theorem cell23_7610332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7610332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610332 prefixEnd_7610332 := by exact prefixLift 7610332
  have htrace : WordTrace (prefixWord ++ tailWord_7610332) baseStart_7610332 baseEnd_7610332 := by
    simpa [prefixWord, tailWord_7610332, baseEnd_7610332] using wordTrace_append hprefix tailTrace_7610332
  have hstable : (prefixWord ++ tailWord_7610332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610332).length < 2 ^ (prefixWord ++ tailWord_7610332).sum := by decide
  have hdescent : baseEnd_7610332 < baseStart_7610332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610338 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7610338 : Nat := 118140960795 + 7610338 * 2 ^ 59
def prefixEnd_7610338 : Nat := 4983230072969 + 3 ^ 40 * 7610338 * 2
def baseEnd_7610338 : Nat := 3907761337176550751275699

theorem tailTrace_7610338 : CollatzResearch.WordTrace tailWord_7610338 prefixEnd_7610338 3907761337176550751275699 := by
  unfold tailWord_7610338
  simp only [CollatzResearch.WordTrace]
  refine ⟨69392957575763160774435917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185047886868701762065162445 69392957575763160774435917)
  ·
    refine ⟨26022359090911185290413469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69392957575763160774435917 26022359090911185290413469)
    ·
      refine ⟨9758384659091694483905051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26022359090911185290413469 9758384659091694483905051)
      ·
        refine ⟨14637576988637541725857577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758384659091694483905051 14637576988637541725857577)
        ·
          refine ⟨10978182741478156294393183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14637576988637541725857577 10978182741478156294393183)
          ·
            refine ⟨16467274112217234441589775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978182741478156294393183 16467274112217234441589775)
            ·
              refine ⟨24700911168325851662384663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16467274112217234441589775 24700911168325851662384663)
              ·
                refine ⟨37051366752488777493576995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24700911168325851662384663 37051366752488777493576995)
                ·
                  refine ⟨55577050128733166240365493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37051366752488777493576995 55577050128733166240365493)
                  ·
                    refine ⟨5210348449568734335034265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55577050128733166240365493 5210348449568734335034265)
                    ·
                      refine ⟨3907761337176550751275699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210348449568734335034265 3907761337176550751275699)
                      ·
                        rfl

theorem cell23_7610338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7610338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610338 prefixEnd_7610338 := by exact prefixLift 7610338
  have htrace : WordTrace (prefixWord ++ tailWord_7610338) baseStart_7610338 baseEnd_7610338 := by
    simpa [prefixWord, tailWord_7610338, baseEnd_7610338] using wordTrace_append hprefix tailTrace_7610338
  have hstable : (prefixWord ++ tailWord_7610338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610338).length < 2 ^ (prefixWord ++ tailWord_7610338).sum := by decide
  have hdescent : baseEnd_7610338 < baseStart_7610338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610361 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 2, 4]
def baseStart_7610361 : Nat := 118140960795 + 7610361 * 2 ^ 59
def prefixEnd_7610361 : Nat := 4983230072969 + 3 ^ 40 * 7610361 * 2
def baseEnd_7610361 : Nat := 1302591049077201387096031

theorem tailTrace_7610361 : CollatzResearch.WordTrace tailWord_7610361 prefixEnd_7610361 1302591049077201387096031 := by
  unfold tailWord_7610361
  simp only [CollatzResearch.WordTrace]
  refine ⟨277572669181969318025830937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185048446121312878683887291 277572669181969318025830937)
  ·
    refine ⟨208179501886476988519373203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277572669181969318025830937 208179501886476988519373203)
    ·
      refine ⟨312269252829715482779059805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208179501886476988519373203 312269252829715482779059805)
      ·
        refine ⟨117100969811143306042147427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312269252829715482779059805 117100969811143306042147427)
        ·
          refine ⟨175651454716714959063221141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117100969811143306042147427 175651454716714959063221141)
          ·
            refine ⟨8233661939846013706088491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175651454716714959063221141 8233661939846013706088491)
            ·
              refine ⟨12350492909769020559132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233661939846013706088491 12350492909769020559132737)
              ·
                refine ⟨9262869682326765419349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350492909769020559132737 9262869682326765419349553)
                ·
                  refine ⟨6947152261745074064512165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262869682326765419349553 6947152261745074064512165)
                  ·
                    refine ⟨1302591049077201387096031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947152261745074064512165 1302591049077201387096031)
                    ·
                      rfl

theorem cell23_7610361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 4].length) (baseStart_7610361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610361 prefixEnd_7610361 := by exact prefixLift 7610361
  have htrace : WordTrace (prefixWord ++ tailWord_7610361) baseStart_7610361 baseEnd_7610361 := by
    simpa [prefixWord, tailWord_7610361, baseEnd_7610361] using wordTrace_append hprefix tailTrace_7610361
  have hstable : (prefixWord ++ tailWord_7610361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610361).length < 2 ^ (prefixWord ++ tailWord_7610361).sum := by decide
  have hdescent : baseEnd_7610361 < baseStart_7610361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610367 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_7610367 : Nat := 118140960795 + 7610367 * 2 ^ 59
def prefixEnd_7610367 : Nat := 4983230072969 + 3 ^ 40 * 7610367 * 2
def baseEnd_7610367 : Nat := 3907776228115531137813065

theorem tailTrace_7610367 : CollatzResearch.WordTrace tailWord_7610367 prefixEnd_7610367 3907776228115531137813065 := by
  unfold tailWord_7610367
  simp only [CollatzResearch.WordTrace]
  refine ⟨277572888019947581050549355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185048592013298387367032903 277572888019947581050549355)
  ·
    refine ⟨416359332029921371575824033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277572888019947581050549355 416359332029921371575824033)
    ·
      refine ⟨312269499022441028681868025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416359332029921371575824033 312269499022441028681868025)
      ·
        refine ⟨234202124266830771511401019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312269499022441028681868025 234202124266830771511401019)
        ·
          refine ⟨351303186400246157267101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234202124266830771511401019 351303186400246157267101529)
          ·
            refine ⟨263477389800184617950326147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351303186400246157267101529 263477389800184617950326147)
            ·
              refine ⟨395216084700276926925489221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263477389800184617950326147 395216084700276926925489221)
              ·
                refine ⟨74103015881301923798529229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395216084700276926925489221 74103015881301923798529229)
                ·
                  refine ⟨27788630955488221424448461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74103015881301923798529229 27788630955488221424448461)
                  ·
                    refine ⟨10420736608308083034168173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27788630955488221424448461 10420736608308083034168173)
                    ·
                      refine ⟨3907776228115531137813065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420736608308083034168173 3907776228115531137813065)
                      ·
                        rfl

theorem cell23_7610367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_7610367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610367 prefixEnd_7610367 := by exact prefixLift 7610367
  have htrace : WordTrace (prefixWord ++ tailWord_7610367) baseStart_7610367 baseEnd_7610367 := by
    simpa [prefixWord, tailWord_7610367, baseEnd_7610367] using wordTrace_append hprefix tailTrace_7610367
  have hstable : (prefixWord ++ tailWord_7610367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610367).length < 2 ^ (prefixWord ++ tailWord_7610367).sum := by decide
  have hdescent : baseEnd_7610367 < baseStart_7610367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610378 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_7610378 : Nat := 118140960795 + 7610378 * 2 ^ 59
def prefixEnd_7610378 : Nat := 4983230072969 + 3 ^ 40 * 7610378 * 2
def baseEnd_7610378 : Nat := 1302593958800910198258505

theorem tailTrace_7610378 : CollatzResearch.WordTrace tailWord_7610378 prefixEnd_7610378 1302593958800910198258505 := by
  unfold tailWord_7610378
  simp only [CollatzResearch.WordTrace]
  refine ⟨69393322305726932482299947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185048859481938486619466525 69393322305726932482299947)
  ·
    refine ⟨104089983458590398723449921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69393322305726932482299947 104089983458590398723449921)
    ·
      refine ⟨78067487593942799042587441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104089983458590398723449921 78067487593942799042587441)
      ·
        refine ⟨58550615695457099281940581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78067487593942799042587441 58550615695457099281940581)
        ·
          refine ⟨10978240442898206115363859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58550615695457099281940581 10978240442898206115363859)
          ·
            refine ⟨16467360664347309173045789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978240442898206115363859 16467360664347309173045789)
            ·
              refine ⟨6175260249130240939892171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16467360664347309173045789 6175260249130240939892171)
              ·
                refine ⟨9262890373695361409838257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175260249130240939892171 9262890373695361409838257)
                ·
                  refine ⟨6947167780271521057378693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9262890373695361409838257 6947167780271521057378693)
                  ·
                    refine ⟨1302593958800910198258505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947167780271521057378693 1302593958800910198258505)
                    ·
                      rfl

theorem cell23_7610378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_7610378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610378 prefixEnd_7610378 := by exact prefixLift 7610378
  have htrace : WordTrace (prefixWord ++ tailWord_7610378) baseStart_7610378 baseEnd_7610378 := by
    simpa [prefixWord, tailWord_7610378, baseEnd_7610378] using wordTrace_append hprefix tailTrace_7610378
  have hstable : (prefixWord ++ tailWord_7610378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610378).length < 2 ^ (prefixWord ++ tailWord_7610378).sum := by decide
  have hdescent : baseEnd_7610378 < baseStart_7610378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610391 : List Nat := [1, 1, 3, 5, 2, 2, 2, 7]
def baseStart_7610391 : Nat := 118140960795 + 7610391 * 2 ^ 59
def prefixEnd_7610391 : Nat := 4983230072969 + 3 ^ 40 * 7610391 * 2
def baseEnd_7610391 : Nat := 144732909320416260885665

theorem tailTrace_7610391 : CollatzResearch.WordTrace tailWord_7610391 prefixEnd_7610391 144732909320416260885665 := by
  unfold tailWord_7610391
  simp only [CollatzResearch.WordTrace]
  refine ⟨277573763371860633149423027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185049175581240422099615351 277573763371860633149423027)
  ·
    refine ⟨416360645057790949724134541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277573763371860633149423027 416360645057790949724134541)
    ·
      refine ⟨156135241896671606146550453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416360645057790949724134541 156135241896671606146550453)
      ·
        refine ⟨14637678927812963076239105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156135241896671606146550453 14637678927812963076239105)
        ·
          refine ⟨10978259195859722307179329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14637678927812963076239105 10978259195859722307179329)
          ·
            refine ⟨8233694396894791730384497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10978259195859722307179329 8233694396894791730384497)
            ·
              refine ⟨6175270797671093797788373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8233694396894791730384497 6175270797671093797788373)
              ·
                refine ⟨144732909320416260885665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6175270797671093797788373 144732909320416260885665)
                ·
                  rfl

theorem cell23_7610391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 7].length) (baseStart_7610391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610391 prefixEnd_7610391 := by exact prefixLift 7610391
  have htrace : WordTrace (prefixWord ++ tailWord_7610391) baseStart_7610391 baseEnd_7610391 := by
    simpa [prefixWord, tailWord_7610391, baseEnd_7610391] using wordTrace_append hprefix tailTrace_7610391
  have hstable : (prefixWord ++ tailWord_7610391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610391).length < 2 ^ (prefixWord ++ tailWord_7610391).sum := by decide
  have hdescent : baseEnd_7610391 < baseStart_7610391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3]
def baseStart_7610427 : Nat := 118140960795 + 7610427 * 2 ^ 59
def prefixEnd_7610427 : Nat := 4983230072969 + 3 ^ 40 * 7610427 * 2
def baseEnd_7610427 : Nat := 3907807036954800903062789

theorem tailTrace_7610427 : CollatzResearch.WordTrace tailWord_7610427 prefixEnd_7610427 3907807036954800903062789 := by
  unfold tailWord_7610427
  simp only [CollatzResearch.WordTrace]
  refine ⟨277575076399730211297733535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185050050933153474198489023 277575076399730211297733535)
  ·
    refine ⟨416362614599595316946600303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277575076399730211297733535 416362614599595316946600303)
    ·
      refine ⟨624543921899392975419900455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416362614599595316946600303 624543921899392975419900455)
      ·
        refine ⟨936815882849089463129850683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624543921899392975419900455 936815882849089463129850683)
        ·
          refine ⟨1405223824273634194694776025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936815882849089463129850683 1405223824273634194694776025)
          ·
            refine ⟨1053917868205225646021082019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405223824273634194694776025 1053917868205225646021082019)
            ·
              refine ⟨1580876802307838469031623029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053917868205225646021082019 1580876802307838469031623029)
              ·
                refine ⟨148207200216359856471714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580876802307838469031623029 148207200216359856471714659)
                ·
                  refine ⟨222310800324539784707571989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148207200216359856471714659 222310800324539784707571989)
                  ·
                    refine ⟨10420818765212802408167437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222310800324539784707571989 10420818765212802408167437)
                    ·
                      refine ⟨3907807036954800903062789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10420818765212802408167437 3907807036954800903062789)
                      ·
                        rfl

theorem cell23_7610427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 3].length) (baseStart_7610427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610427 prefixEnd_7610427 := by exact prefixLift 7610427
  have htrace : WordTrace (prefixWord ++ tailWord_7610427) baseStart_7610427 baseEnd_7610427 := by
    simpa [prefixWord, tailWord_7610427, baseEnd_7610427] using wordTrace_append hprefix tailTrace_7610427
  have hstable : (prefixWord ++ tailWord_7610427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610427).length < 2 ^ (prefixWord ++ tailWord_7610427).sum := by decide
  have hdescent : baseEnd_7610427 < baseStart_7610427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610437 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_7610437 : Nat := 118140960795 + 7610437 * 2 ^ 59
def prefixEnd_7610437 : Nat := 4983230072969 + 3 ^ 40 * 7610437 * 2
def baseEnd_7610437 : Nat := 3907812171761345863937743

theorem tailTrace_7610437 : CollatzResearch.WordTrace tailWord_7610437 prefixEnd_7610437 3907812171761345863937743 := by
  unfold tailWord_7610437
  simp only [CollatzResearch.WordTrace]
  refine ⟨277575441129693983005597565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185050294086462655337065043 277575441129693983005597565)
  ·
    refine ⟨104090790423635243627099087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277575441129693983005597565 104090790423635243627099087)
    ·
      refine ⟨156136185635452865440648631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104090790423635243627099087 156136185635452865440648631)
      ·
        refine ⟨234204278453179298160972947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156136185635452865440648631 234204278453179298160972947)
        ·
          refine ⟨351306417679768947241459421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234204278453179298160972947 351306417679768947241459421)
          ·
            refine ⟨131739906629913355215547283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351306417679768947241459421 131739906629913355215547283)
            ·
              refine ⟨197609859944870032823320925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131739906629913355215547283 197609859944870032823320925)
              ·
                refine ⟨74103697479326262308745347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197609859944870032823320925 74103697479326262308745347)
                ·
                  refine ⟨111155546218989393463118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74103697479326262308745347 111155546218989393463118021)
                  ·
                    refine ⟨20841664916060511274334629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111155546218989393463118021 20841664916060511274334629)
                    ·
                      refine ⟨3907812171761345863937743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20841664916060511274334629 3907812171761345863937743)
                      ·
                        rfl

theorem cell23_7610437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_7610437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610437 prefixEnd_7610437 := by exact prefixLift 7610437
  have htrace : WordTrace (prefixWord ++ tailWord_7610437) baseStart_7610437 baseEnd_7610437 := by
    simpa [prefixWord, tailWord_7610437, baseEnd_7610437] using wordTrace_append hprefix tailTrace_7610437
  have hstable : (prefixWord ++ tailWord_7610437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610437).length < 2 ^ (prefixWord ++ tailWord_7610437).sum := by decide
  have hdescent : baseEnd_7610437 < baseStart_7610437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610461 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7610461 : Nat := 118140960795 + 7610461 * 2 ^ 59
def prefixEnd_7610461 : Nat := 4983230072969 + 3 ^ 40 * 7610461 * 2
def baseEnd_7610461 : Nat := 3907824495297053770037633

theorem tailTrace_7610461 : CollatzResearch.WordTrace tailWord_7610461 prefixEnd_7610461 3907824495297053770037633 := by
  unfold tailWord_7610461
  simp only [CollatzResearch.WordTrace]
  refine ⟨277576316481607035104471237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185050877654404690069647491 277576316481607035104471237)
  ·
    refine ⟨52045559340301319082088357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277576316481607035104471237 52045559340301319082088357)
    ·
      refine ⟨9758542376306497327891567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52045559340301319082088357 9758542376306497327891567)
      ·
        refine ⟨14637813564459745991837351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758542376306497327891567 14637813564459745991837351)
        ·
          refine ⟨21956720346689618987756027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14637813564459745991837351 21956720346689618987756027)
          ·
            refine ⟨32935080520034428481634041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21956720346689618987756027 32935080520034428481634041)
            ·
              refine ⟨24701310390025821361225531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32935080520034428481634041 24701310390025821361225531)
              ·
                refine ⟨37051965585038732041838297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24701310390025821361225531 37051965585038732041838297)
                ·
                  refine ⟨27788974188779049031378723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37051965585038732041838297 27788974188779049031378723)
                  ·
                    refine ⟨41683461283168573547068085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27788974188779049031378723 41683461283168573547068085)
                    ·
                      refine ⟨3907824495297053770037633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41683461283168573547068085 3907824495297053770037633)
                      ·
                        rfl

theorem cell23_7610461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7610461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610461 prefixEnd_7610461 := by exact prefixLift 7610461
  have htrace : WordTrace (prefixWord ++ tailWord_7610461) baseStart_7610461 baseEnd_7610461 := by
    simpa [prefixWord, tailWord_7610461, baseEnd_7610461] using wordTrace_append hprefix tailTrace_7610461
  have hstable : (prefixWord ++ tailWord_7610461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610461).length < 2 ^ (prefixWord ++ tailWord_7610461).sum := by decide
  have hdescent : baseEnd_7610461 < baseStart_7610461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610554 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_7610554 : Nat := 118140960795 + 7610554 * 2 ^ 59
def prefixEnd_7610554 : Nat := 4983230072969 + 3 ^ 40 * 7610554 * 2
def baseEnd_7610554 : Nat := 434208027666435767352745

theorem tailTrace_7610554 : CollatzResearch.WordTrace tailWord_7610554 prefixEnd_7610554 434208027666435767352745 := by
  unfold tailWord_7610554
  simp only [CollatzResearch.WordTrace]
  refine ⟨69394927117567527996901679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185053138980180074658404477 69394927117567527996901679)
  ·
    refine ⟨104092390676351291995352519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69394927117567527996901679 104092390676351291995352519)
    ·
      refine ⟨156138586014526937993028779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104092390676351291995352519 156138586014526937993028779)
      ·
        refine ⟨234207879021790406989543169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156138586014526937993028779 234207879021790406989543169)
        ·
          refine ⟨175655909266342805242157377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234207879021790406989543169 175655909266342805242157377)
          ·
            refine ⟨131741931949757103931618033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175655909266342805242157377 131741931949757103931618033)
            ·
              refine ⟨98806448962317827948713525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131741931949757103931618033 98806448962317827948713525)
              ·
                refine ⟨9263104590217296370191893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98806448962317827948713525 9263104590217296370191893)
                ·
                  refine ⟨434208027666435767352745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9263104590217296370191893 434208027666435767352745)
                  ·
                    rfl

theorem cell23_7610554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_7610554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610554 prefixEnd_7610554 := by exact prefixLift 7610554
  have htrace : WordTrace (prefixWord ++ tailWord_7610554) baseStart_7610554 baseEnd_7610554 := by
    simpa [prefixWord, tailWord_7610554, baseEnd_7610554] using wordTrace_append hprefix tailTrace_7610554
  have hstable : (prefixWord ++ tailWord_7610554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610554).length < 2 ^ (prefixWord ++ tailWord_7610554).sum := by decide
  have hdescent : baseEnd_7610554 < baseStart_7610554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610605 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7610605 : Nat := 118140960795 + 7610605 * 2 ^ 59
def prefixEnd_7610605 : Nat := 4983230072969 + 3 ^ 40 * 7610605 * 2
def baseEnd_7610605 : Nat := 434210937390144578515219

theorem tailTrace_7610605 : CollatzResearch.WordTrace tailWord_7610605 prefixEnd_7610605 434210937390144578515219 := by
  unfold tailWord_7610605
  simp only [CollatzResearch.WordTrace]
  refine ⟨277581568593085347697713269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185054379062056898465142179 277581568593085347697713269)
  ·
    refine ⟨26023272055601751346660619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277581568593085347697713269 26023272055601751346660619)
    ·
      refine ⟨39034908083402627019990929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26023272055601751346660619 39034908083402627019990929)
      ·
        refine ⟨29276181062551970264993197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39034908083402627019990929 29276181062551970264993197)
        ·
          refine ⟨10978567898456988849372449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29276181062551970264993197 10978567898456988849372449)
          ·
            refine ⟨8233925923842741637029337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10978567898456988849372449 8233925923842741637029337)
            ·
              refine ⟨6175444442882056227772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8233925923842741637029337 6175444442882056227772003)
              ·
                refine ⟨9263166664323084341658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175444442882056227772003 9263166664323084341658005)
                ·
                  refine ⟨434210937390144578515219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9263166664323084341658005 434210937390144578515219)
                  ·
                    rfl

theorem cell23_7610605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7610605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610605 prefixEnd_7610605 := by exact prefixLift 7610605
  have htrace : WordTrace (prefixWord ++ tailWord_7610605) baseStart_7610605 baseEnd_7610605 := by
    simpa [prefixWord, tailWord_7610605, baseEnd_7610605] using wordTrace_append hprefix tailTrace_7610605
  have hstable : (prefixWord ++ tailWord_7610605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610605).length < 2 ^ (prefixWord ++ tailWord_7610605).sum := by decide
  have hdescent : baseEnd_7610605 < baseStart_7610605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610618 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_7610618 : Nat := 118140960795 + 7610618 * 2 ^ 59
def prefixEnd_7610618 : Nat := 4983230072969 + 3 ^ 40 * 7610618 * 2
def baseEnd_7610618 : Nat := 1302635037253269885258137

theorem tailTrace_7610618 : CollatzResearch.WordTrace tailWord_7610618 prefixEnd_7610618 1302635037253269885258137 := by
  unfold tailWord_7610618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69395510685509562729484127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185054695161358833945291005 69395510685509562729484127)
  ·
    refine ⟨104093266028264344094226191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69395510685509562729484127 104093266028264344094226191)
    ·
      refine ⟨156139899042396516141339287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104093266028264344094226191 156139899042396516141339287)
      ·
        refine ⟨234209848563594774212008931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156139899042396516141339287 234209848563594774212008931)
        ·
          refine ⟨351314772845392161318013397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234209848563594774212008931 351314772845392161318013397)
          ·
            refine ⟨8233939988563878780890939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 351314772845392161318013397 8233939988563878780890939)
            ·
              refine ⟨12350909982845818171336409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8233939988563878780890939 12350909982845818171336409)
              ·
                refine ⟨9263182487134363628502307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350909982845818171336409 9263182487134363628502307)
                ·
                  refine ⟨13894773730701545442753461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263182487134363628502307 13894773730701545442753461)
                  ·
                    refine ⟨1302635037253269885258137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13894773730701545442753461 1302635037253269885258137)
                    ·
                      rfl

theorem cell23_7610618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_7610618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610618 prefixEnd_7610618 := by exact prefixLift 7610618
  have htrace : WordTrace (prefixWord ++ tailWord_7610618) baseStart_7610618 baseEnd_7610618 := by
    simpa [prefixWord, tailWord_7610618, baseEnd_7610618] using wordTrace_append hprefix tailTrace_7610618
  have hstable : (prefixWord ++ tailWord_7610618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610618).length < 2 ^ (prefixWord ++ tailWord_7610618).sum := by decide
  have hdescent : baseEnd_7610618 < baseStart_7610618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610621 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_7610621 : Nat := 118140960795 + 7610621 * 2 ^ 59
def prefixEnd_7610621 : Nat := 4983230072969 + 3 ^ 40 * 7610621 * 2
def baseEnd_7610621 : Nat := 3907906652201773144036897

theorem tailTrace_7610621 : CollatzResearch.WordTrace tailWord_7610621 prefixEnd_7610621 3907906652201773144036897 := by
  unfold tailWord_7610621
  simp only [CollatzResearch.WordTrace]
  refine ⟨277582152161027382430295717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185054768107351588286863811 277582152161027382430295717)
  ·
    refine ⟨52046653530192634205680447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277582152161027382430295717 52046653530192634205680447)
    ·
      refine ⟨78069980295288951308520671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52046653530192634205680447 78069980295288951308520671)
      ·
        refine ⟨117104970442933426962781007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78069980295288951308520671 117104970442933426962781007)
        ·
          refine ⟨175657455664400140444171511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117104970442933426962781007 175657455664400140444171511)
          ·
            refine ⟨263486183496600210666257267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175657455664400140444171511 263486183496600210666257267)
            ·
              refine ⟨395229275244900315999385901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263486183496600210666257267 395229275244900315999385901)
              ·
                refine ⟨148210978216837618499769713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395229275244900315999385901 148210978216837618499769713)
                ·
                  refine ⟨111158233662628213874827285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148210978216837618499769713 111158233662628213874827285)
                  ·
                    refine ⟨5210542202935697525382529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111158233662628213874827285 5210542202935697525382529)
                    ·
                      refine ⟨3907906652201773144036897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210542202935697525382529 3907906652201773144036897)
                      ·
                        rfl

theorem cell23_7610621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_7610621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610621 prefixEnd_7610621 := by exact prefixLift 7610621
  have htrace : WordTrace (prefixWord ++ tailWord_7610621) baseStart_7610621 baseEnd_7610621 := by
    simpa [prefixWord, tailWord_7610621, baseEnd_7610621] using wordTrace_append hprefix tailTrace_7610621
  have hstable : (prefixWord ++ tailWord_7610621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610621).length < 2 ^ (prefixWord ++ tailWord_7610621).sum := by decide
  have hdescent : baseEnd_7610621 < baseStart_7610621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610624 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_7610624 : Nat := 118140960795 + 7610624 * 2 ^ 59
def prefixEnd_7610624 : Nat := 4983230072969 + 3 ^ 40 * 7610624 * 2
def baseEnd_7610624 : Nat := 3907908192643736632299383

theorem tailTrace_7610624 : CollatzResearch.WordTrace tailWord_7610624 prefixEnd_7610624 3907908192643736632299383 := by
  unfold tailWord_7610624
  simp only [CollatzResearch.WordTrace]
  refine ⟨138791130790008256971327463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185054841053344342628436617 138791130790008256971327463)
  ·
    refine ⟨208186696185012385456991195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138791130790008256971327463 208186696185012385456991195)
    ·
      refine ⟨312280044277518578185486793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208186696185012385456991195 312280044277518578185486793)
      ·
        refine ⟨234210033208138933639115095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312280044277518578185486793 234210033208138933639115095)
        ·
          refine ⟨351315049812208400458672643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234210033208138933639115095 351315049812208400458672643)
          ·
            refine ⟨526972574718312600688008965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351315049812208400458672643 526972574718312600688008965)
            ·
              refine ⟨98807357759683612629001681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526972574718312600688008965 98807357759683612629001681)
              ·
                refine ⟨74105518319762709471751261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98807357759683612629001681 74105518319762709471751261)
                ·
                  refine ⟨27789569369911016051906723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74105518319762709471751261 27789569369911016051906723)
                  ·
                    refine ⟨41684354054866524077860085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27789569369911016051906723 41684354054866524077860085)
                    ·
                      refine ⟨3907908192643736632299383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41684354054866524077860085 3907908192643736632299383)
                      ·
                        rfl

theorem cell23_7610624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_7610624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610624 prefixEnd_7610624 := by exact prefixLift 7610624
  have htrace : WordTrace (prefixWord ++ tailWord_7610624) baseStart_7610624 baseEnd_7610624 := by
    simpa [prefixWord, tailWord_7610624, baseEnd_7610624] using wordTrace_append hprefix tailTrace_7610624
  have hstable : (prefixWord ++ tailWord_7610624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610624).length < 2 ^ (prefixWord ++ tailWord_7610624).sum := by decide
  have hdescent : baseEnd_7610624 < baseStart_7610624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610641 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_7610641 : Nat := 118140960795 + 7610641 * 2 ^ 59
def prefixEnd_7610641 : Nat := 4983230072969 + 3 ^ 40 * 7610641 * 2
def baseEnd_7610641 : Nat := 3907916921814863065786805

theorem tailTrace_7610641 : CollatzResearch.WordTrace tailWord_7610641 prefixEnd_7610641 3907916921814863065786805 := by
  unfold tailWord_7610641
  simp only [CollatzResearch.WordTrace]
  refine ⟨277582881620954925846023777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185055254413969950564015851 277582881620954925846023777)
  ·
    refine ⟨208187161215716194384517833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277582881620954925846023777 208187161215716194384517833)
    ·
      refine ⟨156140370911787145788388375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208187161215716194384517833 156140370911787145788388375)
      ·
        refine ⟨234210556367680718682582563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156140370911787145788388375 234210556367680718682582563)
        ·
          refine ⟨351315834551521078023873845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234210556367680718682582563 351315834551521078023873845)
          ·
            refine ⟨32935859489205101064738173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351315834551521078023873845 32935859489205101064738173)
            ·
              refine ⟨12350947308451912899276815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32935859489205101064738173 12350947308451912899276815)
              ·
                refine ⟨18526420962677869348915223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12350947308451912899276815 18526420962677869348915223)
                ·
                  refine ⟨27789631444016804023372835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18526420962677869348915223 27789631444016804023372835)
                  ·
                    refine ⟨41684447166025206035059253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27789631444016804023372835 41684447166025206035059253)
                    ·
                      refine ⟨3907916921814863065786805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41684447166025206035059253 3907916921814863065786805)
                      ·
                        rfl

theorem cell23_7610641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_7610641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610641 prefixEnd_7610641 := by exact prefixLift 7610641
  have htrace : WordTrace (prefixWord ++ tailWord_7610641) baseStart_7610641 baseEnd_7610641 := by
    simpa [prefixWord, tailWord_7610641, baseEnd_7610641] using wordTrace_append hprefix tailTrace_7610641
  have hstable : (prefixWord ++ tailWord_7610641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610641).length < 2 ^ (prefixWord ++ tailWord_7610641).sum := by decide
  have hdescent : baseEnd_7610641 < baseStart_7610641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610648 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_7610648 : Nat := 118140960795 + 7610648 * 2 ^ 59
def prefixEnd_7610648 : Nat := 4983230072969 + 3 ^ 40 * 7610648 * 2
def baseEnd_7610648 : Nat := 1302640172059814846133091

theorem tailTrace_7610648 : CollatzResearch.WordTrace tailWord_7610648 prefixEnd_7610648 1302640172059814846133091 := by
  unfold tailWord_7610648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138791568465964783020764299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185055424621286377361019065 138791568465964783020764299)
  ·
    refine ⟨208187352698947174531146449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138791568465964783020764299 208187352698947174531146449)
    ·
      refine ⟨156140514524210380898359837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208187352698947174531146449 156140514524210380898359837)
      ·
        refine ⟨58552692946578892836884939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156140514524210380898359837 58552692946578892836884939)
        ·
          refine ⟨87829039419868339255327409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58552692946578892836884939 87829039419868339255327409)
          ·
            refine ⟨65871779564901254441495557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87829039419868339255327409 65871779564901254441495557)
            ·
              refine ⟨12350958668418985207780417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65871779564901254441495557 12350958668418985207780417)
              ·
                refine ⟨9263219001314238905835313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12350958668418985207780417 9263219001314238905835313)
                ·
                  refine ⟨6947414250985679179376485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9263219001314238905835313 6947414250985679179376485)
                  ·
                    refine ⟨1302640172059814846133091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947414250985679179376485 1302640172059814846133091)
                    ·
                      rfl

theorem cell23_7610648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_7610648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610648 prefixEnd_7610648 := by exact prefixLift 7610648
  have htrace : WordTrace (prefixWord ++ tailWord_7610648) baseStart_7610648 baseEnd_7610648 := by
    simpa [prefixWord, tailWord_7610648, baseEnd_7610648] using wordTrace_append hprefix tailTrace_7610648
  have hstable : (prefixWord ++ tailWord_7610648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610648).length < 2 ^ (prefixWord ++ tailWord_7610648).sum := by decide
  have hdescent : baseEnd_7610648 < baseStart_7610648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610658 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_7610658 : Nat := 118140960795 + 7610658 * 2 ^ 59
def prefixEnd_7610658 : Nat := 4983230072969 + 3 ^ 40 * 7610658 * 2
def baseEnd_7610658 : Nat := 3907925650985989499274227

theorem tailTrace_7610658 : CollatzResearch.WordTrace tailWord_7610658 prefixEnd_7610658 3907925650985989499274227 := by
  unfold tailWord_7610658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69395875415473334437348157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185055667774595558499595085 69395875415473334437348157)
  ·
    refine ⟨26023453280802500414005559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69395875415473334437348157 26023453280802500414005559)
    ·
      refine ⟨39035179921203750621008339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26023453280802500414005559 39035179921203750621008339)
      ·
        refine ⟨58552769881805625931512509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39035179921203750621008339 58552769881805625931512509)
        ·
          refine ⟨21957288705677109724317191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58552769881805625931512509 21957288705677109724317191)
          ·
            refine ⟨32935933058515664586475787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21957288705677109724317191 32935933058515664586475787)
            ·
              refine ⟨49403899587773496879713681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32935933058515664586475787 49403899587773496879713681)
              ·
                refine ⟨37052924690830122659785261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49403899587773496879713681 37052924690830122659785261)
                ·
                  refine ⟨13894846759061295997419473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37052924690830122659785261 13894846759061295997419473)
                  ·
                    refine ⟨10421135069295971998064605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13894846759061295997419473 10421135069295971998064605)
                    ·
                      refine ⟨3907925650985989499274227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421135069295971998064605 3907925650985989499274227)
                      ·
                        rfl

theorem cell23_7610658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_7610658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610658 prefixEnd_7610658 := by exact prefixLift 7610658
  have htrace : WordTrace (prefixWord ++ tailWord_7610658) baseStart_7610658 baseEnd_7610658 := by
    simpa [prefixWord, tailWord_7610658, baseEnd_7610658] using wordTrace_append hprefix tailTrace_7610658
  have hstable : (prefixWord ++ tailWord_7610658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610658).length < 2 ^ (prefixWord ++ tailWord_7610658).sum := by decide
  have hdescent : baseEnd_7610658 < baseStart_7610658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610671 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_7610671 : Nat := 118140960795 + 7610671 * 2 ^ 59
def prefixEnd_7610671 : Nat := 4983230072969 + 3 ^ 40 * 7610671 * 2
def baseEnd_7610671 : Nat := 3907932326234497948411667

theorem tailTrace_7610671 : CollatzResearch.WordTrace tailWord_7610671 prefixEnd_7610671 3907932326234497948411667 := by
  unfold tailWord_7610671
  simp only [CollatzResearch.WordTrace]
  refine ⟨277583975810846240969615867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185055983873897493979743911 277583975810846240969615867)
  ·
    refine ⟨416375963716269361454423801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277583975810846240969615867 416375963716269361454423801)
    ·
      refine ⟨312281972787202021090817851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416375963716269361454423801 312281972787202021090817851)
      ·
        refine ⟨468422959180803031636226777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312281972787202021090817851 468422959180803031636226777)
        ·
          refine ⟨351317219385602273727170083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468422959180803031636226777 351317219385602273727170083)
          ·
            refine ⟨526975829078403410590755125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351317219385602273727170083 526975829078403410590755125)
            ·
              refine ⟨49403983976100319742883293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 526975829078403410590755125 49403983976100319742883293)
              ·
                refine ⟨18526493991037619903581235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49403983976100319742883293 18526493991037619903581235)
                ·
                  refine ⟨27789740986556429855371853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18526493991037619903581235 27789740986556429855371853)
                  ·
                    refine ⟨10421152869958661195764445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27789740986556429855371853 10421152869958661195764445)
                    ·
                      refine ⟨3907932326234497948411667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421152869958661195764445 3907932326234497948411667)
                      ·
                        rfl

theorem cell23_7610671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_7610671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610671 prefixEnd_7610671 := by exact prefixLift 7610671
  have htrace : WordTrace (prefixWord ++ tailWord_7610671) baseStart_7610671 baseEnd_7610671 := by
    simpa [prefixWord, tailWord_7610671, baseEnd_7610671] using wordTrace_append hprefix tailTrace_7610671
  have hstable : (prefixWord ++ tailWord_7610671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610671).length < 2 ^ (prefixWord ++ tailWord_7610671).sum := by decide
  have hdescent : baseEnd_7610671 < baseStart_7610671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610689 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7610689 : Nat := 118140960795 + 7610689 * 2 ^ 59
def prefixEnd_7610689 : Nat := 4983230072969 + 3 ^ 40 * 7610689 * 2
def baseEnd_7610689 : Nat := 3907941568886278877986585

theorem tailTrace_7610689 : CollatzResearch.WordTrace tailWord_7610689 prefixEnd_7610689 3907941568886278877986585 := by
  unfold tailWord_7610689
  simp only [CollatzResearch.WordTrace]
  refine ⟨277584632324781030043771121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185056421549854020029180747 277584632324781030043771121)
  ·
    refine ⟨208188474243585772532828341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277584632324781030043771121 208188474243585772532828341)
    ·
      refine ⟨19517669460336166174952657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208188474243585772532828341 19517669460336166174952657)
      ·
        refine ⟨14638252095252124631214493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19517669460336166174952657 14638252095252124631214493)
        ·
          refine ⟨5489344535719546736705435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14638252095252124631214493 5489344535719546736705435)
          ·
            refine ⟨8234016803579320105058153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489344535719546736705435 8234016803579320105058153)
            ·
              refine ⟨6175512602684490078793615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234016803579320105058153 6175512602684490078793615)
              ·
                refine ⟨9263268904026735118190423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175512602684490078793615 9263268904026735118190423)
                ·
                  refine ⟨13894903356040102677285635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263268904026735118190423 13894903356040102677285635)
                  ·
                    refine ⟨20842355034060154015928453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13894903356040102677285635 20842355034060154015928453)
                    ·
                      refine ⟨3907941568886278877986585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20842355034060154015928453 3907941568886278877986585)
                      ·
                        rfl

theorem cell23_7610689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7610689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610689 prefixEnd_7610689 := by exact prefixLift 7610689
  have htrace : WordTrace (prefixWord ++ tailWord_7610689) baseStart_7610689 baseEnd_7610689 := by
    simpa [prefixWord, tailWord_7610689, baseEnd_7610689] using wordTrace_append hprefix tailTrace_7610689
  have hstable : (prefixWord ++ tailWord_7610689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610689).length < 2 ^ (prefixWord ++ tailWord_7610689).sum := by decide
  have hdescent : baseEnd_7610689 < baseStart_7610689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610692 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7610692 : Nat := 118140960795 + 7610692 * 2 ^ 59
def prefixEnd_7610692 : Nat := 4983230072969 + 3 ^ 40 * 7610692 * 2
def baseEnd_7610692 : Nat := 3907943109328242366249071

theorem tailTrace_7610692 : CollatzResearch.WordTrace tailWord_7610692 prefixEnd_7610692 3907943109328242366249071 := by
  unfold tailWord_7610692
  simp only [CollatzResearch.WordTrace]
  refine ⟨138792370871885080778065165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185056494495846774370753553 138792370871885080778065165)
  ·
    refine ⟨52047139076956905291774437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138792370871885080778065165 52047139076956905291774437)
    ·
      refine ⟨9758838576929419742207707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52047139076956905291774437 9758838576929419742207707)
      ·
        refine ⟨14638257865394129613311561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758838576929419742207707 14638257865394129613311561)
        ·
          refine ⟨10978693399045597209983671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14638257865394129613311561 10978693399045597209983671)
          ·
            refine ⟨16468040098568395814975507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978693399045597209983671 16468040098568395814975507)
            ·
              refine ⟨24702060147852593722463261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468040098568395814975507 24702060147852593722463261)
              ·
                refine ⟨9263272555444722645923723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24702060147852593722463261 9263272555444722645923723)
                ·
                  refine ⟨13894908833167083968885585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263272555444722645923723 13894908833167083968885585)
                  ·
                    refine ⟨10421181624875312976664189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13894908833167083968885585 10421181624875312976664189)
                    ·
                      refine ⟨3907943109328242366249071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421181624875312976664189 3907943109328242366249071)
                      ·
                        rfl

theorem cell23_7610692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7610692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610692 prefixEnd_7610692 := by exact prefixLift 7610692
  have htrace : WordTrace (prefixWord ++ tailWord_7610692) baseStart_7610692 baseEnd_7610692 := by
    simpa [prefixWord, tailWord_7610692, baseEnd_7610692] using wordTrace_append hprefix tailTrace_7610692
  have hstable : (prefixWord ++ tailWord_7610692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610692).length < 2 ^ (prefixWord ++ tailWord_7610692).sum := by decide
  have hdescent : baseEnd_7610692 < baseStart_7610692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610705 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_7610705 : Nat := 118140960795 + 7610705 * 2 ^ 59
def prefixEnd_7610705 : Nat := 4983230072969 + 3 ^ 40 * 7610705 * 2
def baseEnd_7610705 : Nat := 3907949784576750815386511

theorem tailTrace_7610705 : CollatzResearch.WordTrace tailWord_7610705 prefixEnd_7610705 3907949784576750815386511 := by
  unfold tailWord_7610705
  simp only [CollatzResearch.WordTrace]
  refine ⟨277585215892723064776353569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185056810595148709850902379 277585215892723064776353569)
  ·
    refine ⟨208188911919542298582265177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277585215892723064776353569 208188911919542298582265177)
    ·
      refine ⟨156141683939656723936698883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208188911919542298582265177 156141683939656723936698883)
      ·
        refine ⟨234212525909485085905048325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156141683939656723936698883 234212525909485085905048325)
        ·
          refine ⟨43914848608028453607196561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234212525909485085905048325 43914848608028453607196561)
          ·
            refine ⟨32936136456021340205397421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43914848608028453607196561 32936136456021340205397421)
            ·
              refine ⟨12351051171008002577024033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32936136456021340205397421 12351051171008002577024033)
              ·
                refine ⟨9263288378256001932768025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351051171008002577024033 9263288378256001932768025)
                ·
                  refine ⟨6947466283692001449576019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9263288378256001932768025 6947466283692001449576019)
                  ·
                    refine ⟨10421199425538002174364029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6947466283692001449576019 10421199425538002174364029)
                    ·
                      refine ⟨3907949784576750815386511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421199425538002174364029 3907949784576750815386511)
                      ·
                        rfl

theorem cell23_7610705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_7610705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610705 prefixEnd_7610705 := by exact prefixLift 7610705
  have htrace : WordTrace (prefixWord ++ tailWord_7610705) baseStart_7610705 baseEnd_7610705 := by
    simpa [prefixWord, tailWord_7610705, baseEnd_7610705] using wordTrace_append hprefix tailTrace_7610705
  have hstable : (prefixWord ++ tailWord_7610705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610705).length < 2 ^ (prefixWord ++ tailWord_7610705).sum := by decide
  have hdescent : baseEnd_7610705 < baseStart_7610705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610732 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_7610732 : Nat := 118140960795 + 7610732 * 2 ^ 59
def prefixEnd_7610732 : Nat := 4983230072969 + 3 ^ 40 * 7610732 * 2
def baseEnd_7610732 : Nat := 3907963648554422209748887

theorem tailTrace_7610732 : CollatzResearch.WordTrace tailWord_7610732 prefixEnd_7610732 3907963648554422209748887 := by
  unfold tailWord_7610732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138793100331812624193793225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185057467109083498925057633 138793100331812624193793225)
  ·
    refine ⟨104094825248859468145344919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138793100331812624193793225 104094825248859468145344919)
    ·
      refine ⟨156142237873289202218017379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104094825248859468145344919 156142237873289202218017379)
      ·
        refine ⟨234213356809933803327026069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156142237873289202218017379 234213356809933803327026069)
        ·
          refine ⟨10978751100465647030954347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234213356809933803327026069 10978751100465647030954347)
          ·
            refine ⟨16468126650698470546431521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10978751100465647030954347 16468126650698470546431521)
            ·
              refine ⟨12351094988023852909823641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16468126650698470546431521 12351094988023852909823641)
              ·
                refine ⟨9263321241017889682367731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351094988023852909823641 9263321241017889682367731)
                ·
                  refine ⟨13894981861526834523551597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263321241017889682367731 13894981861526834523551597)
                  ·
                    refine ⟨5210618198072562946331849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13894981861526834523551597 5210618198072562946331849)
                    ·
                      refine ⟨3907963648554422209748887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210618198072562946331849 3907963648554422209748887)
                      ·
                        rfl

theorem cell23_7610732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_7610732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610732 prefixEnd_7610732 := by exact prefixLift 7610732
  have htrace : WordTrace (prefixWord ++ tailWord_7610732) baseStart_7610732 baseEnd_7610732 := by
    simpa [prefixWord, tailWord_7610732, baseEnd_7610732] using wordTrace_append hprefix tailTrace_7610732
  have hstable : (prefixWord ++ tailWord_7610732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610732).length < 2 ^ (prefixWord ++ tailWord_7610732).sum := by decide
  have hdescent : baseEnd_7610732 < baseStart_7610732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610831 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_7610831 : Nat := 118140960795 + 7610831 * 2 ^ 59
def prefixEnd_7610831 : Nat := 4983230072969 + 3 ^ 40 * 7610831 * 2
def baseEnd_7610831 : Nat := 3908014483139217322410931

theorem tailTrace_7610831 : CollatzResearch.WordTrace tailWord_7610831 prefixEnd_7610831 3908014483139217322410931 := by
  unfold tailWord_7610831
  simp only [CollatzResearch.WordTrace]
  refine ⟨277589811490266588295440347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185059874326844392196960231 277589811490266588295440347)
  ·
    refine ⟨416384717235399882443160521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277589811490266588295440347 416384717235399882443160521)
    ·
      refine ⟨312288537926549911832370391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416384717235399882443160521 312288537926549911832370391)
      ·
        refine ⟨468432806889824867748555587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312288537926549911832370391 468432806889824867748555587)
        ·
          refine ⟨702649210334737301622833381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468432806889824867748555587 702649210334737301622833381)
          ·
            refine ⟨131746726937763244054281259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 702649210334737301622833381 131746726937763244054281259)
            ·
              refine ⟨197620090406644866081421889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131746726937763244054281259 197620090406644866081421889)
              ·
                refine ⟨148215067804983649561066417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197620090406644866081421889 148215067804983649561066417)
                ·
                  refine ⟨111161300853737737170799813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148215067804983649561066417 111161300853737737170799813)
                  ·
                    refine ⟨20842743910075825719524965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111161300853737737170799813 20842743910075825719524965)
                    ·
                      refine ⟨3908014483139217322410931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20842743910075825719524965 3908014483139217322410931)
                      ·
                        rfl

theorem cell23_7610831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_7610831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610831 prefixEnd_7610831 := by exact prefixLift 7610831
  have htrace : WordTrace (prefixWord ++ tailWord_7610831) baseStart_7610831 baseEnd_7610831 := by
    simpa [prefixWord, tailWord_7610831, baseEnd_7610831] using wordTrace_append hprefix tailTrace_7610831
  have hstable : (prefixWord ++ tailWord_7610831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610831).length < 2 ^ (prefixWord ++ tailWord_7610831).sum := by decide
  have hdescent : baseEnd_7610831 < baseStart_7610831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610845 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7610845 : Nat := 118140960795 + 7610845 * 2 ^ 59
def prefixEnd_7610845 : Nat := 4983230072969 + 3 ^ 40 * 7610845 * 2
def baseEnd_7610845 : Nat := 1302673890622793422545289

theorem tailTrace_7610845 : CollatzResearch.WordTrace tailWord_7610845 prefixEnd_7610845 1302673890622793422545289 := by
  unfold tailWord_7610845
  simp only [CollatzResearch.WordTrace]
  refine ⟨277590322112215868686449989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185060214741477245790966659 277590322112215868686449989)
  ·
    refine ⟨52048185396040475378709373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277590322112215868686449989 52048185396040475378709373)
    ·
      refine ⟨19518069523515178267016015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52048185396040475378709373 19518069523515178267016015)
      ·
        refine ⟨29277104285272767400524023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518069523515178267016015 29277104285272767400524023)
        ·
          refine ⟨43915656427909151100786035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29277104285272767400524023 43915656427909151100786035)
          ·
            refine ⟨65873484641863726651179053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43915656427909151100786035 65873484641863726651179053)
            ·
              refine ⟨24702556740698897494192145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65873484641863726651179053 24702556740698897494192145)
              ·
                refine ⟨18526917555524173120644109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24702556740698897494192145 18526917555524173120644109)
                ·
                  refine ⟨6947594083321564920241541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18526917555524173120644109 6947594083321564920241541)
                  ·
                    refine ⟨1302673890622793422545289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947594083321564920241541 1302673890622793422545289)
                    ·
                      rfl

theorem cell23_7610845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7610845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610845 prefixEnd_7610845 := by exact prefixLift 7610845
  have htrace : WordTrace (prefixWord ++ tailWord_7610845) baseStart_7610845 baseEnd_7610845 := by
    simpa [prefixWord, tailWord_7610845, baseEnd_7610845] using wordTrace_append hprefix tailTrace_7610845
  have hstable : (prefixWord ++ tailWord_7610845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610845).length < 2 ^ (prefixWord ++ tailWord_7610845).sum := by decide
  have hdescent : baseEnd_7610845 < baseStart_7610845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610862 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_7610862 : Nat := 118140960795 + 7610862 * 2 ^ 59
def prefixEnd_7610862 : Nat := 4983230072969 + 3 ^ 40 * 7610862 * 2
def baseEnd_7610862 : Nat := 1302676800346502233707763

theorem tailTrace_7610862 : CollatzResearch.WordTrace tailWord_7610862 prefixEnd_7610862 1302676800346502233707763 := by
  unfold tailWord_7610862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34698867769144285073727355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185060628102102853726545893 34698867769144285073727355)
  ·
    refine ⟨52048301653716427610591033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34698867769144285073727355 52048301653716427610591033)
    ·
      refine ⟨39036226240287320707943275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52048301653716427610591033 39036226240287320707943275)
      ·
        refine ⟨58554339360430981061914913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39036226240287320707943275 58554339360430981061914913)
        ·
          refine ⟨43915754520323235796436185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58554339360430981061914913 43915754520323235796436185)
          ·
            refine ⟨32936815890242426847327139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43915754520323235796436185 32936815890242426847327139)
            ·
              refine ⟨49405223835363640270990709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32936815890242426847327139 49405223835363640270990709)
              ·
                refine ⟨4631739734565341275405379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49405223835363640270990709 4631739734565341275405379)
                ·
                  refine ⟨6947609601848011913108069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631739734565341275405379 6947609601848011913108069)
                  ·
                    refine ⟨1302676800346502233707763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947609601848011913108069 1302676800346502233707763)
                    ·
                      rfl

theorem cell23_7610862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_7610862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610862 prefixEnd_7610862 := by exact prefixLift 7610862
  have htrace : WordTrace (prefixWord ++ tailWord_7610862) baseStart_7610862 baseEnd_7610862 := by
    simpa [prefixWord, tailWord_7610862, baseEnd_7610862] using wordTrace_append hprefix tailTrace_7610862
  have hstable : (prefixWord ++ tailWord_7610862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610862).length < 2 ^ (prefixWord ++ tailWord_7610862).sum := by decide
  have hdescent : baseEnd_7610862 < baseStart_7610862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610885 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_7610885 : Nat := 118140960795 + 7610885 * 2 ^ 59
def prefixEnd_7610885 : Nat := 4983230072969 + 3 ^ 40 * 7610885 * 2
def baseEnd_7610885 : Nat := 3908042211094560111135683

theorem tailTrace_7610885 : CollatzResearch.WordTrace tailWord_7610885 prefixEnd_7610885 3908042211094560111135683 := by
  unfold tailWord_7610885
  simp only [CollatzResearch.WordTrace]
  refine ⟨277591781032070955517906109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185061187354713970345270739 277591781032070955517906109)
  ·
    refine ⟨104096917887026608319214791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277591781032070955517906109 104096917887026608319214791)
    ·
      refine ⟨156145376830539912478822187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104096917887026608319214791 156145376830539912478822187)
      ·
        refine ⟨234218065245809868718233281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156145376830539912478822187 234218065245809868718233281)
        ·
          refine ⟨175663548934357401538674961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234218065245809868718233281 175663548934357401538674961)
          ·
            refine ⟨131747661700768051154006221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175663548934357401538674961 131747661700768051154006221)
            ·
              refine ⟨49405373137788019182752333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131747661700768051154006221 49405373137788019182752333)
              ·
                refine ⟨18527014926670507193532125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49405373137788019182752333 18527014926670507193532125)
                ·
                  refine ⟨6947630597501440197574547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18527014926670507193532125 6947630597501440197574547)
                  ·
                    refine ⟨10421445896252160296361821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6947630597501440197574547 10421445896252160296361821)
                    ·
                      refine ⟨3908042211094560111135683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421445896252160296361821 3908042211094560111135683)
                      ·
                        rfl

theorem cell23_7610885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_7610885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610885 prefixEnd_7610885 := by exact prefixLift 7610885
  have htrace : WordTrace (prefixWord ++ tailWord_7610885) baseStart_7610885 baseEnd_7610885 := by
    simpa [prefixWord, tailWord_7610885, baseEnd_7610885] using wordTrace_append hprefix tailTrace_7610885
  have hstable : (prefixWord ++ tailWord_7610885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610885).length < 2 ^ (prefixWord ++ tailWord_7610885).sum := by decide
  have hdescent : baseEnd_7610885 < baseStart_7610885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610886 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7610886 : Nat := 118140960795 + 7610886 * 2 ^ 59
def prefixEnd_7610886 : Nat := 4983230072969 + 3 ^ 40 * 7610886 * 2
def baseEnd_7610886 : Nat := 3908042724575214607223179

theorem tailTrace_7610886 : CollatzResearch.WordTrace tailWord_7610886 prefixEnd_7610886 3908042724575214607223179 := by
  unfold tailWord_7610886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674744297033354146521641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185061211670044888459128341 8674744297033354146521641)
  ·
    refine ⟨6506058222775015609891231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8674744297033354146521641 6506058222775015609891231)
    ·
      refine ⟨9759087334162523414836847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6506058222775015609891231 9759087334162523414836847)
      ·
        refine ⟨14638631001243785122255271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9759087334162523414836847 14638631001243785122255271)
        ·
          refine ⟨21957946501865677683382907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14638631001243785122255271 21957946501865677683382907)
          ·
            refine ⟨32936919752798516525074361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21957946501865677683382907 32936919752798516525074361)
            ·
              refine ⟨24702689814598887393805771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32936919752798516525074361 24702689814598887393805771)
              ·
                refine ⟨37054034721898331090708657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24702689814598887393805771 37054034721898331090708657)
                ·
                  refine ⟨27790526041423748318031493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37054034721898331090708657 27790526041423748318031493)
                  ·
                    refine ⟨5210723632766952809630905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27790526041423748318031493 5210723632766952809630905)
                    ·
                      refine ⟨3908042724575214607223179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210723632766952809630905 3908042724575214607223179)
                      ·
                        rfl

theorem cell23_7610886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7610886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610886 prefixEnd_7610886 := by exact prefixLift 7610886
  have htrace : WordTrace (prefixWord ++ tailWord_7610886) baseStart_7610886 baseEnd_7610886 := by
    simpa [prefixWord, tailWord_7610886, baseEnd_7610886] using wordTrace_append hprefix tailTrace_7610886
  have hstable : (prefixWord ++ tailWord_7610886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610886).length < 2 ^ (prefixWord ++ tailWord_7610886).sum := by decide
  have hdescent : baseEnd_7610886 < baseStart_7610886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610928 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_7610928 : Nat := 118140960795 + 7610928 * 2 ^ 59
def prefixEnd_7610928 : Nat := 4983230072969 + 3 ^ 40 * 7610928 * 2
def baseEnd_7610928 : Nat := 3908064290762703442897985

theorem tailTrace_7610928 : CollatzResearch.WordTrace tailWord_7610928 prefixEnd_7610928 3908064290762703442897985 := by
  unfold tailWord_7610928
  simp only [CollatzResearch.WordTrace]
  refine ⟨138796674685457586930860719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185062232913943449241147625 138796674685457586930860719)
  ·
    refine ⟨208195012028186380396291079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138796674685457586930860719 208195012028186380396291079)
    ·
      refine ⟨312292518042279570594436619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208195012028186380396291079 312292518042279570594436619)
      ·
        refine ⟨468438777063419355891654929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312292518042279570594436619 468438777063419355891654929)
        ·
          refine ⟨351329082797564516918741197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468438777063419355891654929 351329082797564516918741197)
          ·
            refine ⟨131748406049086693844527949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351329082797564516918741197 131748406049086693844527949)
            ·
              refine ⟨49405652268407510191697981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131748406049086693844527949 49405652268407510191697981)
              ·
                refine ⟨18527119600652816321886743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49405652268407510191697981 18527119600652816321886743)
                ·
                  refine ⟨27790679400979224482830115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527119600652816321886743 27790679400979224482830115)
                  ·
                    refine ⟨41686019101468836724245173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27790679400979224482830115 41686019101468836724245173)
                    ·
                      refine ⟨3908064290762703442897985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41686019101468836724245173 3908064290762703442897985)
                      ·
                        rfl

theorem cell23_7610928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_7610928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610928 prefixEnd_7610928 := by exact prefixLift 7610928
  have htrace : WordTrace (prefixWord ++ tailWord_7610928) baseStart_7610928 baseEnd_7610928 := by
    simpa [prefixWord, tailWord_7610928, baseEnd_7610928] using wordTrace_append hprefix tailTrace_7610928
  have hstable : (prefixWord ++ tailWord_7610928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610928).length < 2 ^ (prefixWord ++ tailWord_7610928).sum := by decide
  have hdescent : baseEnd_7610928 < baseStart_7610928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610935 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 2, 4]
def baseStart_7610935 : Nat := 118140960795 + 7610935 * 2 ^ 59
def prefixEnd_7610935 : Nat := 4983230072969 + 3 ^ 40 * 7610935 * 2
def baseEnd_7610935 : Nat := 1302689295042428305170151

theorem tailTrace_7610935 : CollatzResearch.WordTrace tailWord_7610935 prefixEnd_7610935 1302689295042428305170151 := by
  unfold tailWord_7610935
  simp only [CollatzResearch.WordTrace]
  refine ⟨277593604681889814057226259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185062403121259876038150839 277593604681889814057226259)
  ·
    refine ⟨416390407022834721085839389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277593604681889814057226259 416390407022834721085839389)
    ·
      refine ⟨156146402633563020407189771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416390407022834721085839389 156146402633563020407189771)
      ·
        refine ⟨234219603950344530610784657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156146402633563020407189771 234219603950344530610784657)
        ·
          refine ⟨175664702962758397958088493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234219603950344530610784657 175664702962758397958088493)
          ·
            refine ⟨65874263611034399234283185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175664702962758397958088493 65874263611034399234283185)
            ·
              refine ⟨49405697708275799425712389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65874263611034399234283185 49405697708275799425712389)
              ·
                refine ⟨9263568320301712392321073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49405697708275799425712389 9263568320301712392321073)
                ·
                  refine ⟨6947676240226284294240805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9263568320301712392321073 6947676240226284294240805)
                  ·
                    refine ⟨1302689295042428305170151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6947676240226284294240805 1302689295042428305170151)
                    ·
                      rfl

theorem cell23_7610935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_7610935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610935 prefixEnd_7610935 := by exact prefixLift 7610935
  have htrace : WordTrace (prefixWord ++ tailWord_7610935) baseStart_7610935 baseEnd_7610935 := by
    simpa [prefixWord, tailWord_7610935, baseEnd_7610935] using wordTrace_append hprefix tailTrace_7610935
  have hstable : (prefixWord ++ tailWord_7610935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610935).length < 2 ^ (prefixWord ++ tailWord_7610935).sum := by decide
  have hdescent : baseEnd_7610935 < baseStart_7610935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610938 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_7610938 : Nat := 118140960795 + 7610938 * 2 ^ 59
def prefixEnd_7610938 : Nat := 4983230072969 + 3 ^ 40 * 7610938 * 2
def baseEnd_7610938 : Nat := 3908069425569248403772939

theorem tailTrace_7610938 : CollatzResearch.WordTrace tailWord_7610938 prefixEnd_7610938 3908069425569248403772939 := by
  unfold tailWord_7610938
  simp only [CollatzResearch.WordTrace]
  refine ⟨69398428525219736392396367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185062476067252630379723645 69398428525219736392396367)
  ·
    refine ⟨104097642787829604588594551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69398428525219736392396367 104097642787829604588594551)
    ·
      refine ⟨156146464181744406882891827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104097642787829604588594551 156146464181744406882891827)
      ·
        refine ⟨234219696272616610324337741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156146464181744406882891827 234219696272616610324337741)
        ·
          refine ⟨87832386102231228871626653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234219696272616610324337741 87832386102231228871626653)
          ·
            refine ⟨32937144788336710826859995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87832386102231228871626653 32937144788336710826859995)
            ·
              refine ⟨49405717182505066240289993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32937144788336710826859995 49405717182505066240289993)
              ·
                refine ⟨37054287886878799680217495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49405717182505066240289993 37054287886878799680217495)
                ·
                  refine ⟨55581431830318199520326243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37054287886878799680217495 55581431830318199520326243)
                  ·
                    refine ⟨83372147745477299280489365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55581431830318199520326243 83372147745477299280489365)
                    ·
                      refine ⟨3908069425569248403772939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83372147745477299280489365 3908069425569248403772939)
                      ·
                        rfl

theorem cell23_7610938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_7610938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610938 prefixEnd_7610938 := by exact prefixLift 7610938
  have htrace : WordTrace (prefixWord ++ tailWord_7610938) baseStart_7610938 baseEnd_7610938 := by
    simpa [prefixWord, tailWord_7610938, baseEnd_7610938] using wordTrace_append hprefix tailTrace_7610938
  have hstable : (prefixWord ++ tailWord_7610938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610938).length < 2 ^ (prefixWord ++ tailWord_7610938).sum := by decide
  have hdescent : baseEnd_7610938 < baseStart_7610938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610945 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7610945 : Nat := 118140960795 + 7610945 * 2 ^ 59
def prefixEnd_7610945 : Nat := 4983230072969 + 3 ^ 40 * 7610945 * 2
def baseEnd_7610945 : Nat := 3908073019933829876385407

theorem tailTrace_7610945 : CollatzResearch.WordTrace tailWord_7610945 prefixEnd_7610945 3908073019933829876385407 := by
  unfold tailWord_7610945
  simp only [CollatzResearch.WordTrace]
  refine ⟨277593969411853585765090289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185062646274569057176726859 277593969411853585765090289)
  ·
    refine ⟨208195477058890189323817717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277593969411853585765090289 208195477058890189323817717)
    ·
      refine ⟨19518325974270955249107911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208195477058890189323817717 19518325974270955249107911)
      ·
        refine ⟨29277488961406432873661867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518325974270955249107911 29277488961406432873661867)
        ·
          refine ⟨43916233442109649310492801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29277488961406432873661867 43916233442109649310492801)
          ·
            refine ⟨32937175081582236982869601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43916233442109649310492801 32937175081582236982869601)
            ·
              refine ⟨24702881311186677737152201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32937175081582236982869601 24702881311186677737152201)
              ·
                refine ⟨18527160983390008302864151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24702881311186677737152201 18527160983390008302864151)
                ·
                  refine ⟨27790741475085012454296227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527160983390008302864151 27790741475085012454296227)
                  ·
                    refine ⟨41686112212627518681444341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27790741475085012454296227 41686112212627518681444341)
                    ·
                      refine ⟨3908073019933829876385407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41686112212627518681444341 3908073019933829876385407)
                      ·
                        rfl

theorem cell23_7610945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7610945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610945 prefixEnd_7610945 := by exact prefixLift 7610945
  have htrace : WordTrace (prefixWord ++ tailWord_7610945) baseStart_7610945 baseEnd_7610945 := by
    simpa [prefixWord, tailWord_7610945, baseEnd_7610945] using wordTrace_append hprefix tailTrace_7610945
  have hstable : (prefixWord ++ tailWord_7610945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610945).length < 2 ^ (prefixWord ++ tailWord_7610945).sum := by decide
  have hdescent : baseEnd_7610945 < baseStart_7610945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610972 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7610972 : Nat := 118140960795 + 7610972 * 2 ^ 59
def prefixEnd_7610972 : Nat := 4983230072969 + 3 ^ 40 * 7610972 * 2
def baseEnd_7610972 : Nat := 3908086883911501270747783

theorem tailTrace_7610972 : CollatzResearch.WordTrace tailWord_7610972 prefixEnd_7610972 3908086883911501270747783 := by
  unfold tailWord_7610972
  simp only [CollatzResearch.WordTrace]
  refine ⟨138797477091377884688161585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185063302788503846250882113 138797477091377884688161585)
  ·
    refine ⟨104098107818533413516121189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138797477091377884688161585 104098107818533413516121189)
    ·
      refine ⟨19518395215975015034272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104098107818533413516121189 19518395215975015034272723)
      ·
        refine ⟨29277592823962522551409085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518395215975015034272723 29277592823962522551409085)
        ·
          refine ⟨10979097308985945956778407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29277592823962522551409085 10979097308985945956778407)
          ·
            refine ⟨16468645963478918935167611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979097308985945956778407 16468645963478918935167611)
            ·
              refine ⟨24702968945218378402751417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468645963478918935167611 24702968945218378402751417)
              ·
                refine ⟨18527226708913783802063563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24702968945218378402751417 18527226708913783802063563)
                ·
                  refine ⟨27790840063370675703095345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527226708913783802063563 27790840063370675703095345)
                  ·
                    refine ⟨20843130047528006777321509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27790840063370675703095345 20843130047528006777321509)
                    ·
                      refine ⟨3908086883911501270747783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20843130047528006777321509 3908086883911501270747783)
                      ·
                        rfl

theorem cell23_7610972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7610972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610972 prefixEnd_7610972 := by exact prefixLift 7610972
  have htrace : WordTrace (prefixWord ++ tailWord_7610972) baseStart_7610972 baseEnd_7610972 := by
    simpa [prefixWord, tailWord_7610972, baseEnd_7610972] using wordTrace_append hprefix tailTrace_7610972
  have hstable : (prefixWord ++ tailWord_7610972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610972).length < 2 ^ (prefixWord ++ tailWord_7610972).sum := by decide
  have hdescent : baseEnd_7610972 < baseStart_7610972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610975 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_7610975 : Nat := 118140960795 + 7610975 * 2 ^ 59
def prefixEnd_7610975 : Nat := 4983230072969 + 3 ^ 40 * 7610975 * 2
def baseEnd_7610975 : Nat := 3908088424353464759010269

theorem tailTrace_7610975 : CollatzResearch.WordTrace tailWord_7610975 prefixEnd_7610975 3908088424353464759010269 := by
  unfold tailWord_7610975
  simp only [CollatzResearch.WordTrace]
  refine ⟨277595063601744900888682379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185063375734496600592454919 277595063601744900888682379)
  ·
    refine ⟨416392595402617351333023569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277595063601744900888682379 416392595402617351333023569)
    ·
      refine ⟨312294446551963013499767677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416392595402617351333023569 312294446551963013499767677)
      ·
        refine ⟨117110417456986130062412879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312294446551963013499767677 117110417456986130062412879)
        ·
          refine ⟨175665626185479195093619319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117110417456986130062412879 175665626185479195093619319)
          ·
            refine ⟨263498439278218792640428979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175665626185479195093619319 263498439278218792640428979)
            ·
              refine ⟨395247658917328188960643469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263498439278218792640428979 395247658917328188960643469)
              ·
                refine ⟨148217872093998070860241301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395247658917328188960643469 148217872093998070860241301)
                ·
                  refine ⟨6947712754406159571573811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148217872093998070860241301 6947712754406159571573811)
                  ·
                    refine ⟨10421569131609239357360717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6947712754406159571573811 10421569131609239357360717)
                    ·
                      refine ⟨3908088424353464759010269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421569131609239357360717 3908088424353464759010269)
                      ·
                        rfl

theorem cell23_7610975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_7610975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610975 prefixEnd_7610975 := by exact prefixLift 7610975
  have htrace : WordTrace (prefixWord ++ tailWord_7610975) baseStart_7610975 baseEnd_7610975 := by
    simpa [prefixWord, tailWord_7610975, baseEnd_7610975] using wordTrace_append hprefix tailTrace_7610975
  have hstable : (prefixWord ++ tailWord_7610975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610975).length < 2 ^ (prefixWord ++ tailWord_7610975).sum := by decide
  have hdescent : baseEnd_7610975 < baseStart_7610975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7610988 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_7610988 : Nat := 118140960795 + 7610988 * 2 ^ 59
def prefixEnd_7610988 : Nat := 4983230072969 + 3 ^ 40 * 7610988 * 2
def baseEnd_7610988 : Nat := 3908095099601973208147709

theorem tailTrace_7610988 : CollatzResearch.WordTrace tailWord_7610988 prefixEnd_7610988 3908095099601973208147709 := by
  unfold tailWord_7610988
  simp only [CollatzResearch.WordTrace]
  refine ⟨138797768875348902054452809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185063691833798536072603745 138797768875348902054452809)
  ·
    refine ⟨104098326656511676540839607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138797768875348902054452809 104098326656511676540839607)
    ·
      refine ⟨156147489984767514811259411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104098326656511676540839607 156147489984767514811259411)
      ·
        refine ⟨234221234977151272216889117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156147489984767514811259411 234221234977151272216889117)
        ·
          refine ⟨87832963116431727081333419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234221234977151272216889117 87832963116431727081333419)
          ·
            refine ⟨131749444674647590622000129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87832963116431727081333419 131749444674647590622000129)
            ·
              refine ⟨98812083505985692966500097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131749444674647590622000129 98812083505985692966500097)
              ·
                refine ⟨74109062629489269724875073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98812083505985692966500097 74109062629489269724875073)
                ·
                  refine ⟨55581796972116952293656305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74109062629489269724875073 55581796972116952293656305)
                  ·
                    refine ⟨41686347729087714220242229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55581796972116952293656305 41686347729087714220242229)
                    ·
                      refine ⟨3908095099601973208147709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41686347729087714220242229 3908095099601973208147709)
                      ·
                        rfl

theorem cell23_7610988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_7610988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7610988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7610988 prefixEnd_7610988 := by exact prefixLift 7610988
  have htrace : WordTrace (prefixWord ++ tailWord_7610988) baseStart_7610988 baseEnd_7610988 := by
    simpa [prefixWord, tailWord_7610988, baseEnd_7610988] using wordTrace_append hprefix tailTrace_7610988
  have hstable : (prefixWord ++ tailWord_7610988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7610988).length < 2 ^ (prefixWord ++ tailWord_7610988).sum := by decide
  have hdescent : baseEnd_7610988 < baseStart_7610988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7610988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611008 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_7611008 : Nat := 118140960795 + 7611008 * 2 ^ 59
def prefixEnd_7611008 : Nat := 4983230072969 + 3 ^ 40 * 7611008 * 2
def baseEnd_7611008 : Nat := 1302701789738354376632539

theorem tailTrace_7611008 : CollatzResearch.WordTrace tailWord_7611008 prefixEnd_7611008 1302701789738354376632539 := by
  unfold tailWord_7611008
  simp only [CollatzResearch.WordTrace]
  refine ⟨138798133605312673762316839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185064178140416898349755785 138798133605312673762316839)
  ·
    refine ⟨208197200407969010643475259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138798133605312673762316839 208197200407969010643475259)
    ·
      refine ⟨312295800611953515965212889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208197200407969010643475259 312295800611953515965212889)
      ·
        refine ⟨234221850458965136973909667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312295800611953515965212889 234221850458965136973909667)
        ·
          refine ⟨351332775688447705460864501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234221850458965136973909667 351332775688447705460864501)
          ·
            refine ⟨32937447720791972386956047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351332775688447705460864501 32937447720791972386956047)
            ·
              refine ⟨49406171581187958580434071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32937447720791972386956047 49406171581187958580434071)
              ·
                refine ⟨74109257371781937870651107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49406171581187958580434071 74109257371781937870651107)
                ·
                  refine ⟨111163886057672906805976661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74109257371781937870651107 111163886057672906805976661)
                  ·
                    refine ⟨1302701789738354376632539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111163886057672906805976661 1302701789738354376632539)
                    ·
                      rfl

theorem cell23_7611008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_7611008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611008 prefixEnd_7611008 := by exact prefixLift 7611008
  have htrace : WordTrace (prefixWord ++ tailWord_7611008) baseStart_7611008 baseEnd_7611008 := by
    simpa [prefixWord, tailWord_7611008, baseEnd_7611008] using wordTrace_append hprefix tailTrace_7611008
  have hstable : (prefixWord ++ tailWord_7611008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611008).length < 2 ^ (prefixWord ++ tailWord_7611008).sum := by decide
  have hdescent : baseEnd_7611008 < baseStart_7611008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611010 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_7611010 : Nat := 118140960795 + 7611010 * 2 ^ 59
def prefixEnd_7611010 : Nat := 4983230072969 + 3 ^ 40 * 7611010 * 2
def baseEnd_7611010 : Nat := 3908106396176372122072609

theorem tailTrace_7611010 : CollatzResearch.WordTrace tailWord_7611010 prefixEnd_7611010 3908106396176372122072609 := by
  unfold tailWord_7611010
  simp only [CollatzResearch.WordTrace]
  refine ⟨69399085039154525466551621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185064226771078734577470989 69399085039154525466551621)
  ·
    refine ⟨13012328444841473524978429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69399085039154525466551621 13012328444841473524978429)
    ·
      refine ⟨4879623166815552571866911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13012328444841473524978429 4879623166815552571866911)
      ·
        refine ⟨7319434750223328857800367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4879623166815552571866911 7319434750223328857800367)
        ·
          refine ⟨10979152125334993286700551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7319434750223328857800367 10979152125334993286700551)
          ·
            refine ⟨16468728188002489930050827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979152125334993286700551 16468728188002489930050827)
            ·
              refine ⟨24703092282003734895076241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468728188002489930050827 24703092282003734895076241)
              ·
                refine ⟨18527319211502801171307181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24703092282003734895076241 18527319211502801171307181)
                ·
                  refine ⟨6947744704313550439240193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18527319211502801171307181 6947744704313550439240193)
                  ·
                    refine ⟨5210808528235162829430145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947744704313550439240193 5210808528235162829430145)
                    ·
                      refine ⟨3908106396176372122072609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210808528235162829430145 3908106396176372122072609)
                      ·
                        rfl

theorem cell23_7611010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_7611010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611010 prefixEnd_7611010 := by exact prefixLift 7611010
  have htrace : WordTrace (prefixWord ++ tailWord_7611010) baseStart_7611010 baseEnd_7611010 := by
    simpa [prefixWord, tailWord_7611010, baseEnd_7611010] using wordTrace_append hprefix tailTrace_7611010
  have hstable : (prefixWord ++ tailWord_7611010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611010).length < 2 ^ (prefixWord ++ tailWord_7611010).sum := by decide
  have hdescent : baseEnd_7611010 < baseStart_7611010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611032 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2]
def baseStart_7611032 : Nat := 118140960795 + 7611032 * 2 ^ 59
def prefixEnd_7611032 : Nat := 4983230072969 + 3 ^ 40 * 7611032 * 2
def baseEnd_7611032 : Nat := 3908117692750771035997507

theorem tailTrace_7611032 : CollatzResearch.WordTrace tailWord_7611032 prefixEnd_7611032 3908117692750771035997507 := by
  unfold tailWord_7611032
  simp only [CollatzResearch.WordTrace]
  refine ⟨138798571281269199811753675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185064761708358933082338233 138798571281269199811753675)
  ·
    refine ⟨208197856921903799717630513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138798571281269199811753675 208197856921903799717630513)
    ·
      refine ⟨156148392691427849788222885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208197856921903799717630513 156148392691427849788222885)
      ·
        refine ⟨29277823629642721835291791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156148392691427849788222885 29277823629642721835291791)
        ·
          refine ⟨43916735444464082752937687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29277823629642721835291791 43916735444464082752937687)
          ·
            refine ⟨65875103166696124129406531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43916735444464082752937687 65875103166696124129406531)
            ·
              refine ⟨98812654750044186194109797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65875103166696124129406531 98812654750044186194109797)
              ·
                refine ⟨18527372765633284911395587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98812654750044186194109797 18527372765633284911395587)
                ·
                  refine ⟨27791059148449927367093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527372765633284911395587 27791059148449927367093381)
                  ·
                    refine ⟨5210823590334361381330009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27791059148449927367093381 5210823590334361381330009)
                    ·
                      refine ⟨3908117692750771035997507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210823590334361381330009 3908117692750771035997507)
                      ·
                        rfl

theorem cell23_7611032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_7611032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611032 prefixEnd_7611032 := by exact prefixLift 7611032
  have htrace : WordTrace (prefixWord ++ tailWord_7611032) baseStart_7611032 baseEnd_7611032 := by
    simpa [prefixWord, tailWord_7611032, baseEnd_7611032] using wordTrace_append hprefix tailTrace_7611032
  have hstable : (prefixWord ++ tailWord_7611032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611032).length < 2 ^ (prefixWord ++ tailWord_7611032).sum := by decide
  have hdescent : baseEnd_7611032 < baseStart_7611032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611036 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7611036 : Nat := 118140960795 + 7611036 * 2 ^ 59
def prefixEnd_7611036 : Nat := 4983230072969 + 3 ^ 40 * 7611036 * 2
def baseEnd_7611036 : Nat := 3908119746673389020347489

theorem tailTrace_7611036 : CollatzResearch.WordTrace tailWord_7611036 prefixEnd_7611036 3908119746673389020347489 := by
  unfold tailWord_7611036
  simp only [CollatzResearch.WordTrace]
  refine ⟨138798644227261954153326481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185064858969682605537768641 138798644227261954153326481)
  ·
    refine ⟨104098983170446465614994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138798644227261954153326481 104098983170446465614994861)
    ·
      refine ⟨39037118688917424605623073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104098983170446465614994861 39037118688917424605623073)
      ·
        refine ⟨29277839016688068454217305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39037118688917424605623073 29277839016688068454217305)
        ·
          refine ⟨21958379262516051340662979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29277839016688068454217305 21958379262516051340662979)
          ·
            refine ⟨32937568893774077010994469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21958379262516051340662979 32937568893774077010994469)
            ·
              refine ⟨6175794167582639439561463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32937568893774077010994469 6175794167582639439561463)
              ·
                refine ⟨9263691251373959159342195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175794167582639439561463 9263691251373959159342195)
                ·
                  refine ⟨13895536877060938739013293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263691251373959159342195 13895536877060938739013293)
                  ·
                    refine ⟨5210826328897852027129985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13895536877060938739013293 5210826328897852027129985)
                    ·
                      refine ⟨3908119746673389020347489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210826328897852027129985 3908119746673389020347489)
                      ·
                        rfl

theorem cell23_7611036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7611036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611036 prefixEnd_7611036 := by exact prefixLift 7611036
  have htrace : WordTrace (prefixWord ++ tailWord_7611036) baseStart_7611036 baseEnd_7611036 := by
    simpa [prefixWord, tailWord_7611036, baseEnd_7611036] using wordTrace_append hprefix tailTrace_7611036
  have hstable : (prefixWord ++ tailWord_7611036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611036).length < 2 ^ (prefixWord ++ tailWord_7611036).sum := by decide
  have hdescent : baseEnd_7611036 < baseStart_7611036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611055 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 7]
def baseStart_7611055 : Nat := 118140960795 + 7611055 * 2 ^ 59
def prefixEnd_7611055 : Nat := 4983230072969 + 3 ^ 40 * 7611055 * 2
def baseEnd_7611055 : Nat := 434236611422869382889989

theorem tailTrace_7611055 : CollatzResearch.WordTrace tailWord_7611055 prefixEnd_7611055 434236611422869382889989 := by
  unfold tailWord_7611055
  simp only [CollatzResearch.WordTrace]
  refine ⟨277597981441455074551594619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185065320960970049701063079 277597981441455074551594619)
  ·
    refine ⟨416396972162182611827391929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277597981441455074551594619 416396972162182611827391929)
    ·
      refine ⟨312297729121636958870543947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416396972162182611827391929 312297729121636958870543947)
      ·
        refine ⟨468446593682455438305815921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312297729121636958870543947 468446593682455438305815921)
        ·
          refine ⟨351334945261841578729361941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468446593682455438305815921 351334945261841578729361941)
          ·
            refine ⟨16468825559148824002938841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351334945261841578729361941 16468825559148824002938841)
            ·
              refine ⟨12351619169361618002204131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16468825559148824002938841 12351619169361618002204131)
              ·
                refine ⟨18527428754042427003306197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351619169361618002204131 18527428754042427003306197)
                ·
                  refine ⟨434236611422869382889989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18527428754042427003306197 434236611422869382889989)
                  ·
                    rfl

theorem cell23_7611055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 7].length) (baseStart_7611055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611055 prefixEnd_7611055 := by exact prefixLift 7611055
  have htrace : WordTrace (prefixWord ++ tailWord_7611055) baseStart_7611055 baseEnd_7611055 := by
    simpa [prefixWord, tailWord_7611055, baseEnd_7611055] using wordTrace_append hprefix tailTrace_7611055
  have hstable : (prefixWord ++ tailWord_7611055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611055).length < 2 ^ (prefixWord ++ tailWord_7611055).sum := by decide
  have hdescent : baseEnd_7611055 < baseStart_7611055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611066 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2]
def baseStart_7611066 : Nat := 118140960795 + 7611066 * 2 ^ 59
def prefixEnd_7611066 : Nat := 4983230072969 + 3 ^ 40 * 7611066 * 2
def baseEnd_7611066 : Nat := 3908135151093023902972351

theorem tailTrace_7611066 : CollatzResearch.WordTrace tailWord_7611066 prefixEnd_7611066 3908135151093023902972351 := by
  unfold tailWord_7611066
  simp only [CollatzResearch.WordTrace]
  refine ⟨69399595661103805857561263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185065588429610148953496701 69399595661103805857561263)
  ·
    refine ⟨104099393491655708786341895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69399595661103805857561263 104099393491655708786341895)
    ·
      refine ⟨156149090237483563179512843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104099393491655708786341895 156149090237483563179512843)
      ·
        refine ⟨234223635356225344769269265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156149090237483563179512843 234223635356225344769269265)
        ·
          refine ⟨175667726517169008576951949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234223635356225344769269265 175667726517169008576951949)
          ·
            refine ⟨65875397443938378216356981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175667726517169008576951949 65875397443938378216356981)
            ·
              refine ⟨6175818510369222957783467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65875397443938378216356981 6175818510369222957783467)
              ·
                refine ⟨9263727765553834436675201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175818510369222957783467 9263727765553834436675201)
                ·
                  refine ⟨6947795824165375827506401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9263727765553834436675201 6947795824165375827506401)
                  ·
                    refine ⟨5210846868124031870629801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947795824165375827506401 5210846868124031870629801)
                    ·
                      refine ⟨3908135151093023902972351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210846868124031870629801 3908135151093023902972351)
                      ·
                        rfl

theorem cell23_7611066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_7611066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611066 prefixEnd_7611066 := by exact prefixLift 7611066
  have htrace : WordTrace (prefixWord ++ tailWord_7611066) baseStart_7611066 baseEnd_7611066 := by
    simpa [prefixWord, tailWord_7611066, baseEnd_7611066] using wordTrace_append hprefix tailTrace_7611066
  have hstable : (prefixWord ++ tailWord_7611066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611066).length < 2 ^ (prefixWord ++ tailWord_7611066).sum := by decide
  have hdescent : baseEnd_7611066 < baseStart_7611066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611088 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_7611088 : Nat := 118140960795 + 7611088 * 2 ^ 59
def prefixEnd_7611088 : Nat := 4983230072969 + 3 ^ 40 * 7611088 * 2
def baseEnd_7611088 : Nat := 3908146447667422816897249

theorem tailTrace_7611088 : CollatzResearch.WordTrace tailWord_7611088 prefixEnd_7611088 3908146447667422816897249 := by
  unfold tailWord_7611088
  simp only [CollatzResearch.WordTrace]
  refine ⟨138799592525167760593772959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185066123366890347458363945 138799592525167760593772959)
  ·
    refine ⟨208199388787751640890659439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138799592525167760593772959 208199388787751640890659439)
    ·
      refine ⟨312299083181627461335989159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208199388787751640890659439 312299083181627461335989159)
      ·
        refine ⟨468448624772441192003983739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312299083181627461335989159 468448624772441192003983739)
        ·
          refine ⟨702672937158661788005975609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468448624772441192003983739 702672937158661788005975609)
          ·
            refine ⟨527004702868996341004481707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702672937158661788005975609 527004702868996341004481707)
            ·
              refine ⟨790507054303494511506722561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527004702868996341004481707 790507054303494511506722561)
              ·
                refine ⟨592880290727620883630041921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790507054303494511506722561 592880290727620883630041921)
                ·
                  refine ⟨444660218045715662722531441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592880290727620883630041921 444660218045715662722531441)
                  ·
                    refine ⟨333495163534286747041898581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 444660218045715662722531441 333495163534286747041898581)
                    ·
                      refine ⟨3908146447667422816897249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 333495163534286747041898581 3908146447667422816897249)
                      ·
                        rfl

theorem cell23_7611088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_7611088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611088 prefixEnd_7611088 := by exact prefixLift 7611088
  have htrace : WordTrace (prefixWord ++ tailWord_7611088) baseStart_7611088 baseEnd_7611088 := by
    simpa [prefixWord, tailWord_7611088, baseEnd_7611088] using wordTrace_append hprefix tailTrace_7611088
  have hstable : (prefixWord ++ tailWord_7611088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611088).length < 2 ^ (prefixWord ++ tailWord_7611088).sum := by decide
  have hdescent : baseEnd_7611088 < baseStart_7611088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611112 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7611112 : Nat := 118140960795 + 7611112 * 2 ^ 59
def prefixEnd_7611112 : Nat := 4983230072969 + 3 ^ 40 * 7611112 * 2
def baseEnd_7611112 : Nat := 3908158771203130722997139

theorem tailTrace_7611112 : CollatzResearch.WordTrace tailWord_7611112 prefixEnd_7611112 3908158771203130722997139 := by
  unfold tailWord_7611112
  simp only [CollatzResearch.WordTrace]
  refine ⟨138800030201124286643209795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185066706934832382190946393 138800030201124286643209795)
  ·
    refine ⟨208200045301686429964814693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138800030201124286643209795 208200045301686429964814693)
    ·
      refine ⟨39037508494066205618402755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208200045301686429964814693 39037508494066205618402755)
      ·
        refine ⟨58556262741099308427604133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39037508494066205618402755 58556262741099308427604133)
        ·
          refine ⟨10979299263956120330175775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58556262741099308427604133 10979299263956120330175775)
          ·
            refine ⟨16468948895934180495263663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979299263956120330175775 16468948895934180495263663)
            ·
              refine ⟨24703423343901270742895495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16468948895934180495263663 24703423343901270742895495)
              ·
                refine ⟨37055135015851906114343243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24703423343901270742895495 37055135015851906114343243)
                ·
                  refine ⟨55582702523777859171514865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37055135015851906114343243 55582702523777859171514865)
                  ·
                    refine ⟨41687026892833394378636149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55582702523777859171514865 41687026892833394378636149)
                    ·
                      refine ⟨3908158771203130722997139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41687026892833394378636149 3908158771203130722997139)
                      ·
                        rfl

theorem cell23_7611112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7611112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611112 prefixEnd_7611112 := by exact prefixLift 7611112
  have htrace : WordTrace (prefixWord ++ tailWord_7611112) baseStart_7611112 baseEnd_7611112 := by
    simpa [prefixWord, tailWord_7611112, baseEnd_7611112] using wordTrace_append hprefix tailTrace_7611112
  have hstable : (prefixWord ++ tailWord_7611112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611112).length < 2 ^ (prefixWord ++ tailWord_7611112).sum := by decide
  have hdescent : baseEnd_7611112 < baseStart_7611112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611162 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_7611162 : Nat := 118140960795 + 7611162 * 2 ^ 59
def prefixEnd_7611162 : Nat := 4983230072969 + 3 ^ 40 * 7611162 * 2
def baseEnd_7611162 : Nat := 434242716137317280819101

theorem tailTrace_7611162 : CollatzResearch.WordTrace tailWord_7611162 prefixEnd_7611162 434242716137317280819101 := by
  unfold tailWord_7611162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69400471013016857956434935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185067922701378287883826493 69400471013016857956434935)
  ·
    refine ⟨104100706519525286934652403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69400471013016857956434935 104100706519525286934652403)
    ·
      refine ⟨156151059779287930401978605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104100706519525286934652403 156151059779287930401978605)
      ·
        refine ⟨58556647417232973900741977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156151059779287930401978605 58556647417232973900741977)
        ·
          refine ⟨43917485562924730425556483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58556647417232973900741977 43917485562924730425556483)
          ·
            refine ⟨65876228344387095638334725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43917485562924730425556483 65876228344387095638334725)
            ·
              refine ⟨12351792814572580432187761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65876228344387095638334725 12351792814572580432187761)
              ·
                refine ⟨9263844610929435324140821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351792814572580432187761 9263844610929435324140821)
                ·
                  refine ⟨434242716137317280819101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9263844610929435324140821 434242716137317280819101)
                  ·
                    rfl

theorem cell23_7611162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_7611162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611162 prefixEnd_7611162 := by exact prefixLift 7611162
  have htrace : WordTrace (prefixWord ++ tailWord_7611162) baseStart_7611162 baseEnd_7611162 := by
    simpa [prefixWord, tailWord_7611162, baseEnd_7611162] using wordTrace_append hprefix tailTrace_7611162
  have hstable : (prefixWord ++ tailWord_7611162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611162).length < 2 ^ (prefixWord ++ tailWord_7611162).sum := by decide
  have hdescent : baseEnd_7611162 < baseStart_7611162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611185 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_7611185 : Nat := 118140960795 + 7611185 * 2 ^ 59
def prefixEnd_7611185 : Nat := 4983230072969 + 3 ^ 40 * 7611185 * 2
def baseEnd_7611185 : Nat := 3908196255290908937384303

theorem tailTrace_7611185 : CollatzResearch.WordTrace tailWord_7611185 prefixEnd_7611185 3908196255290908937384303 := by
  unfold tailWord_7611185
  simp only [CollatzResearch.WordTrace]
  refine ⟨277602722930984106753827009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185068481953989404502551339 277602722930984106753827009)
  ·
    refine ⟨208202042198238080065370257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277602722930984106753827009 208202042198238080065370257)
    ·
      refine ⟨156151531648678560049027693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208202042198238080065370257 156151531648678560049027693)
      ·
        refine ⟨58556824368254460018385385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156151531648678560049027693 58556824368254460018385385)
        ·
          refine ⟨43917618276190845013789039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58556824368254460018385385 43917618276190845013789039)
          ·
            refine ⟨65876427414286267520683559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43917618276190845013789039 65876427414286267520683559)
            ·
              refine ⟨98814641121429401281025339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65876427414286267520683559 98814641121429401281025339)
              ·
                refine ⟨148221961682144101921538009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98814641121429401281025339 148221961682144101921538009)
                ·
                  refine ⟨111166471261608076441153507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148221961682144101921538009 111166471261608076441153507)
                  ·
                    refine ⟨166749706892412114661730261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111166471261608076441153507 166749706892412114661730261)
                    ·
                      refine ⟨3908196255290908937384303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166749706892412114661730261 3908196255290908937384303)
                      ·
                        rfl

theorem cell23_7611185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_7611185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611185 prefixEnd_7611185 := by exact prefixLift 7611185
  have htrace : WordTrace (prefixWord ++ tailWord_7611185) baseStart_7611185 baseEnd_7611185 := by
    simpa [prefixWord, tailWord_7611185, baseEnd_7611185] using wordTrace_append hprefix tailTrace_7611185
  have hstable : (prefixWord ++ tailWord_7611185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611185).length < 2 ^ (prefixWord ++ tailWord_7611185).sum := by decide
  have hdescent : baseEnd_7611185 < baseStart_7611185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611189 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_7611189 : Nat := 118140960795 + 7611189 * 2 ^ 59
def prefixEnd_7611189 : Nat := 4983230072969 + 3 ^ 40 * 7611189 * 2
def baseEnd_7611189 : Nat := 3908198309213526921734285

theorem tailTrace_7611189 : CollatzResearch.WordTrace tailWord_7611189 prefixEnd_7611189 3908198309213526921734285 := by
  unfold tailWord_7611189
  simp only [CollatzResearch.WordTrace]
  refine ⟨277602868822969615436972621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185068579215313076957981747 277602868822969615436972621)
  ·
    refine ⟨104101075808613605788864733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277602868822969615436972621 104101075808613605788864733)
    ·
      refine ⟨39037903428230102170824275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104101075808613605788864733 39037903428230102170824275)
      ·
        refine ⟨58556855142345153256236413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39037903428230102170824275 58556855142345153256236413)
        ·
          refine ⟨21958820678379432471088655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58556855142345153256236413 21958820678379432471088655)
          ·
            refine ⟨32938231017569148706632983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21958820678379432471088655 32938231017569148706632983)
            ·
              refine ⟨49407346526353723059949475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32938231017569148706632983 49407346526353723059949475)
              ·
                refine ⟨74111019789530584589924213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49407346526353723059949475 74111019789530584589924213)
                ·
                  refine ⟨6947908105268492305305395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74111019789530584589924213 6947908105268492305305395)
                  ·
                    refine ⟨10421862157902738457958093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6947908105268492305305395 10421862157902738457958093)
                    ·
                      refine ⟨3908198309213526921734285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421862157902738457958093 3908198309213526921734285)
                      ·
                        rfl

theorem cell23_7611189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_7611189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611189 prefixEnd_7611189 := by exact prefixLift 7611189
  have htrace : WordTrace (prefixWord ++ tailWord_7611189) baseStart_7611189 baseEnd_7611189 := by
    simpa [prefixWord, tailWord_7611189, baseEnd_7611189] using wordTrace_append hprefix tailTrace_7611189
  have hstable : (prefixWord ++ tailWord_7611189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611189).length < 2 ^ (prefixWord ++ tailWord_7611189).sum := by decide
  have hdescent : baseEnd_7611189 < baseStart_7611189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611192 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_7611192 : Nat := 118140960795 + 7611192 * 2 ^ 59
def prefixEnd_7611192 : Nat := 4983230072969 + 3 ^ 40 * 7611192 * 2
def baseEnd_7611192 : Nat := 1302733283218496803332257

theorem tailTrace_7611192 : CollatzResearch.WordTrace tailWord_7611192 prefixEnd_7611192 1302733283218496803332257 := by
  unfold tailWord_7611192
  simp only [CollatzResearch.WordTrace]
  refine ⟨138801489120979373474665915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185068652161305831299554553 138801489120979373474665915)
  ·
    refine ⟨208202233681469060211998873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138801489120979373474665915 208202233681469060211998873)
    ·
      refine ⟨156151675261101795158999155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208202233681469060211998873 156151675261101795158999155)
      ·
        refine ⟨234227512891652692738498733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156151675261101795158999155 234227512891652692738498733)
        ·
          refine ⟨87835317334369759776937025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234227512891652692738498733 87835317334369759776937025)
          ·
            refine ⟨65876488000777319832702769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87835317334369759776937025 65876488000777319832702769)
            ·
              refine ⟨49407366000582989874527077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65876488000777319832702769 49407366000582989874527077)
              ·
                refine ⟨9263881125109310601473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49407366000582989874527077 9263881125109310601473827)
                ·
                  refine ⟨13895821687663965902210741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263881125109310601473827 13895821687663965902210741)
                  ·
                    refine ⟨1302733283218496803332257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13895821687663965902210741 1302733283218496803332257)
                    ·
                      rfl

theorem cell23_7611192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_7611192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611192 prefixEnd_7611192 := by exact prefixLift 7611192
  have htrace : WordTrace (prefixWord ++ tailWord_7611192) baseStart_7611192 baseEnd_7611192 := by
    simpa [prefixWord, tailWord_7611192, baseEnd_7611192] using wordTrace_append hprefix tailTrace_7611192
  have hstable : (prefixWord ++ tailWord_7611192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611192).length < 2 ^ (prefixWord ++ tailWord_7611192).sum := by decide
  have hdescent : baseEnd_7611192 < baseStart_7611192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611199 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 5, 2]
def baseStart_7611199 : Nat := 118140960795 + 7611199 * 2 ^ 59
def prefixEnd_7611199 : Nat := 4983230072969 + 3 ^ 40 * 7611199 * 2
def baseEnd_7611199 : Nat := 3908203444020071882609239

theorem tailTrace_7611199 : CollatzResearch.WordTrace tailWord_7611199 prefixEnd_7611199 3908203444020071882609239 := by
  unfold tailWord_7611199
  simp only [CollatzResearch.WordTrace]
  refine ⟨277603233552933387144836651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185068822368622258096557767 277603233552933387144836651)
  ·
    refine ⟨416404850329400080717254977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277603233552933387144836651 416404850329400080717254977)
    ·
      refine ⟨312303637747050060537941233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416404850329400080717254977 312303637747050060537941233)
      ·
        refine ⟨234227728310287545403455925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312303637747050060537941233 234227728310287545403455925)
        ·
          refine ⟨21958849529089457381573993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234227728310287545403455925 21958849529089457381573993)
          ·
            refine ⟨16469137146817093036180495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21958849529089457381573993 16469137146817093036180495)
            ·
              refine ⟨24703705720225639554270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16469137146817093036180495 24703705720225639554270743)
              ·
                refine ⟨37055558580338459331406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24703705720225639554270743 37055558580338459331406115)
                ·
                  refine ⟨55583337870507688997109173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37055558580338459331406115 55583337870507688997109173)
                  ·
                    refine ⟨5210937925360095843478985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55583337870507688997109173 5210937925360095843478985)
                    ·
                      refine ⟨3908203444020071882609239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210937925360095843478985 3908203444020071882609239)
                      ·
                        rfl

theorem cell23_7611199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_7611199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611199 prefixEnd_7611199 := by exact prefixLift 7611199
  have htrace : WordTrace (prefixWord ++ tailWord_7611199) baseStart_7611199 baseEnd_7611199 := by
    simpa [prefixWord, tailWord_7611199, baseEnd_7611199] using wordTrace_append hprefix tailTrace_7611199
  have hstable : (prefixWord ++ tailWord_7611199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611199).length < 2 ^ (prefixWord ++ tailWord_7611199).sum := by decide
  have hdescent : baseEnd_7611199 < baseStart_7611199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611205 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 6]
def baseStart_7611205 : Nat := 118140960795 + 7611205 * 2 ^ 59
def prefixEnd_7611205 : Nat := 4983230072969 + 3 ^ 40 * 7611205 * 2
def baseEnd_7611205 : Nat := 1302735508301332953044737

theorem tailTrace_7611205 : CollatzResearch.WordTrace tailWord_7611205 prefixEnd_7611205 1302735508301332953044737 := by
  unfold tailWord_7611205
  simp only [CollatzResearch.WordTrace]
  refine ⟨277603452390911650169555069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185068968260607766779703379 277603452390911650169555069)
  ·
    refine ⟨104101294646591868813583151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277603452390911650169555069 104101294646591868813583151)
    ·
      refine ⟨156151941969887803220374727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104101294646591868813583151 156151941969887803220374727)
      ·
        refine ⟨234227912954831704830562091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156151941969887803220374727 234227912954831704830562091)
        ·
          refine ⟨351341869432247557245843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234227912954831704830562091 351341869432247557245843137)
          ·
            refine ⟨263506402074185667934382353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351341869432247557245843137 263506402074185667934382353)
            ·
              refine ⟨197629801555639250950786765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263506402074185667934382353 197629801555639250950786765)
              ·
                refine ⟨74111175583364719106545037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197629801555639250950786765 74111175583364719106545037)
                ·
                  refine ⟨27791690843761769664954389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74111175583364719106545037 27791690843761769664954389)
                  ·
                    refine ⟨1302735508301332953044737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27791690843761769664954389 1302735508301332953044737)
                    ·
                      rfl

theorem cell23_7611205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_7611205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611205 prefixEnd_7611205 := by exact prefixLift 7611205
  have htrace : WordTrace (prefixWord ++ tailWord_7611205) baseStart_7611205 baseEnd_7611205 := by
    simpa [prefixWord, tailWord_7611205, baseEnd_7611205] using wordTrace_append hprefix tailTrace_7611205
  have hstable : (prefixWord ++ tailWord_7611205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611205).length < 2 ^ (prefixWord ++ tailWord_7611205).sum := by decide
  have hdescent : baseEnd_7611205 < baseStart_7611205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611209 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_7611209 : Nat := 118140960795 + 7611209 * 2 ^ 59
def prefixEnd_7611209 : Nat := 4983230072969 + 3 ^ 40 * 7611209 * 2
def baseEnd_7611209 : Nat := 1302736192942205614494731

theorem tailTrace_7611209 : CollatzResearch.WordTrace tailWord_7611209 prefixEnd_7611209 1302736192942205614494731 := by
  unfold tailWord_7611209
  simp only [CollatzResearch.WordTrace]
  refine ⟨277603598282897158852700681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185069065521931439235133787 277603598282897158852700681)
  ·
    refine ⟨208202698712172869139525511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277603598282897158852700681 208202698712172869139525511)
    ·
      refine ⟨312304048068259303709288267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208202698712172869139525511 312304048068259303709288267)
      ·
        refine ⟨468456072102388955563932401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312304048068259303709288267 468456072102388955563932401)
        ·
          refine ⟨351342054076791716672949301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468456072102388955563932401 351342054076791716672949301)
          ·
            refine ⟨32938317569699223438088997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351342054076791716672949301 32938317569699223438088997)
            ·
              refine ⟨6175934544318604394641687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32938317569699223438088997 6175934544318604394641687)
              ·
                refine ⟨9263901816477906591962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175934544318604394641687 9263901816477906591962531)
                ·
                  refine ⟨13895852724716859887943797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263901816477906591962531 13895852724716859887943797)
                  ·
                    refine ⟨1302736192942205614494731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13895852724716859887943797 1302736192942205614494731)
                    ·
                      rfl

theorem cell23_7611209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_7611209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611209 prefixEnd_7611209 := by exact prefixLift 7611209
  have htrace : WordTrace (prefixWord ++ tailWord_7611209) baseStart_7611209 baseEnd_7611209 := by
    simpa [prefixWord, tailWord_7611209, baseEnd_7611209] using wordTrace_append hprefix tailTrace_7611209
  have hstable : (prefixWord ++ tailWord_7611209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611209).length < 2 ^ (prefixWord ++ tailWord_7611209).sum := by decide
  have hdescent : baseEnd_7611209 < baseStart_7611209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611213 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 6]
def baseStart_7611213 : Nat := 118140960795 + 7611213 * 2 ^ 59
def prefixEnd_7611213 : Nat := 4983230072969 + 3 ^ 40 * 7611213 * 2
def baseEnd_7611213 : Nat := 434245625861026091981575

theorem tailTrace_7611213 : CollatzResearch.WordTrace tailWord_7611213 prefixEnd_7611213 434245625861026091981575 := by
  unfold tailWord_7611213
  simp only [CollatzResearch.WordTrace]
  refine ⟨277603744174882667535846293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185069162783255111690564195 277603744174882667535846293)
  ·
    refine ⟨13012675508197625040742795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277603744174882667535846293 13012675508197625040742795)
    ·
      refine ⟨19519013262296437561114193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13012675508197625040742795 19519013262296437561114193)
      ·
        refine ⟨14639259946722328170835645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19519013262296437561114193 14639259946722328170835645)
        ·
          refine ⟨5489722480020873064063367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14639259946722328170835645 5489722480020873064063367)
          ·
            refine ⟨8234583720031309596095051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489722480020873064063367 8234583720031309596095051)
            ·
              refine ⟨12351875580046964394142577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234583720031309596095051 12351875580046964394142577)
              ·
                refine ⟨9263906685035223295606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12351875580046964394142577 9263906685035223295606933)
                ·
                  refine ⟨434245625861026091981575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9263906685035223295606933 434245625861026091981575)
                  ·
                    rfl

theorem cell23_7611213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_7611213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611213 prefixEnd_7611213 := by exact prefixLift 7611213
  have htrace : WordTrace (prefixWord ++ tailWord_7611213) baseStart_7611213 baseEnd_7611213 := by
    simpa [prefixWord, tailWord_7611213, baseEnd_7611213] using wordTrace_append hprefix tailTrace_7611213
  have hstable : (prefixWord ++ tailWord_7611213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611213).length < 2 ^ (prefixWord ++ tailWord_7611213).sum := by decide
  have hdescent : baseEnd_7611213 < baseStart_7611213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611215 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_7611215 : Nat := 118140960795 + 7611215 * 2 ^ 59
def prefixEnd_7611215 : Nat := 4983230072969 + 3 ^ 40 * 7611215 * 2
def baseEnd_7611215 : Nat := 3908211659710543820009165

theorem tailTrace_7611215 : CollatzResearch.WordTrace tailWord_7611215 prefixEnd_7611215 3908211659710543820009165 := by
  unfold tailWord_7611215
  simp only [CollatzResearch.WordTrace]
  refine ⟨277603817120875421877419099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185069211413916947918279399 277603817120875421877419099)
  ·
    refine ⟨416405725681313132816128649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277603817120875421877419099 416405725681313132816128649)
    ·
      refine ⟨312304294260984849612096487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416405725681313132816128649 312304294260984849612096487)
      ·
        refine ⟨468456441391477274418144731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312304294260984849612096487 468456441391477274418144731)
        ·
          refine ⟨702684662087215911627217097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468456441391477274418144731 702684662087215911627217097)
          ·
            refine ⟨527013496565411933720412823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702684662087215911627217097 527013496565411933720412823)
            ·
              refine ⟨790520244848117900580619235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527013496565411933720412823 790520244848117900580619235)
              ·
                refine ⟨1185780367272176850870928853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790520244848117900580619235 1185780367272176850870928853)
                ·
                  refine ⟨27791727357941644942287395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1185780367272176850870928853 27791727357941644942287395)
                  ·
                    refine ⟨41687591036912467413431093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27791727357941644942287395 41687591036912467413431093)
                    ·
                      refine ⟨3908211659710543820009165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41687591036912467413431093 3908211659710543820009165)
                      ·
                        rfl

theorem cell23_7611215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_7611215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611215 prefixEnd_7611215 := by exact prefixLift 7611215
  have htrace : WordTrace (prefixWord ++ tailWord_7611215) baseStart_7611215 baseEnd_7611215 := by
    simpa [prefixWord, tailWord_7611215, baseEnd_7611215] using wordTrace_append hprefix tailTrace_7611215
  have hstable : (prefixWord ++ tailWord_7611215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611215).length < 2 ^ (prefixWord ++ tailWord_7611215).sum := by decide
  have hdescent : baseEnd_7611215 < baseStart_7611215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611232 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_7611232 : Nat := 118140960795 + 7611232 * 2 ^ 59
def prefixEnd_7611232 : Nat := 4983230072969 + 3 ^ 40 * 7611232 * 2
def baseEnd_7611232 : Nat := 3908220388881670253496587

theorem tailTrace_7611232 : CollatzResearch.WordTrace tailWord_7611232 prefixEnd_7611232 3908220388881670253496587 := by
  unfold tailWord_7611232
  simp only [CollatzResearch.WordTrace]
  refine ⟨138802218580906916890393975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185069624774542555853858633 138802218580906916890393975)
  ·
    refine ⟨208203327871360375335590963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138802218580906916890393975 208203327871360375335590963)
    ·
      refine ⟨312304991807040563003386445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208203327871360375335590963 312304991807040563003386445)
      ·
        refine ⟨117114371927640211126269917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312304991807040563003386445 117114371927640211126269917)
        ·
          refine ⟨43917889472865079172351219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117114371927640211126269917 43917889472865079172351219)
          ·
            refine ⟨65876834209297618758526829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43917889472865079172351219 65876834209297618758526829)
            ·
              refine ⟨24703812828486607034447561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65876834209297618758526829 24703812828486607034447561)
              ·
                refine ⟨18527859621364955275835671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24703812828486607034447561 18527859621364955275835671)
                ·
                  refine ⟨27791789432047432913753507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527859621364955275835671 27791789432047432913753507)
                  ·
                    refine ⟨41687684148071149370630261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27791789432047432913753507 41687684148071149370630261)
                    ·
                      refine ⟨3908220388881670253496587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41687684148071149370630261 3908220388881670253496587)
                      ·
                        rfl

theorem cell23_7611232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_7611232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611232 prefixEnd_7611232 := by exact prefixLift 7611232
  have htrace : WordTrace (prefixWord ++ tailWord_7611232) baseStart_7611232 baseEnd_7611232 := by
    simpa [prefixWord, tailWord_7611232, baseEnd_7611232] using wordTrace_append hprefix tailTrace_7611232
  have hstable : (prefixWord ++ tailWord_7611232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611232).length < 2 ^ (prefixWord ++ tailWord_7611232).sum := by decide
  have hdescent : baseEnd_7611232 < baseStart_7611232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611239 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 6]
def baseStart_7611239 : Nat := 118140960795 + 7611239 * 2 ^ 59
def prefixEnd_7611239 : Nat := 4983230072969 + 3 ^ 40 * 7611239 * 2
def baseEnd_7611239 : Nat := 1302741327748750575369685

theorem tailTrace_7611239 : CollatzResearch.WordTrace tailWord_7611239 prefixEnd_7611239 1302741327748750575369685 := by
  unfold tailWord_7611239
  simp only [CollatzResearch.WordTrace]
  refine ⟨277604692472788473976292771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185069794981858982650861847 277604692472788473976292771)
  ·
    refine ⟨416407038709182710964439157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277604692472788473976292771 416407038709182710964439157)
    ·
      refine ⟨39038159878985879152916171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416407038709182710964439157 39038159878985879152916171)
      ·
        refine ⟨58557239818478818729374257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39038159878985879152916171 58557239818478818729374257)
        ·
          refine ⟨43917929863859114047030693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58557239818478818729374257 43917929863859114047030693)
          ·
            refine ⟨8234611849473583883818255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43917929863859114047030693 8234611849473583883818255)
            ·
              refine ⟨12351917774210375825727383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234611849473583883818255 12351917774210375825727383)
              ·
                refine ⟨18527876661315563738591075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351917774210375825727383 18527876661315563738591075)
                ·
                  refine ⟨27791814991973345607886613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18527876661315563738591075 27791814991973345607886613)
                  ·
                    refine ⟨1302741327748750575369685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27791814991973345607886613 1302741327748750575369685)
                    ·
                      rfl

theorem cell23_7611239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_7611239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611239 prefixEnd_7611239 := by exact prefixLift 7611239
  have htrace : WordTrace (prefixWord ++ tailWord_7611239) baseStart_7611239 baseEnd_7611239 := by
    simpa [prefixWord, tailWord_7611239, baseEnd_7611239] using wordTrace_append hprefix tailTrace_7611239
  have hstable : (prefixWord ++ tailWord_7611239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611239).length < 2 ^ (prefixWord ++ tailWord_7611239).sum := by decide
  have hdescent : baseEnd_7611239 < baseStart_7611239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611249 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_7611249 : Nat := 118140960795 + 7611249 * 2 ^ 59
def prefixEnd_7611249 : Nat := 4983230072969 + 3 ^ 40 * 7611249 * 2
def baseEnd_7611249 : Nat := 3908229118052796686984009

theorem tailTrace_7611249 : CollatzResearch.WordTrace tailWord_7611249 prefixEnd_7611249 3908229118052796686984009 := by
  unfold tailWord_7611249
  simp only [CollatzResearch.WordTrace]
  refine ⟨277605057202752245684156801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185070038135168163789437867 277605057202752245684156801)
  ·
    refine ⟨208203792902064184263117601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277605057202752245684156801 208203792902064184263117601)
    ·
      refine ⟨156152844676548138197338201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208203792902064184263117601 156152844676548138197338201)
      ·
        refine ⟨117114633507411103648003651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156152844676548138197338201 117114633507411103648003651)
        ·
          refine ⟨175671950261116655472005477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117114633507411103648003651 175671950261116655472005477)
          ·
            refine ⟨32938490673959372901001027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175671950261116655472005477 32938490673959372901001027)
            ·
              refine ⟨49407736010939059351501541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32938490673959372901001027 49407736010939059351501541)
              ·
                refine ⟨9263950502051073628406539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49407736010939059351501541 9263950502051073628406539)
                ·
                  refine ⟨13895925753076610442609809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9263950502051073628406539 13895925753076610442609809)
                  ·
                    refine ⟨10421944314807457831957357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13895925753076610442609809 10421944314807457831957357)
                    ·
                      refine ⟨3908229118052796686984009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10421944314807457831957357 3908229118052796686984009)
                      ·
                        rfl

theorem cell23_7611249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_7611249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611249 prefixEnd_7611249 := by exact prefixLift 7611249
  have htrace : WordTrace (prefixWord ++ tailWord_7611249) baseStart_7611249 baseEnd_7611249 := by
    simpa [prefixWord, tailWord_7611249, baseEnd_7611249] using wordTrace_append hprefix tailTrace_7611249
  have hstable : (prefixWord ++ tailWord_7611249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611249).length < 2 ^ (prefixWord ++ tailWord_7611249).sum := by decide
  have hdescent : baseEnd_7611249 < baseStart_7611249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611255 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_7611255 : Nat := 118140960795 + 7611255 * 2 ^ 59
def prefixEnd_7611255 : Nat := 4983230072969 + 3 ^ 40 * 7611255 * 2
def baseEnd_7611255 : Nat := 3908232198936723663508981

theorem tailTrace_7611255 : CollatzResearch.WordTrace tailWord_7611255 prefixEnd_7611255 3908232198936723663508981 := by
  unfold tailWord_7611255
  simp only [CollatzResearch.WordTrace]
  refine ⟨277605276040730508708875219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185070184027153672472583479 277605276040730508708875219)
  ·
    refine ⟨416407914061095763063312829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277605276040730508708875219 416407914061095763063312829)
    ·
      refine ⟨156152967772910911148742311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416407914061095763063312829 156152967772910911148742311)
      ·
        refine ⟨234229451659366366723113467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156152967772910911148742311 234229451659366366723113467)
        ·
          refine ⟨351344177489049550084670201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234229451659366366723113467 351344177489049550084670201)
          ·
            refine ⟨263508133116787162563502651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351344177489049550084670201 263508133116787162563502651)
            ·
              refine ⟨395262199675180743845253977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263508133116787162563502651 395262199675180743845253977)
              ·
                refine ⟨296446649756385557883940483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395262199675180743845253977 296446649756385557883940483)
                ·
                  refine ⟨444669974634578336825910725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296446649756385557883940483 444669974634578336825910725)
                  ·
                    refine ⟨83375620243983438154858261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444669974634578336825910725 83375620243983438154858261)
                    ·
                      refine ⟨3908232198936723663508981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83375620243983438154858261 3908232198936723663508981)
                      ·
                        rfl

theorem cell23_7611255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_7611255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611255 prefixEnd_7611255 := by exact prefixLift 7611255
  have htrace : WordTrace (prefixWord ++ tailWord_7611255) baseStart_7611255 baseEnd_7611255 := by
    simpa [prefixWord, tailWord_7611255, baseEnd_7611255] using wordTrace_append hprefix tailTrace_7611255
  have hstable : (prefixWord ++ tailWord_7611255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611255).length < 2 ^ (prefixWord ++ tailWord_7611255).sum := by decide
  have hdescent : baseEnd_7611255 < baseStart_7611255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611263 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 1, 2, 2]
def baseStart_7611263 : Nat := 118140960795 + 7611263 * 2 ^ 59
def prefixEnd_7611263 : Nat := 4983230072969 + 3 ^ 40 * 7611263 * 2
def baseEnd_7611263 : Nat := 3908236306781959632208945

theorem tailTrace_7611263 : CollatzResearch.WordTrace tailWord_7611263 prefixEnd_7611263 3908236306781959632208945 := by
  unfold tailWord_7611263
  simp only [CollatzResearch.WordTrace]
  refine ⟨277605567824701526075166443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185070378549801017383444295 277605567824701526075166443)
  ·
    refine ⟨416408351737052289112749665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277605567824701526075166443 416408351737052289112749665)
    ·
      refine ⟨312306263802789216834562249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416408351737052289112749665 312306263802789216834562249)
      ·
        refine ⟨234229697852091912625921687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312306263802789216834562249 234229697852091912625921687)
        ·
          refine ⟨351344546778137868938882531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234229697852091912625921687 351344546778137868938882531)
          ·
            refine ⟨527016820167206803408323797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351344546778137868938882531 527016820167206803408323797)
            ·
              refine ⟨12351956722668909454882589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 527016820167206803408323797 12351956722668909454882589)
              ·
                refine ⟨4631983771000841045580971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12351956722668909454882589 4631983771000841045580971)
                ·
                  refine ⟨6947975656501261568371457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4631983771000841045580971 6947975656501261568371457)
                  ·
                    refine ⟨5210981742375946176278593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6947975656501261568371457 5210981742375946176278593)
                    ·
                      refine ⟨3908236306781959632208945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210981742375946176278593 3908236306781959632208945)
                      ·
                        rfl

theorem cell23_7611263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_7611263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611263 prefixEnd_7611263 := by exact prefixLift 7611263
  have htrace : WordTrace (prefixWord ++ tailWord_7611263) baseStart_7611263 baseEnd_7611263 := by
    simpa [prefixWord, tailWord_7611263, baseEnd_7611263] using wordTrace_append hprefix tailTrace_7611263
  have hstable : (prefixWord ++ tailWord_7611263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611263).length < 2 ^ (prefixWord ++ tailWord_7611263).sum := by decide
  have hdescent : baseEnd_7611263 < baseStart_7611263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611286 : List Nat := [5, 3, 1, 1, 1, 1, 1, 10]
def baseStart_7611286 : Nat := 118140960795 + 7611286 * 2 ^ 59
def prefixEnd_7611286 : Nat := 4983230072969 + 3 ^ 40 * 7611286 * 2
def baseEnd_7611286 : Nat := 144749930253222705267457

theorem tailTrace_7611286 : CollatzResearch.WordTrace tailWord_7611286 prefixEnd_7611286 144749930253222705267457 := by
  unfold tailWord_7611286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17350400418976137562703357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185070937802412134002169141 17350400418976137562703357)
  ·
    refine ⟨6506400157116051586013759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17350400418976137562703357 6506400157116051586013759)
    ·
      refine ⟨9759600235674077379020639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6506400157116051586013759 9759600235674077379020639)
      ·
        refine ⟨14639400353511116068530959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9759600235674077379020639 14639400353511116068530959)
        ·
          refine ⟨21959100530266674102796439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14639400353511116068530959 21959100530266674102796439)
          ·
            refine ⟨32938650795400011154194659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959100530266674102796439 32938650795400011154194659)
            ·
              refine ⟨49407976193100016731291989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32938650795400011154194659 49407976193100016731291989)
              ·
                refine ⟨144749930253222705267457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49407976193100016731291989 144749930253222705267457)
                ·
                  rfl

theorem cell23_7611286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_7611286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611286 prefixEnd_7611286 := by exact prefixLift 7611286
  have htrace : WordTrace (prefixWord ++ tailWord_7611286) baseStart_7611286 baseEnd_7611286 := by
    simpa [prefixWord, tailWord_7611286, baseEnd_7611286] using wordTrace_append hprefix tailTrace_7611286
  have hstable : (prefixWord ++ tailWord_7611286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611286).length < 2 ^ (prefixWord ++ tailWord_7611286).sum := by decide
  have hdescent : baseEnd_7611286 < baseStart_7611286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611289 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 3, 3, 2]
def baseStart_7611289 : Nat := 118140960795 + 7611289 * 2 ^ 59
def prefixEnd_7611289 : Nat := 4983230072969 + 3 ^ 40 * 7611289 * 2
def baseEnd_7611289 : Nat := 3908249657278976530483825

theorem tailTrace_7611289 : CollatzResearch.WordTrace tailWord_7611289 prefixEnd_7611289 3908249657278976530483825 := by
  unfold tailWord_7611289
  simp only [CollatzResearch.WordTrace]
  refine ⟨277606516122607332515612921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185071010748404888343741947 277606516122607332515612921)
  ·
    refine ⟨208204887091955499386709691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277606516122607332515612921 208204887091955499386709691)
    ·
      refine ⟨312307330637933249080064537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208204887091955499386709691 312307330637933249080064537)
      ·
        refine ⟨234230497978449936810048403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312307330637933249080064537 234230497978449936810048403)
        ·
          refine ⟨351345746967674905215072605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234230497978449936810048403 351345746967674905215072605)
          ·
            refine ⟨131754655112878089455652227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351345746967674905215072605 131754655112878089455652227)
            ·
              refine ⟨197631982669317134183478341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131754655112878089455652227 197631982669317134183478341)
              ·
                refine ⟨37055996750496962659402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197631982669317134183478341 37055996750496962659402189)
                ·
                  refine ⟨13895998781436360997275821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37055996750496962659402189 13895998781436360997275821)
                  ·
                    refine ⟨5210999543038635373978433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13895998781436360997275821 5210999543038635373978433)
                    ·
                      refine ⟨3908249657278976530483825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5210999543038635373978433 3908249657278976530483825)
                      ·
                        rfl

theorem cell23_7611289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_7611289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611289 prefixEnd_7611289 := by exact prefixLift 7611289
  have htrace : WordTrace (prefixWord ++ tailWord_7611289) baseStart_7611289 baseEnd_7611289 := by
    simpa [prefixWord, tailWord_7611289, baseEnd_7611289] using wordTrace_append hprefix tailTrace_7611289
  have hstable : (prefixWord ++ tailWord_7611289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611289).length < 2 ^ (prefixWord ++ tailWord_7611289).sum := by decide
  have hdescent : baseEnd_7611289 < baseStart_7611289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611290 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_7611290 : Nat := 118140960795 + 7611290 * 2 ^ 59
def prefixEnd_7611290 : Nat := 4983230072969 + 3 ^ 40 * 7611290 * 2
def baseEnd_7611290 : Nat := 1302750056919877008857107

theorem tailTrace_7611290 : CollatzResearch.WordTrace tailWord_7611290 prefixEnd_7611290 1302750056919877008857107 := by
  unfold tailWord_7611290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401638148900927421599831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185071035063735806457599549 69401638148900927421599831)
  ·
    refine ⟨104102457223351391132399747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69401638148900927421599831 104102457223351391132399747)
    ·
      refine ⟨156153685835027086698599621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104102457223351391132399747 156153685835027086698599621)
      ·
        refine ⟨29278816094067578755987429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156153685835027086698599621 29278816094067578755987429)
        ·
          refine ⟨5489778017637671016747643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29278816094067578755987429 5489778017637671016747643)
          ·
            refine ⟨8234667026456506525121465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5489778017637671016747643 8234667026456506525121465)
            ·
              refine ⟨6176000269842379893841099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234667026456506525121465 6176000269842379893841099)
              ·
                refine ⟨9264000404763569840761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176000269842379893841099 9264000404763569840761649)
                ·
                  refine ⟨6948000303572677380571237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264000404763569840761649 6948000303572677380571237)
                  ·
                    refine ⟨1302750056919877008857107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948000303572677380571237 1302750056919877008857107)
                    ·
                      rfl

theorem cell23_7611290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_7611290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611290 prefixEnd_7611290 := by exact prefixLift 7611290
  have htrace : WordTrace (prefixWord ++ tailWord_7611290) baseStart_7611290 baseEnd_7611290 := by
    simpa [prefixWord, tailWord_7611290, baseEnd_7611290] using wordTrace_append hprefix tailTrace_7611290
  have hstable : (prefixWord ++ tailWord_7611290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611290).length < 2 ^ (prefixWord ++ tailWord_7611290).sum := by decide
  have hdescent : baseEnd_7611290 < baseStart_7611290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611319 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_7611319 : Nat := 118140960795 + 7611319 * 2 ^ 59
def prefixEnd_7611319 : Nat := 4983230072969 + 3 ^ 40 * 7611319 * 2
def baseEnd_7611319 : Nat := 3908265061698611413108687

theorem tailTrace_7611319 : CollatzResearch.WordTrace tailWord_7611319 prefixEnd_7611319 3908265061698611413108687 := by
  unfold tailWord_7611319
  simp only [CollatzResearch.WordTrace]
  refine ⟨277607610312498647639205011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185071740208332431759470007 277607610312498647639205011)
  ·
    refine ⟨416411415468747971458807517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277607610312498647639205011 416411415468747971458807517)
    ·
      refine ⟨156154280800780489297052819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416411415468747971458807517 156154280800780489297052819)
      ·
        refine ⟨234231421201170733945579229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156154280800780489297052819 234231421201170733945579229)
        ·
          refine ⟨87836782950439025229592211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234231421201170733945579229 87836782950439025229592211)
          ·
            refine ⟨131755174425658537844388317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87836782950439025229592211 131755174425658537844388317)
            ·
              refine ⟨49408190409621951691645619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131755174425658537844388317 49408190409621951691645619)
              ·
                refine ⟨74112285614432927537468429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49408190409621951691645619 74112285614432927537468429)
                ·
                  refine ⟨27792107105412347826550661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74112285614432927537468429 27792107105412347826550661)
                  ·
                    refine ⟨5211020082264815217478249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27792107105412347826550661 5211020082264815217478249)
                    ·
                      refine ⟨3908265061698611413108687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211020082264815217478249 3908265061698611413108687)
                      ·
                        rfl

theorem cell23_7611319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_7611319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611319 prefixEnd_7611319 := by exact prefixLift 7611319
  have htrace : WordTrace (prefixWord ++ tailWord_7611319) baseStart_7611319 baseEnd_7611319 := by
    simpa [prefixWord, tailWord_7611319, baseEnd_7611319] using wordTrace_append hprefix tailTrace_7611319
  have hstable : (prefixWord ++ tailWord_7611319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611319).length < 2 ^ (prefixWord ++ tailWord_7611319).sum := by decide
  have hdescent : baseEnd_7611319 < baseStart_7611319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611322 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_7611322 : Nat := 118140960795 + 7611322 * 2 ^ 59
def prefixEnd_7611322 : Nat := 4983230072969 + 3 ^ 40 * 7611322 * 2
def baseEnd_7611322 : Nat := 3908266602140574901371173

theorem tailTrace_7611322 : CollatzResearch.WordTrace tailWord_7611322 prefixEnd_7611322 3908266602140574901371173 := by
  unfold tailWord_7611322
  simp only [CollatzResearch.WordTrace]
  refine ⟨69401929932871944787891055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185071813154325186101042813 69401929932871944787891055)
  ·
    refine ⟨104102894899307917181836583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69401929932871944787891055 104102894899307917181836583)
    ·
      refine ⟨156154342348961875772754875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104102894899307917181836583 156154342348961875772754875)
      ·
        refine ⟨234231513523442813659132313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156154342348961875772754875 234231513523442813659132313)
        ·
          refine ⟨175673635142582110244349235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234231513523442813659132313 175673635142582110244349235)
          ·
            refine ⟨263510452713873165366523853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175673635142582110244349235 263510452713873165366523853)
            ·
              refine ⟨98816419767702437012446445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263510452713873165366523853 98816419767702437012446445)
              ·
                refine ⟨37056157412888413879667417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98816419767702437012446445 37056157412888413879667417)
                ·
                  refine ⟨27792118059666310409750563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37056157412888413879667417 27792118059666310409750563)
                  ·
                    refine ⟨41688177089499465614625845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27792118059666310409750563 41688177089499465614625845)
                    ·
                      refine ⟨3908266602140574901371173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41688177089499465614625845 3908266602140574901371173)
                      ·
                        rfl

theorem cell23_7611322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_7611322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611322 prefixEnd_7611322 := by exact prefixLift 7611322
  have htrace : WordTrace (prefixWord ++ tailWord_7611322) baseStart_7611322 baseEnd_7611322 := by
    simpa [prefixWord, tailWord_7611322, baseEnd_7611322] using wordTrace_append hprefix tailTrace_7611322
  have hstable : (prefixWord ++ tailWord_7611322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611322).length < 2 ^ (prefixWord ++ tailWord_7611322).sum := by decide
  have hdescent : baseEnd_7611322 < baseStart_7611322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611353 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 2, 2, 2]
def baseStart_7611353 : Nat := 118140960795 + 7611353 * 2 ^ 59
def prefixEnd_7611353 : Nat := 4983230072969 + 3 ^ 40 * 7611353 * 2
def baseEnd_7611353 : Nat := 3908282520040864280083531

theorem tailTrace_7611353 : CollatzResearch.WordTrace tailWord_7611353 prefixEnd_7611353 3908282520040864280083531 := by
  unfold tailWord_7611353
  simp only [CollatzResearch.WordTrace]
  refine ⟨277608850394375471445942713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185072566929583647630628475 277608850394375471445942713)
  ·
    refine ⟨208206637795781603584457035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277608850394375471445942713 208206637795781603584457035)
    ·
      refine ⟨312309956693672405376685553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208206637795781603584457035 312309956693672405376685553)
      ·
        refine ⟨234232467520254304032514165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312309956693672405376685553 234232467520254304032514165)
        ·
          refine ⟨21959293830023841003048203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234232467520254304032514165 21959293830023841003048203)
          ·
            refine ⟨32938940745035761504572305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959293830023841003048203 32938940745035761504572305)
            ·
              refine ⟨24704205558776821128429229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32938940745035761504572305 24704205558776821128429229)
              ·
                refine ⟨9264077084541307923160961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24704205558776821128429229 9264077084541307923160961)
                ·
                  refine ⟨6948057813405980942370721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264077084541307923160961 6948057813405980942370721)
                  ·
                    refine ⟨5211043360054485706778041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6948057813405980942370721 5211043360054485706778041)
                    ·
                      refine ⟨3908282520040864280083531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211043360054485706778041 3908282520040864280083531)
                      ·
                        rfl

theorem cell23_7611353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_7611353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611353 prefixEnd_7611353 := by exact prefixLift 7611353
  have htrace : WordTrace (prefixWord ++ tailWord_7611353) baseStart_7611353 baseEnd_7611353 := by
    simpa [prefixWord, tailWord_7611353, baseEnd_7611353] using wordTrace_append hprefix tailTrace_7611353
  have hstable : (prefixWord ++ tailWord_7611353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611353).length < 2 ^ (prefixWord ++ tailWord_7611353).sum := by decide
  have hdescent : baseEnd_7611353 < baseStart_7611353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611359 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 7]
def baseStart_7611359 : Nat := 118140960795 + 7611359 * 2 ^ 59
def prefixEnd_7611359 : Nat := 4983230072969 + 3 ^ 40 * 7611359 * 2
def baseEnd_7611359 : Nat := 434253955658310139623167

theorem tailTrace_7611359 : CollatzResearch.WordTrace tailWord_7611359 prefixEnd_7611359 434253955658310139623167 := by
  unfold tailWord_7611359
  simp only [CollatzResearch.WordTrace]
  refine ⟨277609069232353734470661131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185072712821569156313774087 277609069232353734470661131)
  ·
    refine ⟨416413603848530601705991697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277609069232353734470661131 416413603848530601705991697)
    ·
      refine ⟨312310202886397951279493773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416413603848530601705991697 312310202886397951279493773)
      ·
        refine ⟨117116326082399231729810165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312310202886397951279493773 117116326082399231729810165)
        ·
          refine ⟨10979655570224927974669703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117116326082399231729810165 10979655570224927974669703)
          ·
            refine ⟨16469483355337391962004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979655570224927974669703 16469483355337391962004555)
            ·
              refine ⟨24704225033006087943006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16469483355337391962004555 24704225033006087943006833)
              ·
                refine ⟨18528168774754565957255125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24704225033006087943006833 18528168774754565957255125)
                ·
                  refine ⟨434253955658310139623167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18528168774754565957255125 434253955658310139623167)
                  ·
                    rfl

theorem cell23_7611359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 7].length) (baseStart_7611359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611359 prefixEnd_7611359 := by exact prefixLift 7611359
  have htrace : WordTrace (prefixWord ++ tailWord_7611359) baseStart_7611359 baseEnd_7611359 := by
    simpa [prefixWord, tailWord_7611359, baseEnd_7611359] using wordTrace_append hprefix tailTrace_7611359
  have hstable : (prefixWord ++ tailWord_7611359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611359).length < 2 ^ (prefixWord ++ tailWord_7611359).sum := by decide
  have hdescent : baseEnd_7611359 < baseStart_7611359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611429 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 3]
def baseStart_7611429 : Nat := 118140960795 + 7611429 * 2 ^ 59
def prefixEnd_7611429 : Nat := 4983230072969 + 3 ^ 40 * 7611429 * 2
def baseEnd_7611429 : Nat := 3908321544570605982733181

theorem tailTrace_7611429 : CollatzResearch.WordTrace tailWord_7611429 prefixEnd_7611429 3908321544570605982733181 := by
  unfold tailWord_7611429
  simp only [CollatzResearch.WordTrace]
  refine ⟨277611622342100136425709341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185074414894733424283806227 277611622342100136425709341)
  ·
    refine ⟨104104358378287551159641003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277611622342100136425709341 104104358378287551159641003)
    ·
      refine ⟨156156537567431326739461505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104104358378287551159641003 156156537567431326739461505)
      ·
        refine ⟨117117403175573495054596129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156156537567431326739461505 117117403175573495054596129)
        ·
          refine ⟨87838052381680121290947097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117117403175573495054596129 87838052381680121290947097)
          ·
            refine ⟨65878539286260090968210323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87838052381680121290947097 65878539286260090968210323)
            ·
              refine ⟨98817808929390136452315485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65878539286260090968210323 98817808929390136452315485)
              ·
                refine ⟨37056678348521301169618307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98817808929390136452315485 37056678348521301169618307)
                ·
                  refine ⟨55585017522781951754427461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37056678348521301169618307 55585017522781951754427461)
                  ·
                    refine ⟨10422190785521615953955149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55585017522781951754427461 10422190785521615953955149)
                    ·
                      refine ⟨3908321544570605982733181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422190785521615953955149 3908321544570605982733181)
                      ·
                        rfl

theorem cell23_7611429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_7611429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611429 prefixEnd_7611429 := by exact prefixLift 7611429
  have htrace : WordTrace (prefixWord ++ tailWord_7611429) baseStart_7611429 baseEnd_7611429 := by
    simpa [prefixWord, tailWord_7611429, baseEnd_7611429] using wordTrace_append hprefix tailTrace_7611429
  have hstable : (prefixWord ++ tailWord_7611429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611429).length < 2 ^ (prefixWord ++ tailWord_7611429).sum := by decide
  have hdescent : baseEnd_7611429 < baseStart_7611429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611449 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 8]
def baseStart_7611449 : Nat := 118140960795 + 7611449 * 2 ^ 59
def prefixEnd_7611449 : Nat := 4983230072969 + 3 ^ 40 * 7611449 * 2
def baseEnd_7611449 : Nat := 434259090464855100498121

theorem tailTrace_7611449 : CollatzResearch.WordTrace tailWord_7611449 prefixEnd_7611449 434259090464855100498121 := by
  unfold tailWord_7611449
  simp only [CollatzResearch.WordTrace]
  refine ⟨277612351802027679841437401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185074901201351786560958267 277612351802027679841437401)
  ·
    refine ⟨208209263851520759881078051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277612351802027679841437401 208209263851520759881078051)
    ·
      refine ⟨312313895777281139821617077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208209263851520759881078051 312313895777281139821617077)
      ·
        refine ⟨29279427729120106858276601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312313895777281139821617077 29279427729120106858276601)
        ·
          refine ⟨21959570796840080143707451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29279427729120106858276601 21959570796840080143707451)
          ·
            refine ⟨32939356195260120215561177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959570796840080143707451 32939356195260120215561177)
            ·
              refine ⟨24704517146445090161670883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32939356195260120215561177 24704517146445090161670883)
              ·
                refine ⟨37056775719667635242506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24704517146445090161670883 37056775719667635242506325)
                ·
                  refine ⟨434259090464855100498121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37056775719667635242506325 434259090464855100498121)
                  ·
                    rfl

theorem cell23_7611449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_7611449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611449 prefixEnd_7611449 := by exact prefixLift 7611449
  have htrace : WordTrace (prefixWord ++ tailWord_7611449) baseStart_7611449 baseEnd_7611449 := by
    simpa [prefixWord, tailWord_7611449, baseEnd_7611449] using wordTrace_append hprefix tailTrace_7611449
  have hstable : (prefixWord ++ tailWord_7611449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611449).length < 2 ^ (prefixWord ++ tailWord_7611449).sum := by decide
  have hdescent : baseEnd_7611449 < baseStart_7611449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611453 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_7611453 : Nat := 118140960795 + 7611453 * 2 ^ 59
def prefixEnd_7611453 : Nat := 4983230072969 + 3 ^ 40 * 7611453 * 2
def baseEnd_7611453 : Nat := 1302777956035437962944357

theorem tailTrace_7611453 : CollatzResearch.WordTrace tailWord_7611453 prefixEnd_7611453 1302777956035437962944357 := by
  unfold tailWord_7611453
  simp only [CollatzResearch.WordTrace]
  refine ⟨277612497694013188524583013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185074998462675459016388675 277612497694013188524583013)
  ·
    refine ⟨52052343317627472848359315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277612497694013188524583013 52052343317627472848359315)
    ·
      refine ⟨78078514976441209272538973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52052343317627472848359315 78078514976441209272538973)
      ·
        refine ⟨29279443116165453477202115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78078514976441209272538973 29279443116165453477202115)
        ·
          refine ⟨43919164674248180215803173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29279443116165453477202115 43919164674248180215803173)
          ·
            refine ⟨8234843376421533790463095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43919164674248180215803173 8234843376421533790463095)
            ·
              refine ⟨12352265064632300685694643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8234843376421533790463095 12352265064632300685694643)
              ·
                refine ⟨18528397596948451028541965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12352265064632300685694643 18528397596948451028541965)
                ·
                  refine ⟨6948149098855669135703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18528397596948451028541965 6948149098855669135703237)
                  ·
                    refine ⟨1302777956035437962944357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6948149098855669135703237 1302777956035437962944357)
                    ·
                      rfl

theorem cell23_7611453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_7611453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611453 prefixEnd_7611453 := by exact prefixLift 7611453
  have htrace : WordTrace (prefixWord ++ tailWord_7611453) baseStart_7611453 baseEnd_7611453 := by
    simpa [prefixWord, tailWord_7611453, baseEnd_7611453] using wordTrace_append hprefix tailTrace_7611453
  have hstable : (prefixWord ++ tailWord_7611453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611453).length < 2 ^ (prefixWord ++ tailWord_7611453).sum := by decide
  have hdescent : baseEnd_7611453 < baseStart_7611453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611466 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_7611466 : Nat := 118140960795 + 7611466 * 2 ^ 59
def prefixEnd_7611466 : Nat := 4983230072969 + 3 ^ 40 * 7611466 * 2
def baseEnd_7611466 : Nat := 434260060372758037552279

theorem tailTrace_7611466 : CollatzResearch.WordTrace tailWord_7611466 prefixEnd_7611466 434260060372758037552279 := by
  unfold tailWord_7611466
  simp only [CollatzResearch.WordTrace]
  refine ⟨69403242960741522936201563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185075314561977394496537501 69403242960741522936201563)
  ·
    refine ⟨104104864441112284404302345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69403242960741522936201563 104104864441112284404302345)
    ·
      refine ⟨78078648330834213303226759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104104864441112284404302345 78078648330834213303226759)
      ·
        refine ⟨117117972496251319954840139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78078648330834213303226759 117117972496251319954840139)
        ·
          refine ⟨175676958744376979932260209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117117972496251319954840139 175676958744376979932260209)
          ·
            refine ⟨131757719058282734949195157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175676958744376979932260209 131757719058282734949195157)
            ·
              refine ⟨6176143080857003200743523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131757719058282734949195157 6176143080857003200743523)
              ·
                refine ⟨9264214621285504801115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176143080857003200743523 9264214621285504801115285)
                ·
                  refine ⟨434260060372758037552279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9264214621285504801115285 434260060372758037552279)
                  ·
                    rfl

theorem cell23_7611466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_7611466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611466 prefixEnd_7611466 := by exact prefixLift 7611466
  have htrace : WordTrace (prefixWord ++ tailWord_7611466) baseStart_7611466 baseEnd_7611466 := by
    simpa [prefixWord, tailWord_7611466, baseEnd_7611466] using wordTrace_append hprefix tailTrace_7611466
  have hstable : (prefixWord ++ tailWord_7611466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611466).length < 2 ^ (prefixWord ++ tailWord_7611466).sum := by decide
  have hdescent : baseEnd_7611466 < baseStart_7611466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611550 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7611550 : Nat := 118140960795 + 7611550 * 2 ^ 59
def prefixEnd_7611550 : Nat := 4983230072969 + 3 ^ 40 * 7611550 * 2
def baseEnd_7611550 : Nat := 3908383675729800009320125

theorem tailTrace_7611550 : CollatzResearch.WordTrace tailWord_7611550 prefixEnd_7611550 3908383675729800009320125 := by
  unfold tailWord_7611550
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702004446832721761358013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185077357049774516060576069 34702004446832721761358013)
  ·
    refine ⟨13013251667562270660509255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34702004446832721761358013 13013251667562270660509255)
    ·
      refine ⟨19519877501343405990763883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013251667562270660509255 19519877501343405990763883)
      ·
        refine ⟨29279816252015108986145825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19519877501343405990763883 29279816252015108986145825)
        ·
          refine ⟨21959862189011331739609369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29279816252015108986145825 21959862189011331739609369)
          ·
            refine ⟨16469896641758498804707027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21959862189011331739609369 16469896641758498804707027)
            ·
              refine ⟨24704844962637748207060541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16469896641758498804707027 24704844962637748207060541)
              ·
                refine ⟨9264316860989155577647703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24704844962637748207060541 9264316860989155577647703)
                ·
                  refine ⟨13896475291483733366471555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264316860989155577647703 13896475291483733366471555)
                  ·
                    refine ⟨20844712937225600049707333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13896475291483733366471555 20844712937225600049707333)
                    ·
                      refine ⟨3908383675729800009320125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20844712937225600049707333 3908383675729800009320125)
                      ·
                        rfl

theorem cell23_7611550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7611550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611550 prefixEnd_7611550 := by exact prefixLift 7611550
  have htrace : WordTrace (prefixWord ++ tailWord_7611550) baseStart_7611550 baseEnd_7611550 := by
    simpa [prefixWord, tailWord_7611550, baseEnd_7611550] using wordTrace_append hprefix tailTrace_7611550
  have hstable : (prefixWord ++ tailWord_7611550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611550).length < 2 ^ (prefixWord ++ tailWord_7611550).sum := by decide
  have hdescent : baseEnd_7611550 < baseStart_7611550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611553 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7611553 : Nat := 118140960795 + 7611553 * 2 ^ 59
def prefixEnd_7611553 : Nat := 4983230072969 + 3 ^ 40 * 7611553 * 2
def baseEnd_7611553 : Nat := 3908385216171763497582611

theorem tailTrace_7611553 : CollatzResearch.WordTrace tailWord_7611553 prefixEnd_7611553 3908385216171763497582611 := by
  unfold tailWord_7611553
  simp only [CollatzResearch.WordTrace]
  refine ⟨277616144993650905603223313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185077429995767270402148875 277616144993650905603223313)
  ·
    refine ⟨208212108745238179202417485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277616144993650905603223313 208212108745238179202417485)
    ·
      refine ⟨78079540779464317200906557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208212108745238179202417485 78079540779464317200906557)
      ·
        refine ⟨29279827792299118950339959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78079540779464317200906557 29279827792299118950339959)
        ·
          refine ⟨43919741688448678425509939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29279827792299118950339959 43919741688448678425509939)
          ·
            refine ⟨65879612532673017638264909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43919741688448678425509939 65879612532673017638264909)
            ·
              refine ⟨24704854699752381614349341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65879612532673017638264909 24704854699752381614349341)
              ·
                refine ⟨9264320512407143105381003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24704854699752381614349341 9264320512407143105381003)
                ·
                  refine ⟨13896480768610714658071505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264320512407143105381003 13896480768610714658071505)
                  ·
                    refine ⟨10422360576458035993553629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13896480768610714658071505 10422360576458035993553629)
                    ·
                      refine ⟨3908385216171763497582611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422360576458035993553629 3908385216171763497582611)
                      ·
                        rfl

theorem cell23_7611553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7611553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611553 prefixEnd_7611553 := by exact prefixLift 7611553
  have htrace : WordTrace (prefixWord ++ tailWord_7611553) baseStart_7611553 baseEnd_7611553 := by
    simpa [prefixWord, tailWord_7611553, baseEnd_7611553] using wordTrace_append hprefix tailTrace_7611553
  have hstable : (prefixWord ++ tailWord_7611553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611553).length < 2 ^ (prefixWord ++ tailWord_7611553).sum := by decide
  have hdescent : baseEnd_7611553 < baseStart_7611553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611576 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2]
def baseStart_7611576 : Nat := 118140960795 + 7611576 * 2 ^ 59
def prefixEnd_7611576 : Nat := 4983230072969 + 3 ^ 40 * 7611576 * 2
def baseEnd_7611576 : Nat := 3908397026226816907595005

theorem tailTrace_7611576 : CollatzResearch.WordTrace tailWord_7611576 prefixEnd_7611576 3908397026226816907595005 := by
  unfold tailWord_7611576
  simp only [CollatzResearch.WordTrace]
  refine ⟨138808491936283790265655291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185077989248378387020873721 138808491936283790265655291)
  ·
    refine ⟨208212737904425685398482937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138808491936283790265655291 208212737904425685398482937)
    ·
      refine ⟨156159553428319264048862203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208212737904425685398482937 156159553428319264048862203)
      ·
        refine ⟨234239330142478896073293305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156159553428319264048862203 234239330142478896073293305)
        ·
          refine ⟨175679497606859172054969979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234239330142478896073293305 175679497606859172054969979)
          ·
            refine ⟨263519246410288758082454969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175679497606859172054969979 263519246410288758082454969)
            ·
              refine ⟨197639434807716568561841227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263519246410288758082454969 197639434807716568561841227)
              ·
                refine ⟨296459152211574852842761841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197639434807716568561841227 296459152211574852842761841)
                ·
                  refine ⟨222344364158681139632071381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296459152211574852842761841 222344364158681139632071381)
                  ·
                    refine ⟨5211196034969089210126673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222344364158681139632071381 5211196034969089210126673)
                    ·
                      refine ⟨3908397026226816907595005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211196034969089210126673 3908397026226816907595005)
                      ·
                        rfl

theorem cell23_7611576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_7611576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611576 prefixEnd_7611576 := by exact prefixLift 7611576
  have htrace : WordTrace (prefixWord ++ tailWord_7611576) baseStart_7611576 baseEnd_7611576 := by
    simpa [prefixWord, tailWord_7611576, baseEnd_7611576] using wordTrace_append hprefix tailTrace_7611576
  have hstable : (prefixWord ++ tailWord_7611576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611576).length < 2 ^ (prefixWord ++ tailWord_7611576).sum := by decide
  have hdescent : baseEnd_7611576 < baseStart_7611576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611583 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_7611583 : Nat := 118140960795 + 7611583 * 2 ^ 59
def prefixEnd_7611583 : Nat := 4983230072969 + 3 ^ 40 * 7611583 * 2
def baseEnd_7611583 : Nat := 3908400620591398380207473

theorem tailTrace_7611583 : CollatzResearch.WordTrace tailWord_7611583 prefixEnd_7611583 3908400620591398380207473 := by
  unfold tailWord_7611583
  simp only [CollatzResearch.WordTrace]
  refine ⟨277617239183542220726815403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185078159455694813817876935 277617239183542220726815403)
  ·
    refine ⟨416425858775313331090223105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277617239183542220726815403 416425858775313331090223105)
    ·
      refine ⟨312319394081484998317667329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416425858775313331090223105 312319394081484998317667329)
      ·
        refine ⟨234239545561113748738250497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312319394081484998317667329 234239545561113748738250497)
        ·
          refine ⟨175679659170835311553687873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234239545561113748738250497 175679659170835311553687873)
          ·
            refine ⟨131759744378126483665265905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175679659170835311553687873 131759744378126483665265905)
            ·
              refine ⟨98819808283594862748949429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131759744378126483665265905 98819808283594862748949429)
              ·
                refine ⟨9264357026587018382714009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98819808283594862748949429 9264357026587018382714009)
                ·
                  refine ⟨6948267769940263787035507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264357026587018382714009 6948267769940263787035507)
                  ·
                    refine ⟨10422401654910395680553261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948267769940263787035507 10422401654910395680553261)
                    ·
                      refine ⟨3908400620591398380207473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422401654910395680553261 3908400620591398380207473)
                      ·
                        rfl

theorem cell23_7611583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_7611583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611583 prefixEnd_7611583 := by exact prefixLift 7611583
  have htrace : WordTrace (prefixWord ++ tailWord_7611583) baseStart_7611583 baseEnd_7611583 := by
    simpa [prefixWord, tailWord_7611583, baseEnd_7611583] using wordTrace_append hprefix tailTrace_7611583
  have hstable : (prefixWord ++ tailWord_7611583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611583).length < 2 ^ (prefixWord ++ tailWord_7611583).sum := by decide
  have hdescent : baseEnd_7611583 < baseStart_7611583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611599 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 6]
def baseStart_7611599 : Nat := 118140960795 + 7611599 * 2 ^ 59
def prefixEnd_7611599 : Nat := 4983230072969 + 3 ^ 40 * 7611599 * 2
def baseEnd_7611599 : Nat := 1302802945427290105869133

theorem tailTrace_7611599 : CollatzResearch.WordTrace tailWord_7611599 prefixEnd_7611599 1302802945427290105869133 := by
  unfold tailWord_7611599
  simp only [CollatzResearch.WordTrace]
  refine ⟨277617822751484255459397851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185078548500989503639598567 277617822751484255459397851)
  ·
    refine ⟨416426734127226383189096777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277617822751484255459397851 416426734127226383189096777)
    ·
      refine ⟨312320050595419787391822583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416426734127226383189096777 312320050595419787391822583)
      ·
        refine ⟨468480075893129681087733875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312320050595419787391822583 468480075893129681087733875)
        ·
          refine ⟨702720113839694521631600813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468480075893129681087733875 702720113839694521631600813)
          ·
            refine ⟨263520042689885445611850305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702720113839694521631600813 263520042689885445611850305)
            ·
              refine ⟨197640032017414084208887729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263520042689885445611850305 197640032017414084208887729)
              ·
                refine ⟨148230024013060563156665797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197640032017414084208887729 148230024013060563156665797)
                ·
                  refine ⟨27793129502448855591874837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148230024013060563156665797 27793129502448855591874837)
                  ·
                    refine ⟨1302802945427290105869133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27793129502448855591874837 1302802945427290105869133)
                    ·
                      rfl

theorem cell23_7611599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_7611599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611599 prefixEnd_7611599 := by exact prefixLift 7611599
  have htrace : WordTrace (prefixWord ++ tailWord_7611599) baseStart_7611599 baseEnd_7611599 := by
    simpa [prefixWord, tailWord_7611599, baseEnd_7611599] using wordTrace_append hprefix tailTrace_7611599
  have hstable : (prefixWord ++ tailWord_7611599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611599).length < 2 ^ (prefixWord ++ tailWord_7611599).sum := by decide
  have hdescent : baseEnd_7611599 < baseStart_7611599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611634 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7611634 : Nat := 118140960795 + 7611634 * 2 ^ 59
def prefixEnd_7611634 : Nat := 4983230072969 + 3 ^ 40 * 7611634 * 2
def baseEnd_7611634 : Nat := 3908426808104777680669739

theorem tailTrace_7611634 : CollatzResearch.WordTrace tailWord_7611634 prefixEnd_7611634 3908426808104777680669739 := by
  unfold tailWord_7611634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69404774826589364109230489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185079399537571637624614637 69404774826589364109230489)
  ·
    refine ⟨52053581119942023081922867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69404774826589364109230489 52053581119942023081922867)
    ·
      refine ⟨78080371679913034622884301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52053581119942023081922867 78080371679913034622884301)
      ·
        refine ⟨29280139379967387983581613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78080371679913034622884301 29280139379967387983581613)
        ·
          refine ⟨10980052267487770493843105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29280139379967387983581613 10980052267487770493843105)
          ·
            refine ⟨8235039200615827870382329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10980052267487770493843105 8235039200615827870382329)
            ·
              refine ⟨6176279400461870902786747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8235039200615827870382329 6176279400461870902786747)
              ·
                refine ⟨9264419100692806354180121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6176279400461870902786747 9264419100692806354180121)
                ·
                  refine ⟨6948314325519604765635091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9264419100692806354180121 6948314325519604765635091)
                  ·
                    refine ⟨10422471488279407148452637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6948314325519604765635091 10422471488279407148452637)
                    ·
                      refine ⟨3908426808104777680669739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422471488279407148452637 3908426808104777680669739)
                      ·
                        rfl

theorem cell23_7611634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7611634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611634 prefixEnd_7611634 := by exact prefixLift 7611634
  have htrace : WordTrace (prefixWord ++ tailWord_7611634) baseStart_7611634 baseEnd_7611634 := by
    simpa [prefixWord, tailWord_7611634, baseEnd_7611634] using wordTrace_append hprefix tailTrace_7611634
  have hstable : (prefixWord ++ tailWord_7611634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611634).length < 2 ^ (prefixWord ++ tailWord_7611634).sum := by decide
  have hdescent : baseEnd_7611634 < baseStart_7611634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_7611639 : Nat := 118140960795 + 7611639 * 2 ^ 59
def prefixEnd_7611639 : Nat := 4983230072969 + 3 ^ 40 * 7611639 * 2
def baseEnd_7611639 : Nat := 3908429375508050161107215

theorem tailTrace_7611639 : CollatzResearch.WordTrace tailWord_7611639 prefixEnd_7611639 3908429375508050161107215 := by
  unfold tailWord_7611639
  simp only [CollatzResearch.WordTrace]
  refine ⟨277619281671339342290853971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185079521114226228193902647 277619281671339342290853971)
  ·
    refine ⟨416428922507009013436280957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277619281671339342290853971 416428922507009013436280957)
    ·
      refine ⟨156160845940128380038605359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416428922507009013436280957 156160845940128380038605359)
      ·
        refine ⟨234241268910192570057908039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156160845940128380038605359 234241268910192570057908039)
        ·
          refine ⟨351361903365288855086862059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234241268910192570057908039 351361903365288855086862059)
          ·
            refine ⟨527042855047933282630293089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351361903365288855086862059 527042855047933282630293089)
            ·
              refine ⟨395282141285949961972719817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527042855047933282630293089 395282141285949961972719817)
              ·
                refine ⟨296461605964462471479539863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395282141285949961972719817 296461605964462471479539863)
                ·
                  refine ⟨444692408946693707219309795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296461605964462471479539863 444692408946693707219309795)
                  ·
                    refine ⟨667038613420040560828964693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 444692408946693707219309795 667038613420040560828964693)
                    ·
                      refine ⟨3908429375508050161107215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 667038613420040560828964693 3908429375508050161107215)
                      ·
                        rfl

theorem cell23_7611639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_7611639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611639 prefixEnd_7611639 := by exact prefixLift 7611639
  have htrace : WordTrace (prefixWord ++ tailWord_7611639) baseStart_7611639 baseEnd_7611639 := by
    simpa [prefixWord, tailWord_7611639, baseEnd_7611639] using wordTrace_append hprefix tailTrace_7611639
  have hstable : (prefixWord ++ tailWord_7611639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611639).length < 2 ^ (prefixWord ++ tailWord_7611639).sum := by decide
  have hdescent : baseEnd_7611639 < baseStart_7611639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611644 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_7611644 : Nat := 118140960795 + 7611644 * 2 ^ 59
def prefixEnd_7611644 : Nat := 4983230072969 + 3 ^ 40 * 7611644 * 2
def baseEnd_7611644 : Nat := 3908431942911322641544693

theorem tailTrace_7611644 : CollatzResearch.WordTrace tailWord_7611644 prefixEnd_7611644 3908431942911322641544693 := by
  unfold tailWord_7611644
  simp only [CollatzResearch.WordTrace]
  refine ⟨138809732018160614072392993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185079642690880818763190657 138809732018160614072392993)
  ·
    refine ⟨104107299013620460554294745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138809732018160614072392993 104107299013620460554294745)
    ·
      refine ⟨78080474260215345415721059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104107299013620460554294745 78080474260215345415721059)
      ·
        refine ⟨117120711390323018123581589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78080474260215345415721059 117120711390323018123581589)
        ·
          refine ⟨5490033346421391474542887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117120711390323018123581589 5490033346421391474542887)
          ·
            refine ⟨8235050019632087211814331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490033346421391474542887 8235050019632087211814331)
            ·
              refine ⟨12352575029448130817721497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235050019632087211814331 12352575029448130817721497)
              ·
                refine ⟨9264431272086098113291123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12352575029448130817721497 9264431272086098113291123)
                ·
                  refine ⟨13896646908129147169936685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9264431272086098113291123 13896646908129147169936685)
                  ·
                    refine ⟨5211242590548430188726257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13896646908129147169936685 5211242590548430188726257)
                    ·
                      refine ⟨3908431942911322641544693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211242590548430188726257 3908431942911322641544693)
                      ·
                        rfl

theorem cell23_7611644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_7611644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611644 prefixEnd_7611644 := by exact prefixLift 7611644
  have htrace : WordTrace (prefixWord ++ tailWord_7611644) baseStart_7611644 baseEnd_7611644 := by
    simpa [prefixWord, tailWord_7611644, baseEnd_7611644] using wordTrace_append hprefix tailTrace_7611644
  have hstable : (prefixWord ++ tailWord_7611644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611644).length < 2 ^ (prefixWord ++ tailWord_7611644).sum := by decide
  have hdescent : baseEnd_7611644 < baseStart_7611644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611680 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 5]
def baseStart_7611680 : Nat := 118140960795 + 7611680 * 2 ^ 59
def prefixEnd_7611680 : Nat := 4983230072969 + 3 ^ 40 * 7611680 * 2
def baseEnd_7611680 : Nat := 434272269801653833410503

theorem tailTrace_7611680 : CollatzResearch.WordTrace tailWord_7611680 prefixEnd_7611680 434272269801653833410503 := by
  unfold tailWord_7611680
  simp only [CollatzResearch.WordTrace]
  refine ⟨138810388532095403146548247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185080518042793870862064329 138810388532095403146548247)
  ·
    refine ⟨208215582798143104719822371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138810388532095403146548247 208215582798143104719822371)
    ·
      refine ⟨312323374197214657079733557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208215582798143104719822371 312323374197214657079733557)
      ·
        refine ⟨29280316330988874101225021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312323374197214657079733557 29280316330988874101225021)
        ·
          refine ⟨10980118624120827787959383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29280316330988874101225021 10980118624120827787959383)
          ·
            refine ⟨16470177936181241681939075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10980118624120827787959383 16470177936181241681939075)
            ·
              refine ⟨24705266904271862522908613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470177936181241681939075 24705266904271862522908613)
              ·
                refine ⟨4632237544550974223045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24705266904271862522908613 4632237544550974223045365)
                ·
                  refine ⟨434272269801653833410503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4632237544550974223045365 434272269801653833410503)
                  ·
                    rfl

theorem cell23_7611680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 5].length) (baseStart_7611680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611680 prefixEnd_7611680 := by exact prefixLift 7611680
  have htrace : WordTrace (prefixWord ++ tailWord_7611680) baseStart_7611680 baseEnd_7611680 := by
    simpa [prefixWord, tailWord_7611680, baseEnd_7611680] using wordTrace_append hprefix tailTrace_7611680
  have hstable : (prefixWord ++ tailWord_7611680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611680).length < 2 ^ (prefixWord ++ tailWord_7611680).sum := by decide
  have hdescent : baseEnd_7611680 < baseStart_7611680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611683 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 5, 2]
def baseStart_7611683 : Nat := 118140960795 + 7611683 * 2 ^ 59
def prefixEnd_7611683 : Nat := 4983230072969 + 3 ^ 40 * 7611683 * 2
def baseEnd_7611683 : Nat := 3908451968656847988957013

theorem tailTrace_7611683 : CollatzResearch.WordTrace tailWord_7611683 prefixEnd_7611683 3908451968656847988957013 := by
  unfold tailWord_7611683
  simp only [CollatzResearch.WordTrace]
  refine ⟨277620886483179937805455703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185080590988786625203637135 277620886483179937805455703)
  ·
    refine ⟨416431329724769906708183555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277620886483179937805455703 416431329724769906708183555)
    ·
      refine ⟨624646994587154860062275333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416431329724769906708183555 624646994587154860062275333)
      ·
        refine ⟨117121311485091536261676625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 624646994587154860062275333 117121311485091536261676625)
        ·
          refine ⟨87840983613818652196257469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117121311485091536261676625 87840983613818652196257469)
          ·
            refine ⟨32940368855181994573596551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87840983613818652196257469 32940368855181994573596551)
            ·
              refine ⟨49410553282772991860394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32940368855181994573596551 49410553282772991860394827)
              ·
                refine ⟨74115829924159487790592241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49410553282772991860394827 74115829924159487790592241)
                ·
                  refine ⟨55586872443119615842944181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74115829924159487790592241 55586872443119615842944181)
                  ·
                    refine ⟨5211269291542463985276017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55586872443119615842944181 5211269291542463985276017)
                    ·
                      refine ⟨3908451968656847988957013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211269291542463985276017 3908451968656847988957013)
                      ·
                        rfl

theorem cell23_7611683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_7611683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611683 prefixEnd_7611683 := by exact prefixLift 7611683
  have htrace : WordTrace (prefixWord ++ tailWord_7611683) baseStart_7611683 baseEnd_7611683 := by
    simpa [prefixWord, tailWord_7611683, baseEnd_7611683] using wordTrace_append hprefix tailTrace_7611683
  have hstable : (prefixWord ++ tailWord_7611683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611683).length < 2 ^ (prefixWord ++ tailWord_7611683).sum := by decide
  have hdescent : baseEnd_7611683 < baseStart_7611683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611690 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7611690 : Nat := 118140960795 + 7611690 * 2 ^ 59
def prefixEnd_7611690 : Nat := 4983230072969 + 3 ^ 40 * 7611690 * 2
def baseEnd_7611690 : Nat := 3908455563021429461569481

theorem tailTrace_7611690 : CollatzResearch.WordTrace tailWord_7611690 prefixEnd_7611690 3908455563021429461569481 := by
  unfold tailWord_7611690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69405285448538644500240131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185080761196103052000640349 69405285448538644500240131)
  ·
    refine ⟨104107928172807966750360197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69405285448538644500240131 104107928172807966750360197)
    ·
      refine ⟨19520236532401493765692537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104107928172807966750360197 19520236532401493765692537)
      ·
        refine ⟨14640177399301120324269403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19520236532401493765692537 14640177399301120324269403)
        ·
          refine ⟨21960266098951680486404105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14640177399301120324269403 21960266098951680486404105)
          ·
            refine ⟨16470199574213760364803079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21960266098951680486404105 16470199574213760364803079)
            ·
              refine ⟨24705299361320640547204619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16470199574213760364803079 24705299361320640547204619)
              ·
                refine ⟨37057949041980960820806929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24705299361320640547204619 37057949041980960820806929)
                ·
                  refine ⟨27793461781485720615605197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37057949041980960820806929 27793461781485720615605197)
                  ·
                    refine ⟨10422548168057145230851949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27793461781485720615605197 10422548168057145230851949)
                    ·
                      refine ⟨3908455563021429461569481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10422548168057145230851949 3908455563021429461569481)
                      ·
                        rfl

theorem cell23_7611690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7611690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611690 prefixEnd_7611690 := by exact prefixLift 7611690
  have htrace : WordTrace (prefixWord ++ tailWord_7611690) baseStart_7611690 baseEnd_7611690 := by
    simpa [prefixWord, tailWord_7611690, baseEnd_7611690] using wordTrace_append hprefix tailTrace_7611690
  have hstable : (prefixWord ++ tailWord_7611690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611690).length < 2 ^ (prefixWord ++ tailWord_7611690).sum := by decide
  have hdescent : baseEnd_7611690 < baseStart_7611690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611696 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_7611696 : Nat := 118140960795 + 7611696 * 2 ^ 59
def prefixEnd_7611696 : Nat := 4983230072969 + 3 ^ 40 * 7611696 * 2
def baseEnd_7611696 : Nat := 3908458643905356438094453

theorem tailTrace_7611696 : CollatzResearch.WordTrace tailWord_7611696 prefixEnd_7611696 3908458643905356438094453 := by
  unfold tailWord_7611696
  simp only [CollatzResearch.WordTrace]
  refine ⟨138810680316066420512839471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185080907088088560683785961 138810680316066420512839471)
  ·
    refine ⟨208216020474099630769259207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138810680316066420512839471 208216020474099630769259207)
    ·
      refine ⟨312324030711149446153888811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208216020474099630769259207 312324030711149446153888811)
      ·
        refine ⟨468486046066724169230833217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312324030711149446153888811 468486046066724169230833217)
        ·
          refine ⟨351364534550043126923124913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468486046066724169230833217 351364534550043126923124913)
          ·
            refine ⟨263523400912532345192343685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351364534550043126923124913 263523400912532345192343685)
            ·
              refine ⟨49410637671099814723564441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263523400912532345192343685 49410637671099814723564441)
              ·
                refine ⟨37057978253324861042673331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49410637671099814723564441 37057978253324861042673331)
                ·
                  refine ⟨55586967379987291564009997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37057978253324861042673331 55586967379987291564009997)
                  ·
                    refine ⟨20845112767495234336503749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55586967379987291564009997 20845112767495234336503749)
                    ·
                      refine ⟨3908458643905356438094453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20845112767495234336503749 3908458643905356438094453)
                      ·
                        rfl

theorem cell23_7611696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_7611696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611696 prefixEnd_7611696 := by exact prefixLift 7611696
  have htrace : WordTrace (prefixWord ++ tailWord_7611696) baseStart_7611696 baseEnd_7611696 := by
    simpa [prefixWord, tailWord_7611696, baseEnd_7611696] using wordTrace_append hprefix tailTrace_7611696
  have hstable : (prefixWord ++ tailWord_7611696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611696).length < 2 ^ (prefixWord ++ tailWord_7611696).sum := by decide
  have hdescent : baseEnd_7611696 < baseStart_7611696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611700 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7611700 : Nat := 118140960795 + 7611700 * 2 ^ 59
def prefixEnd_7611700 : Nat := 4983230072969 + 3 ^ 40 * 7611700 * 2
def baseEnd_7611700 : Nat := 3908460697827974422444435

theorem tailTrace_7611700 : CollatzResearch.WordTrace tailWord_7611700 prefixEnd_7611700 3908460697827974422444435 := by
  unfold tailWord_7611700
  simp only [CollatzResearch.WordTrace]
  refine ⟨138810753262059174854412277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185081004349412233139216369 138810753262059174854412277)
  ·
    refine ⟨13013508118318047642601151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138810753262059174854412277 13013508118318047642601151)
    ·
      refine ⟨19520262177477071463901727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13013508118318047642601151 19520262177477071463901727)
      ·
        refine ⟨29280393266215607195852591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19520262177477071463901727 29280393266215607195852591)
        ·
          refine ⟨43920589899323410793778887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29280393266215607195852591 43920589899323410793778887)
          ·
            refine ⟨65880884848985116190668331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43920589899323410793778887 65880884848985116190668331)
            ·
              refine ⟨98821327273477674286002497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65880884848985116190668331 98821327273477674286002497)
              ·
                refine ⟨74115995455108255714501873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98821327273477674286002497 74115995455108255714501873)
                ·
                  refine ⟨55586996591331191785876405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74115995455108255714501873 55586996591331191785876405)
                  ·
                    refine ⟨5211280930437299229925913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55586996591331191785876405 5211280930437299229925913)
                    ·
                      refine ⟨3908460697827974422444435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5211280930437299229925913 3908460697827974422444435)
                      ·
                        rfl

theorem cell23_7611700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7611700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611700 prefixEnd_7611700 := by exact prefixLift 7611700
  have htrace : WordTrace (prefixWord ++ tailWord_7611700) baseStart_7611700 baseEnd_7611700 := by
    simpa [prefixWord, tailWord_7611700, baseEnd_7611700] using wordTrace_append hprefix tailTrace_7611700
  have hstable : (prefixWord ++ tailWord_7611700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611700).length < 2 ^ (prefixWord ++ tailWord_7611700).sum := by decide
  have hdescent : baseEnd_7611700 < baseStart_7611700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611726 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7611726 : Nat := 118140960795 + 7611726 * 2 ^ 59
def prefixEnd_7611726 : Nat := 4983230072969 + 3 ^ 40 * 7611726 * 2
def baseEnd_7611726 : Nat := 3908474048324991320719315

theorem tailTrace_7611726 : CollatzResearch.WordTrace tailWord_7611726 prefixEnd_7611726 3908474048324991320719315 := by
  unfold tailWord_7611726
  simp only [CollatzResearch.WordTrace]
  refine ⟨34702806852753019518658879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185081636548016104099514021 34702806852753019518658879)
  ·
    refine ⟨52054210279129529277988319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34702806852753019518658879 52054210279129529277988319)
    ·
      refine ⟨78081315418694293916982479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52054210279129529277988319 78081315418694293916982479)
      ·
        refine ⟨117121973128041440875473719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78081315418694293916982479 117121973128041440875473719)
        ·
          refine ⟨175682959692062161313210579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117121973128041440875473719 175682959692062161313210579)
          ·
            refine ⟨263524439538093241969815869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175682959692062161313210579 263524439538093241969815869)
            ·
              refine ⟨98821664826784965738680951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263524439538093241969815869 98821664826784965738680951)
              ·
                refine ⟨148232497240177448608021427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98821664826784965738680951 148232497240177448608021427)
                ·
                  refine ⟨222348745860266172912032141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148232497240177448608021427 222348745860266172912032141)
                  ·
                    refine ⟨83380779697599814842012053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222348745860266172912032141 83380779697599814842012053)
                    ·
                      refine ⟨3908474048324991320719315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83380779697599814842012053 3908474048324991320719315)
                      ·
                        rfl

theorem cell23_7611726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7611726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611726 prefixEnd_7611726 := by exact prefixLift 7611726
  have htrace : WordTrace (prefixWord ++ tailWord_7611726) baseStart_7611726 baseEnd_7611726 := by
    simpa [prefixWord, tailWord_7611726, baseEnd_7611726] using wordTrace_append hprefix tailTrace_7611726
  have hstable : (prefixWord ++ tailWord_7611726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611726).length < 2 ^ (prefixWord ++ tailWord_7611726).sum := by decide
  have hdescent : baseEnd_7611726 < baseStart_7611726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7611736 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 8]
def baseStart_7611736 : Nat := 118140960795 + 7611736 * 2 ^ 59
def prefixEnd_7611736 : Nat := 4983230072969 + 3 ^ 40 * 7611736 * 2
def baseEnd_7611736 : Nat := 434275464792392920177141

theorem tailTrace_7611736 : CollatzResearch.WordTrace tailWord_7611736 prefixEnd_7611736 434275464792392920177141 := by
  unfold tailWord_7611736
  simp only [CollatzResearch.WordTrace]
  refine ⟨138811409775993963928567531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185081879701325285238090041 138811409775993963928567531)
  ·
    refine ⟨208217114663990945892851297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138811409775993963928567531 208217114663990945892851297)
    ·
      refine ⟨156162835997993209419638473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208217114663990945892851297 156162835997993209419638473)
      ·
        refine ⟨117122126998494907064728855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156162835997993209419638473 117122126998494907064728855)
        ·
          refine ⟨175683190497742360597093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117122126998494907064728855 175683190497742360597093283)
          ·
            refine ⟨263524785746613540895639925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175683190497742360597093283 263524785746613540895639925)
            ·
              refine ⟨24705448663745019458966243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263524785746613540895639925 24705448663745019458966243)
              ·
                refine ⟨37058172995617529188449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24705448663745019458966243 37058172995617529188449365)
                ·
                  refine ⟨434275464792392920177141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37058172995617529188449365 434275464792392920177141)
                  ·
                    rfl

theorem cell23_7611736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_7611736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7611736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7611736 prefixEnd_7611736 := by exact prefixLift 7611736
  have htrace : WordTrace (prefixWord ++ tailWord_7611736) baseStart_7611736 baseEnd_7611736 := by
    simpa [prefixWord, tailWord_7611736, baseEnd_7611736] using wordTrace_append hprefix tailTrace_7611736
  have hstable : (prefixWord ++ tailWord_7611736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7611736).length < 2 ^ (prefixWord ++ tailWord_7611736).sum := by decide
  have hdescent : baseEnd_7611736 < baseStart_7611736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7611736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
