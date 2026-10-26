import V185TrunkScan23Chunk0704

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4168371 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 3]
def baseStart_4168371 : Nat := 118140960795 + 4168371 * 2 ^ 59
def prefixEnd_4168371 : Nat := 4983230072969 + 3 ^ 40 * 4168371 * 2
def baseEnd_4168371 : Nat := 2140377869262615962992517

theorem tailTrace_4168371 : CollatzResearch.WordTrace tailWord_4168371 prefixEnd_4168371 2140377869262615962992517 := by
  unfold tailWord_4168371
  simp only [CollatzResearch.WordTrace]
  refine ⟨152032980381711242934568967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101355320254474161956379311 152032980381711242934568967)
  ·
    refine ⟨228049470572566864401853451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152032980381711242934568967 228049470572566864401853451)
    ·
      refine ⟨342074205858850296602780177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228049470572566864401853451 342074205858850296602780177)
      ·
        refine ⟨256555654394137722452085133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342074205858850296602780177 256555654394137722452085133)
        ·
          refine ⟨96208370397801645919531925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256555654394137722452085133 96208370397801645919531925)
          ·
            refine ⟨4509767362396952152478059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96208370397801645919531925 4509767362396952152478059)
            ·
              refine ⟨6764651043595428228717089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509767362396952152478059 6764651043595428228717089)
              ·
                refine ⟨5073488282696571171537817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6764651043595428228717089 5073488282696571171537817)
                ·
                  refine ⟨3805116212022428378653363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073488282696571171537817 3805116212022428378653363)
                  ·
                    refine ⟨5707674318033642567980045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805116212022428378653363 5707674318033642567980045)
                    ·
                      refine ⟨2140377869262615962992517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707674318033642567980045 2140377869262615962992517)
                      ·
                        rfl

theorem cell23_4168371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 3].length) (baseStart_4168371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168371 prefixEnd_4168371 := by exact prefixLift 4168371
  have htrace : WordTrace (prefixWord ++ tailWord_4168371) baseStart_4168371 baseEnd_4168371 := by
    simpa [prefixWord, tailWord_4168371, baseEnd_4168371] using wordTrace_append hprefix tailTrace_4168371
  have hstable : (prefixWord ++ tailWord_4168371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168371).length < 2 ^ (prefixWord ++ tailWord_4168371).sum := by decide
  have hdescent : baseEnd_4168371 < baseStart_4168371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168388 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4168388 : Nat := 118140960795 + 4168388 * 2 ^ 59
def prefixEnd_4168388 : Nat := 4983230072969 + 3 ^ 40 * 4168388 * 2
def baseEnd_4168388 : Nat := 2140386598433742396479939

theorem tailTrace_4168388 : CollatzResearch.WordTrace tailWord_4168388 prefixEnd_4168388 2140386598433742396479939 := by
  unfold tailWord_4168388
  simp only [CollatzResearch.WordTrace]
  refine ⟨76016800211324827418968909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101355733615099769891958545 76016800211324827418968909)
  ·
    refine ⟨28506300079246810282113341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76016800211324827418968909 28506300079246810282113341)
    ·
      refine ⟨10689862529717553855792503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28506300079246810282113341 10689862529717553855792503)
      ·
        refine ⟨16034793794576330783688755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10689862529717553855792503 16034793794576330783688755)
        ·
          refine ⟨24052190691864496175533133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034793794576330783688755 24052190691864496175533133)
          ·
            refine ⟨9019571509449186065824925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24052190691864496175533133 9019571509449186065824925)
            ·
              refine ⟨3382339316043444774684347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9019571509449186065824925 3382339316043444774684347)
              ·
                refine ⟨5073508974065167162026521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382339316043444774684347 5073508974065167162026521)
                ·
                  refine ⟨3805131730548875371519891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073508974065167162026521 3805131730548875371519891)
                  ·
                    refine ⟨5707697595823313057279837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805131730548875371519891 5707697595823313057279837)
                    ·
                      refine ⟨2140386598433742396479939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707697595823313057279837 2140386598433742396479939)
                      ·
                        rfl

theorem cell23_4168388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4168388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168388 prefixEnd_4168388 := by exact prefixLift 4168388
  have htrace : WordTrace (prefixWord ++ tailWord_4168388) baseStart_4168388 baseEnd_4168388 := by
    simpa [prefixWord, tailWord_4168388, baseEnd_4168388] using wordTrace_append hprefix tailTrace_4168388
  have hstable : (prefixWord ++ tailWord_4168388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168388).length < 2 ^ (prefixWord ++ tailWord_4168388).sum := by decide
  have hdescent : baseEnd_4168388 < baseStart_4168388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168434 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_4168434 : Nat := 118140960795 + 4168434 * 2 ^ 59
def prefixEnd_4168434 : Nat := 4983230072969 + 3 ^ 40 * 4168434 * 2
def baseEnd_4168434 : Nat := 237823357615983246278303

theorem tailTrace_4168434 : CollatzResearch.WordTrace tailWord_4168434 prefixEnd_4168434 237823357615983246278303 := by
  unfold tailWord_4168434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38008819545120751173528089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101356852120322003129408237 38008819545120751173528089)
  ·
    refine ⟨28506614658840563380146067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38008819545120751173528089 28506614658840563380146067)
    ·
      refine ⟨42759921988260845070219101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28506614658840563380146067 42759921988260845070219101)
      ·
        refine ⟨16034970745597816901332163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42759921988260845070219101 16034970745597816901332163)
        ·
          refine ⟨24052456118396725351998245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16034970745597816901332163 24052456118396725351998245)
          ·
            refine ⟨4509835522199386003499671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24052456118396725351998245 4509835522199386003499671)
            ·
              refine ⟨6764753283299079005249507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509835522199386003499671 6764753283299079005249507)
              ·
                refine ⟨10147129924948618507874261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764753283299079005249507 10147129924948618507874261)
                ·
                  refine ⟨237823357615983246278303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10147129924948618507874261 237823357615983246278303)
                  ·
                    rfl

theorem cell23_4168434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_4168434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168434 prefixEnd_4168434 := by exact prefixLift 4168434
  have htrace : WordTrace (prefixWord ++ tailWord_4168434) baseStart_4168434 baseEnd_4168434 := by
    simpa [prefixWord, tailWord_4168434, baseEnd_4168434] using wordTrace_append hprefix tailTrace_4168434
  have hstable : (prefixWord ++ tailWord_4168434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168434).length < 2 ^ (prefixWord ++ tailWord_4168434).sum := by decide
  have hdescent : baseEnd_4168434 < baseStart_4168434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168501 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_4168501 : Nat := 118140960795 + 4168501 * 2 ^ 59
def prefixEnd_4168501 : Nat := 4983230072969 + 3 ^ 40 * 4168501 * 2
def baseEnd_4168501 : Nat := 2140444621747700454366919

theorem tailTrace_4168501 : CollatzResearch.WordTrace tailWord_4168501 prefixEnd_4168501 2140444621747700454366919 := by
  unfold tailWord_4168501
  simp only [CollatzResearch.WordTrace]
  refine ⟨152037721871240275136801357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101358481247493516757867571 152037721871240275136801357)
  ·
    refine ⟨57014145701715103176300509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152037721871240275136801357 57014145701715103176300509)
    ·
      refine ⟨21380304638143163691112691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57014145701715103176300509 21380304638143163691112691)
      ·
        refine ⟨32070456957214745536669037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21380304638143163691112691 32070456957214745536669037)
        ·
          refine ⟨12026421358955529576250889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32070456957214745536669037 12026421358955529576250889)
          ·
            refine ⟨9019816019216647182188167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026421358955529576250889 9019816019216647182188167)
            ·
              refine ⟨13529724028824970773282251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019816019216647182188167 13529724028824970773282251)
              ·
                refine ⟨20294586043237456159923377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529724028824970773282251 20294586043237456159923377)
                ·
                  refine ⟨15220939532428092119942533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20294586043237456159923377 15220939532428092119942533)
                  ·
                    refine ⟨2853926162330267272489225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15220939532428092119942533 2853926162330267272489225)
                    ·
                      refine ⟨2140444621747700454366919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853926162330267272489225 2140444621747700454366919)
                      ·
                        rfl

theorem cell23_4168501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_4168501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168501 prefixEnd_4168501 := by exact prefixLift 4168501
  have htrace : WordTrace (prefixWord ++ tailWord_4168501) baseStart_4168501 baseEnd_4168501 := by
    simpa [prefixWord, tailWord_4168501, baseEnd_4168501] using wordTrace_append hprefix tailTrace_4168501
  have hstable : (prefixWord ++ tailWord_4168501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168501).length < 2 ^ (prefixWord ++ tailWord_4168501).sum := by decide
  have hdescent : baseEnd_4168501 < baseStart_4168501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168517 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_4168517 : Nat := 118140960795 + 4168517 * 2 ^ 59
def prefixEnd_4168517 : Nat := 4983230072969 + 3 ^ 40 * 4168517 * 2
def baseEnd_4168517 : Nat := 2140452837438172391766845

theorem tailTrace_4168517 : CollatzResearch.WordTrace tailWord_4168517 prefixEnd_4168517 2140452837438172391766845 := by
  unfold tailWord_4168517
  simp only [CollatzResearch.WordTrace]
  refine ⟨152038305439182309869383805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101358870292788206579589203 152038305439182309869383805)
  ·
    refine ⟨57014364539693366201018927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152038305439182309869383805 57014364539693366201018927)
    ·
      refine ⟨85521546809540049301528391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57014364539693366201018927 85521546809540049301528391)
      ·
        refine ⟨128282320214310073952292587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85521546809540049301528391 128282320214310073952292587)
        ·
          refine ⟨192423480321465110928438881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128282320214310073952292587 192423480321465110928438881)
          ·
            refine ⟨144317610241098833196329161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192423480321465110928438881 144317610241098833196329161)
            ·
              refine ⟨108238207680824124897246871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144317610241098833196329161 108238207680824124897246871)
              ·
                refine ⟨162357311521236187345870307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108238207680824124897246871 162357311521236187345870307)
                ·
                  refine ⟨243535967281854281018805461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162357311521236187345870307 243535967281854281018805461)
                  ·
                    refine ⟨5707874233168459711378253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 243535967281854281018805461 5707874233168459711378253)
                    ·
                      refine ⟨2140452837438172391766845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707874233168459711378253 2140452837438172391766845)
                      ·
                        rfl

theorem cell23_4168517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_4168517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168517 prefixEnd_4168517 := by exact prefixLift 4168517
  have htrace : WordTrace (prefixWord ++ tailWord_4168517) baseStart_4168517 baseEnd_4168517 := by
    simpa [prefixWord, tailWord_4168517, baseEnd_4168517] using wordTrace_append hprefix tailTrace_4168517
  have hstable : (prefixWord ++ tailWord_4168517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168517).length < 2 ^ (prefixWord ++ tailWord_4168517).sum := by decide
  have hdescent : baseEnd_4168517 < baseStart_4168517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168518 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4168518 : Nat := 118140960795 + 4168518 * 2 ^ 59
def prefixEnd_4168518 : Nat := 4983230072969 + 3 ^ 40 * 4168518 * 2
def baseEnd_4168518 : Nat := 2140453350918826887854341

theorem tailTrace_4168518 : CollatzResearch.WordTrace tailWord_4168518 prefixEnd_4168518 2140453350918826887854341 := by
  unfold tailWord_4168518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751198184755583970005319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101358894608119124693446805 4751198184755583970005319)
  ·
    refine ⟨7126797277133375955007979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751198184755583970005319 7126797277133375955007979)
    ·
      refine ⟨10690195915700063932511969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126797277133375955007979 10690195915700063932511969)
      ·
        refine ⟨8017646936775047949383977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10690195915700063932511969 8017646936775047949383977)
        ·
          refine ⟨6013235202581285962037983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8017646936775047949383977 6013235202581285962037983)
          ·
            refine ⟨9019852803871928943056975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013235202581285962037983 9019852803871928943056975)
            ·
              refine ⟨13529779205807893414585463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019852803871928943056975 13529779205807893414585463)
              ·
                refine ⟨20294668808711840121878195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13529779205807893414585463 20294668808711840121878195)
                ·
                  refine ⟨30442003213067760182817293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20294668808711840121878195 30442003213067760182817293)
                  ·
                    refine ⟨11415751204900410068556485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30442003213067760182817293 11415751204900410068556485)
                    ·
                      refine ⟨2140453350918826887854341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11415751204900410068556485 2140453350918826887854341)
                      ·
                        rfl

theorem cell23_4168518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4168518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168518 prefixEnd_4168518 := by exact prefixLift 4168518
  have htrace : WordTrace (prefixWord ++ tailWord_4168518) baseStart_4168518 baseEnd_4168518 := by
    simpa [prefixWord, tailWord_4168518, baseEnd_4168518] using wordTrace_append hprefix tailTrace_4168518
  have hstable : (prefixWord ++ tailWord_4168518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168518).length < 2 ^ (prefixWord ++ tailWord_4168518).sum := by decide
  have hdescent : baseEnd_4168518 < baseStart_4168518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168521 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_4168521 : Nat := 118140960795 + 4168521 * 2 ^ 59
def prefixEnd_4168521 : Nat := 4983230072969 + 3 ^ 40 * 4168521 * 2
def baseEnd_4168521 : Nat := 2140454891360790376116827

theorem tailTrace_4168521 : CollatzResearch.WordTrace tailWord_4168521 prefixEnd_4168521 2140454891360790376116827 := by
  unfold tailWord_4168521
  simp only [CollatzResearch.WordTrace]
  refine ⟨152038451331167818552529417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101358967554111879035019611 152038451331167818552529417)
  ·
    refine ⟨114028838498375863914397063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152038451331167818552529417 114028838498375863914397063)
    ·
      refine ⟨171043257747563795871595595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114028838498375863914397063 171043257747563795871595595)
      ·
        refine ⟨256564886621345693807393393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171043257747563795871595595 256564886621345693807393393)
        ·
          refine ⟨192423664966009270355545045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256564886621345693807393393 192423664966009270355545045)
          ·
            refine ⟨4509929647640842273958087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 192423664966009270355545045 4509929647640842273958087)
            ·
              refine ⟨6764894471461263410937131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509929647640842273958087 6764894471461263410937131)
              ·
                refine ⟨10147341707191895116405697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764894471461263410937131 10147341707191895116405697)
                ·
                  refine ⟨7610506280393921337304273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10147341707191895116405697 7610506280393921337304273)
                  ·
                    refine ⟨5707879710295441002978205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7610506280393921337304273 5707879710295441002978205)
                    ·
                      refine ⟨2140454891360790376116827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707879710295441002978205 2140454891360790376116827)
                      ·
                        rfl

theorem cell23_4168521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_4168521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168521 prefixEnd_4168521 := by exact prefixLift 4168521
  have htrace : WordTrace (prefixWord ++ tailWord_4168521) baseStart_4168521 baseEnd_4168521 := by
    simpa [prefixWord, tailWord_4168521, baseEnd_4168521] using wordTrace_append hprefix tailTrace_4168521
  have hstable : (prefixWord ++ tailWord_4168521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168521).length < 2 ^ (prefixWord ++ tailWord_4168521).sum := by decide
  have hdescent : baseEnd_4168521 < baseStart_4168521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168551 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_4168551 : Nat := 118140960795 + 4168551 * 2 ^ 59
def prefixEnd_4168551 : Nat := 4983230072969 + 3 ^ 40 * 4168551 * 2
def baseEnd_4168551 : Nat := 2140470295780425258741689

theorem tailTrace_4168551 : CollatzResearch.WordTrace tailWord_4168551 prefixEnd_4168551 2140470295780425258741689 := by
  unfold tailWord_4168551
  simp only [CollatzResearch.WordTrace]
  refine ⟨152039545521059133676121507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101359697014039422450747671 152039545521059133676121507)
  ·
    refine ⟨228059318281588700514182261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152039545521059133676121507 228059318281588700514182261)
    ·
      refine ⟨21380561088898940673204587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228059318281588700514182261 21380561088898940673204587)
      ·
        refine ⟨32070841633348411009806881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21380561088898940673204587 32070841633348411009806881)
        ·
          refine ⟨24053131225011308257355161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32070841633348411009806881 24053131225011308257355161)
          ·
            refine ⟨18039848418758481193016371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24053131225011308257355161 18039848418758481193016371)
            ·
              refine ⟨27059772628137721789524557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18039848418758481193016371 27059772628137721789524557)
              ·
                refine ⟨10147414735551645671071709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27059772628137721789524557 10147414735551645671071709)
                ·
                  refine ⟨3805280525831867126651891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10147414735551645671071709 3805280525831867126651891)
                  ·
                    refine ⟨5707920788747800689977837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805280525831867126651891 5707920788747800689977837)
                    ·
                      refine ⟨2140470295780425258741689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707920788747800689977837 2140470295780425258741689)
                      ·
                        rfl

theorem cell23_4168551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_4168551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168551 prefixEnd_4168551 := by exact prefixLift 4168551
  have htrace : WordTrace (prefixWord ++ tailWord_4168551) baseStart_4168551 baseEnd_4168551 := by
    simpa [prefixWord, tailWord_4168551, baseEnd_4168551] using wordTrace_append hprefix tailTrace_4168551
  have hstable : (prefixWord ++ tailWord_4168551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168551).length < 2 ^ (prefixWord ++ tailWord_4168551).sum := by decide
  have hdescent : baseEnd_4168551 < baseStart_4168551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168558 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_4168558 : Nat := 118140960795 + 4168558 * 2 ^ 59
def prefixEnd_4168558 : Nat := 4983230072969 + 3 ^ 40 * 4168558 * 2
def baseEnd_4168558 : Nat := 237830432238334081261573

theorem tailTrace_4168558 : CollatzResearch.WordTrace tailWord_4168558 prefixEnd_4168558 237830432238334081261573 := by
  unfold tailWord_4168558
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004975104004221733953291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101359867221355849247750885 19004975104004221733953291)
  ·
    refine ⟨28507462656006332600929937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19004975104004221733953291 28507462656006332600929937)
    ·
      refine ⟨21380596992004749450697453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28507462656006332600929937 21380596992004749450697453)
      ·
        refine ⟨8017723872001781044011545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21380596992004749450697453 8017723872001781044011545)
        ·
          refine ⟨6013292904001335783008659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8017723872001781044011545 6013292904001335783008659)
          ·
            refine ⟨9019939356002003674512989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013292904001335783008659 9019939356002003674512989)
            ·
              refine ⟨3382477258500751377942371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9019939356002003674512989 3382477258500751377942371)
              ·
                refine ⟨5073715887751127066913557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382477258500751377942371 5073715887751127066913557)
                ·
                  refine ⟨237830432238334081261573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5073715887751127066913557 237830432238334081261573)
                  ·
                    rfl

theorem cell23_4168558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_4168558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168558 prefixEnd_4168558 := by exact prefixLift 4168558
  have htrace : WordTrace (prefixWord ++ tailWord_4168558) baseStart_4168558 baseEnd_4168558 := by
    simpa [prefixWord, tailWord_4168558, baseEnd_4168558] using wordTrace_append hprefix tailTrace_4168558
  have hstable : (prefixWord ++ tailWord_4168558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168558).length < 2 ^ (prefixWord ++ tailWord_4168558).sum := by decide
  have hdescent : baseEnd_4168558 < baseStart_4168558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168585 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 1, 1, 3]
def baseStart_4168585 : Nat := 118140960795 + 4168585 * 2 ^ 59
def prefixEnd_4168585 : Nat := 4983230072969 + 3 ^ 40 * 4168585 * 2
def baseEnd_4168585 : Nat := 2140487754122678125716533

theorem tailTrace_4168585 : CollatzResearch.WordTrace tailWord_4168585 prefixEnd_4168585 2140487754122678125716533 := by
  unfold tailWord_4168585
  simp only [CollatzResearch.WordTrace]
  refine ⟨152040785602935957482859209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101360523735290638321906139 152040785602935957482859209)
  ·
    refine ⟨114030589202201968112144407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152040785602935957482859209 114030589202201968112144407)
    ·
      refine ⟨171045883803302952168216611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114030589202201968112144407 171045883803302952168216611)
      ·
        refine ⟨256568825704954428252324917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171045883803302952168216611 256568825704954428252324917)
        ·
          refine ⟨24053327409839477648655461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 256568825704954428252324917 24053327409839477648655461)
          ·
            refine ⟨4509998889344902059122899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24053327409839477648655461 4509998889344902059122899)
            ·
              refine ⟨6764998334017353088684349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509998889344902059122899 6764998334017353088684349)
              ·
                refine ⟨2536874375256507408256631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6764998334017353088684349 2536874375256507408256631)
                ·
                  refine ⟨3805311562884761112384947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536874375256507408256631 3805311562884761112384947)
                  ·
                    refine ⟨5707967344327141668577421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805311562884761112384947 5707967344327141668577421)
                    ·
                      refine ⟨2140487754122678125716533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707967344327141668577421 2140487754122678125716533)
                      ·
                        rfl

theorem cell23_4168585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 1, 3].length) (baseStart_4168585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168585 prefixEnd_4168585 := by exact prefixLift 4168585
  have htrace : WordTrace (prefixWord ++ tailWord_4168585) baseStart_4168585 baseEnd_4168585 := by
    simpa [prefixWord, tailWord_4168585, baseEnd_4168585] using wordTrace_append hprefix tailTrace_4168585
  have hstable : (prefixWord ++ tailWord_4168585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168585).length < 2 ^ (prefixWord ++ tailWord_4168585).sum := by decide
  have hdescent : baseEnd_4168585 < baseStart_4168585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168597 : List Nat := [1, 3, 2, 1, 1, 4, 11]
def baseStart_4168597 : Nat := 118140960795 + 4168597 * 2 ^ 59
def prefixEnd_4168597 : Nat := 4983230072969 + 3 ^ 40 * 4168597 * 2
def baseEnd_4168597 : Nat := 26425850813463358997117

theorem tailTrace_4168597 : CollatzResearch.WordTrace tailWord_4168597 prefixEnd_4168597 26425850813463358997117 := by
  unfold tailWord_4168597
  simp only [CollatzResearch.WordTrace]
  refine ⟨152041223278892483532296045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101360815519261655688197363 152041223278892483532296045)
  ·
    refine ⟨57015458729584681324611017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152041223278892483532296045 57015458729584681324611017)
    ·
      refine ⟨42761594047188510993458263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57015458729584681324611017 42761594047188510993458263)
      ·
        refine ⟨64142391070782766490187395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42761594047188510993458263 64142391070782766490187395)
        ·
          refine ⟨96213586606174149735281093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64142391070782766490187395 96213586606174149735281093)
          ·
            refine ⟨18040047488657653075365205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96213586606174149735281093 18040047488657653075365205)
            ·
              refine ⟨26425850813463358997117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18040047488657653075365205 26425850813463358997117)
              ·
                rfl

theorem cell23_4168597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 11].length) (baseStart_4168597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168597 prefixEnd_4168597 := by exact prefixLift 4168597
  have htrace : WordTrace (prefixWord ++ tailWord_4168597) baseStart_4168597 baseEnd_4168597 := by
    simpa [prefixWord, tailWord_4168597, baseEnd_4168597] using wordTrace_append hprefix tailTrace_4168597
  have hstable : (prefixWord ++ tailWord_4168597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168597).length < 2 ^ (prefixWord ++ tailWord_4168597).sum := by decide
  have hdescent : baseEnd_4168597 < baseStart_4168597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168602 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4168602 : Nat := 118140960795 + 4168602 * 2 ^ 59
def prefixEnd_4168602 : Nat := 4983230072969 + 3 ^ 40 * 4168602 * 2
def baseEnd_4168602 : Nat := 2140496483293804559203955

theorem tailTrace_4168602 : CollatzResearch.WordTrace tailWord_4168602 prefixEnd_4168602 2140496483293804559203955 := by
  unfold tailWord_4168602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010351410968592346557015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101360937095916246257485373 38010351410968592346557015)
  ·
    refine ⟨57015527116452888519835523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38010351410968592346557015 57015527116452888519835523)
    ·
      refine ⟨85523290674679332779753285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57015527116452888519835523 85523290674679332779753285)
      ·
        refine ⟨16035617001502374896203741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85523290674679332779753285 16035617001502374896203741)
        ·
          refine ⟨6013356375563390586076403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16035617001502374896203741 6013356375563390586076403)
          ·
            refine ⟨9020034563345085879114605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013356375563390586076403 9020034563345085879114605)
            ·
              refine ⟨3382512961254407204667977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9020034563345085879114605 3382512961254407204667977)
              ·
                refine ⟨2536884720940805403500983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382512961254407204667977 2536884720940805403500983)
                ·
                  refine ⟨3805327081411208105251475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536884720940805403500983 3805327081411208105251475)
                  ·
                    refine ⟨5707990622116812157877213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805327081411208105251475 5707990622116812157877213)
                    ·
                      refine ⟨2140496483293804559203955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707990622116812157877213 2140496483293804559203955)
                      ·
                        rfl

theorem cell23_4168602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4168602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168602 prefixEnd_4168602 := by exact prefixLift 4168602
  have htrace : WordTrace (prefixWord ++ tailWord_4168602) baseStart_4168602 baseEnd_4168602 := by
    simpa [prefixWord, tailWord_4168602, baseEnd_4168602] using wordTrace_append hprefix tailTrace_4168602
  have hstable : (prefixWord ++ tailWord_4168602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168602).length < 2 ^ (prefixWord ++ tailWord_4168602).sum := by decide
  have hdescent : baseEnd_4168602 < baseStart_4168602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168608 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2]
def baseStart_4168608 : Nat := 118140960795 + 4168608 * 2 ^ 59
def prefixEnd_4168608 : Nat := 4983230072969 + 3 ^ 40 * 4168608 * 2
def baseEnd_4168608 : Nat := 2140499564177731535728927

theorem tailTrace_4168608 : CollatzResearch.WordTrace tailWord_4168608 prefixEnd_4168608 2140499564177731535728927 := by
  unfold tailWord_4168608
  simp only [CollatzResearch.WordTrace]
  refine ⟨76020812240926316205473239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101361082987901754940630985 76020812240926316205473239)
  ·
    refine ⟨114031218361389474308209859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76020812240926316205473239 114031218361389474308209859)
    ·
      refine ⟨171046827542084211462314789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114031218361389474308209859 171046827542084211462314789)
      ·
        refine ⟨32071280164140789649184023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171046827542084211462314789 32071280164140789649184023)
        ·
          refine ⟨48106920246211184473776035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32071280164140789649184023 48106920246211184473776035)
          ·
            refine ⟨72160380369316776710664053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48106920246211184473776035 72160380369316776710664053)
            ·
              refine ⟨6765035659623447816624755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72160380369316776710664053 6765035659623447816624755)
              ·
                refine ⟨10147553489435171724937133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765035659623447816624755 10147553489435171724937133)
                ·
                  refine ⟨3805332558538189396851425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10147553489435171724937133 3805332558538189396851425)
                  ·
                    refine ⟨2853999418903642047638569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805332558538189396851425 2853999418903642047638569)
                    ·
                      refine ⟨2140499564177731535728927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853999418903642047638569 2140499564177731535728927)
                      ·
                        rfl

theorem cell23_4168608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_4168608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168608 prefixEnd_4168608 := by exact prefixLift 4168608
  have htrace : WordTrace (prefixWord ++ tailWord_4168608) baseStart_4168608 baseEnd_4168608 := by
    simpa [prefixWord, tailWord_4168608, baseEnd_4168608] using wordTrace_append hprefix tailTrace_4168608
  have hstable : (prefixWord ++ tailWord_4168608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168608).length < 2 ^ (prefixWord ++ tailWord_4168608).sum := by decide
  have hdescent : baseEnd_4168608 < baseStart_4168608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168617 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_4168617 : Nat := 118140960795 + 4168617 * 2 ^ 59
def prefixEnd_4168617 : Nat := 4983230072969 + 3 ^ 40 * 4168617 * 2
def baseEnd_4168617 : Nat := 2140504185503622000516385

theorem tailTrace_4168617 : CollatzResearch.WordTrace tailWord_4168617 prefixEnd_4168617 2140504185503622000516385 := by
  unfold tailWord_4168617
  simp only [CollatzResearch.WordTrace]
  refine ⟨152041952738820026948024105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101361301825880017965349403 152041952738820026948024105)
  ·
    refine ⟨114031464554115020211018079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152041952738820026948024105 114031464554115020211018079)
    ·
      refine ⟨171047196831172530316527119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114031464554115020211018079 171047196831172530316527119)
      ·
        refine ⟨256570795246758795474790679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171047196831172530316527119 256570795246758795474790679)
        ·
          refine ⟨384856192870138193212186019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256570795246758795474790679 384856192870138193212186019)
          ·
            refine ⟨577284289305207289818279029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384856192870138193212186019 577284289305207289818279029)
            ·
              refine ⟨54120402122363183420463659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 577284289305207289818279029 54120402122363183420463659)
              ·
                refine ⟨81180603183544775130695489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54120402122363183420463659 81180603183544775130695489)
                ·
                  refine ⟨60885452387658581348021617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81180603183544775130695489 60885452387658581348021617)
                  ·
                    refine ⟨45664089290743936011016213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60885452387658581348021617 45664089290743936011016213)
                    ·
                      refine ⟨2140504185503622000516385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45664089290743936011016213 2140504185503622000516385)
                      ·
                        rfl

theorem cell23_4168617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_4168617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168617 prefixEnd_4168617 := by exact prefixLift 4168617
  have htrace : WordTrace (prefixWord ++ tailWord_4168617) baseStart_4168617 baseEnd_4168617 := by
    simpa [prefixWord, tailWord_4168617, baseEnd_4168617] using wordTrace_append hprefix tailTrace_4168617
  have hstable : (prefixWord ++ tailWord_4168617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168617).length < 2 ^ (prefixWord ++ tailWord_4168617).sum := by decide
  have hdescent : baseEnd_4168617 < baseStart_4168617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168625 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4168625 : Nat := 118140960795 + 4168625 * 2 ^ 59
def prefixEnd_4168625 : Nat := 4983230072969 + 3 ^ 40 * 4168625 * 2
def baseEnd_4168625 : Nat := 2140508293348857969216349

theorem tailTrace_4168625 : CollatzResearch.WordTrace tailWord_4168625 prefixEnd_4168625 2140508293348857969216349 := by
  unfold tailWord_4168625
  simp only [CollatzResearch.WordTrace]
  refine ⟨152042244522791044314315329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101361496348527362876210219 152042244522791044314315329)
  ·
    refine ⟨114031683392093283235736497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152042244522791044314315329 114031683392093283235736497)
    ·
      refine ⟨85523762544069962426802373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114031683392093283235736497 85523762544069962426802373)
      ·
        refine ⟨16035705477013117955025445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85523762544069962426802373 16035705477013117955025445)
        ·
          refine ⟨3006694776939959616567271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16035705477013117955025445 3006694776939959616567271)
          ·
            refine ⟨4510042165409939424850907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006694776939959616567271 4510042165409939424850907)
            ·
              refine ⟨6765063248114909137276361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510042165409939424850907 6765063248114909137276361)
              ·
                refine ⟨5073797436086181852957271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765063248114909137276361 5073797436086181852957271)
                ·
                  refine ⟨7610696154129272779435907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073797436086181852957271 7610696154129272779435907)
                  ·
                    refine ⟨11416044231193909169153861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610696154129272779435907 11416044231193909169153861)
                    ·
                      refine ⟨2140508293348857969216349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11416044231193909169153861 2140508293348857969216349)
                      ·
                        rfl

theorem cell23_4168625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4168625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168625 prefixEnd_4168625 := by exact prefixLift 4168625
  have htrace : WordTrace (prefixWord ++ tailWord_4168625) baseStart_4168625 baseEnd_4168625 := by
    simpa [prefixWord, tailWord_4168625, baseEnd_4168625] using wordTrace_append hprefix tailTrace_4168625
  have hstable : (prefixWord ++ tailWord_4168625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168625).length < 2 ^ (prefixWord ++ tailWord_4168625).sum := by decide
  have hdescent : baseEnd_4168625 < baseStart_4168625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168627 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 7]
def baseStart_4168627 : Nat := 118140960795 + 4168627 * 2 ^ 59
def prefixEnd_4168627 : Nat := 4983230072969 + 3 ^ 40 * 4168627 * 2
def baseEnd_4168627 : Nat := 713503106770055653797113

theorem tailTrace_4168627 : CollatzResearch.WordTrace tailWord_4168627 prefixEnd_4168627 713503106770055653797113 := by
  unfold tailWord_4168627
  simp only [CollatzResearch.WordTrace]
  refine ⟨152042317468783798655888135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101361544979189199103925423 152042317468783798655888135)
  ·
    refine ⟨228063476203175697983832203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152042317468783798655888135 228063476203175697983832203)
    ·
      refine ⟨342095214304763546975748305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228063476203175697983832203 342095214304763546975748305)
      ·
        refine ⟨256571410728572660231811229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342095214304763546975748305 256571410728572660231811229)
        ·
          refine ⟨96214279023214747586929211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256571410728572660231811229 96214279023214747586929211)
          ·
            refine ⟨144321418534822121380393817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96214279023214747586929211 144321418534822121380393817)
            ·
              refine ⟨108241063901116591035295363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144321418534822121380393817 108241063901116591035295363)
              ·
                refine ⟨162361595851674886552943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108241063901116591035295363 162361595851674886552943045)
                ·
                  refine ⟨30442799222189041228676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162361595851674886552943045 30442799222189041228676821)
                  ·
                    refine ⟨713503106770055653797113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30442799222189041228676821 713503106770055653797113)
                    ·
                      rfl

theorem cell23_4168627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_4168627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168627 prefixEnd_4168627 := by exact prefixLift 4168627
  have htrace : WordTrace (prefixWord ++ tailWord_4168627) baseStart_4168627 baseEnd_4168627 := by
    simpa [prefixWord, tailWord_4168627, baseEnd_4168627] using wordTrace_append hprefix tailTrace_4168627
  have hstable : (prefixWord ++ tailWord_4168627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168627).length < 2 ^ (prefixWord ++ tailWord_4168627).sum := by decide
  have hdescent : baseEnd_4168627 < baseStart_4168627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168653 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4168653 : Nat := 118140960795 + 4168653 * 2 ^ 59
def prefixEnd_4168653 : Nat := 4983230072969 + 3 ^ 40 * 4168653 * 2
def baseEnd_4168653 : Nat := 2140522670807183859666221

theorem tailTrace_4168653 : CollatzResearch.WordTrace tailWord_4168653 prefixEnd_4168653 2140522670807183859666221 := by
  unfold tailWord_4168653
  simp only [CollatzResearch.WordTrace]
  refine ⟨152043265766689605096334613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101362177177793070064223075 152043265766689605096334613)
  ·
    refine ⟨7127028082813575238890685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152043265766689605096334613 7127028082813575238890685)
    ·
      refine ⟨2672635531055090714584007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7127028082813575238890685 2672635531055090714584007)
      ·
        refine ⟨4008953296582636071876011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672635531055090714584007 4008953296582636071876011)
        ·
          refine ⟨6013429944873954107814017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008953296582636071876011 6013429944873954107814017)
          ·
            refine ⟨4510072458655465580860513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6013429944873954107814017 4510072458655465580860513)
            ·
              refine ⟨3382554343991599185645385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510072458655465580860513 3382554343991599185645385)
              ·
                refine ⟨2536915757993699389234039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382554343991599185645385 2536915757993699389234039)
                ·
                  refine ⟨3805373636990549083851059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536915757993699389234039 3805373636990549083851059)
                  ·
                    refine ⟨5708060455485823625776589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805373636990549083851059 5708060455485823625776589)
                    ·
                      refine ⟨2140522670807183859666221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708060455485823625776589 2140522670807183859666221)
                      ·
                        rfl

theorem cell23_4168653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4168653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168653 prefixEnd_4168653 := by exact prefixLift 4168653
  have htrace : WordTrace (prefixWord ++ tailWord_4168653) baseStart_4168653 baseEnd_4168653 := by
    simpa [prefixWord, tailWord_4168653, baseEnd_4168653] using wordTrace_append hprefix tailTrace_4168653
  have hstable : (prefixWord ++ tailWord_4168653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168653).length < 2 ^ (prefixWord ++ tailWord_4168653).sum := by decide
  have hdescent : baseEnd_4168653 < baseStart_4168653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168664 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4168664 : Nat := 118140960795 + 4168664 * 2 ^ 59
def prefixEnd_4168664 : Nat := 4983230072969 + 3 ^ 40 * 4168664 * 2
def baseEnd_4168664 : Nat := 2140528319094383316628669

theorem tailTrace_4168664 : CollatzResearch.WordTrace tailWord_4168664 prefixEnd_4168664 2140528319094383316628669 := by
  unfold tailWord_4168664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76021833484824876987492523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101362444646433169316656697 76021833484824876987492523)
  ·
    refine ⟨114032750227237315481238785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76021833484824876987492523 114032750227237315481238785)
    ·
      refine ⟨85524562670427986610929089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114032750227237315481238785 85524562670427986610929089)
      ·
        refine ⟨64143422002820989958196817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85524562670427986610929089 64143422002820989958196817)
        ·
          refine ⟨48107566502115742468647613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64143422002820989958196817 48107566502115742468647613)
          ·
            refine ⟨18040337438293403425742855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48107566502115742468647613 18040337438293403425742855)
            ·
              refine ⟨27060506157440105138614283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18040337438293403425742855 27060506157440105138614283)
              ·
                refine ⟨40590759236160157707921425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27060506157440105138614283 40590759236160157707921425)
                ·
                  refine ⟨30443069427120118280941069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40590759236160157707921425 30443069427120118280941069)
                  ·
                    refine ⟨11416151035170044355352901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30443069427120118280941069 11416151035170044355352901)
                    ·
                      refine ⟨2140528319094383316628669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11416151035170044355352901 2140528319094383316628669)
                      ·
                        rfl

theorem cell23_4168664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4168664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168664 prefixEnd_4168664 := by exact prefixLift 4168664
  have htrace : WordTrace (prefixWord ++ tailWord_4168664) baseStart_4168664 baseEnd_4168664 := by
    simpa [prefixWord, tailWord_4168664, baseEnd_4168664] using wordTrace_append hprefix tailTrace_4168664
  have hstable : (prefixWord ++ tailWord_4168664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168664).length < 2 ^ (prefixWord ++ tailWord_4168664).sum := by decide
  have hdescent : baseEnd_4168664 < baseStart_4168664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_4168667 : Nat := 118140960795 + 4168667 * 2 ^ 59
def prefixEnd_4168667 : Nat := 4983230072969 + 3 ^ 40 * 4168667 * 2
def baseEnd_4168667 : Nat := 2140529859536346804891155

theorem tailTrace_4168667 : CollatzResearch.WordTrace tailWord_4168667 prefixEnd_4168667 2140529859536346804891155 := by
  unfold tailWord_4168667
  simp only [CollatzResearch.WordTrace]
  refine ⟨152043776388638885487344255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101362517592425923658229503 152043776388638885487344255)
  ·
    refine ⟨228065664582958328231016383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152043776388638885487344255 228065664582958328231016383)
    ·
      refine ⟨342098496874437492346524575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228065664582958328231016383 342098496874437492346524575)
      ·
        refine ⟨513147745311656238519786863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342098496874437492346524575 513147745311656238519786863)
        ·
          refine ⟨769721617967484357779680295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513147745311656238519786863 769721617967484357779680295)
          ·
            refine ⟨1154582426951226536669520443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769721617967484357779680295 1154582426951226536669520443)
            ·
              refine ⟨1731873640426839805004280665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154582426951226536669520443 1731873640426839805004280665)
              ·
                refine ⟨1298905230320129853753210499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731873640426839805004280665 1298905230320129853753210499)
                ·
                  refine ⟨1948357845480194780629815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298905230320129853753210499 1948357845480194780629815749)
                  ·
                    refine ⟨365317096027536521368090453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1948357845480194780629815749 365317096027536521368090453)
                    ·
                      refine ⟨2140529859536346804891155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 365317096027536521368090453 2140529859536346804891155)
                      ·
                        rfl

theorem cell23_4168667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_4168667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168667 prefixEnd_4168667 := by exact prefixLift 4168667
  have htrace : WordTrace (prefixWord ++ tailWord_4168667) baseStart_4168667 baseEnd_4168667 := by
    simpa [prefixWord, tailWord_4168667, baseEnd_4168667] using wordTrace_append hprefix tailTrace_4168667
  have hstable : (prefixWord ++ tailWord_4168667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168667).length < 2 ^ (prefixWord ++ tailWord_4168667).sum := by decide
  have hdescent : baseEnd_4168667 < baseStart_4168667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168702 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4168702 : Nat := 118140960795 + 4168702 * 2 ^ 59
def prefixEnd_4168702 : Nat := 4983230072969 + 3 ^ 40 * 4168702 * 2
def baseEnd_4168702 : Nat := 2140547831359254167953495

theorem tailTrace_4168702 : CollatzResearch.WordTrace tailWord_4168702 prefixEnd_4168702 2140547831359254167953495 := by
  unfold tailWord_4168702
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005631617939010808108545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101363368629008057643245573 19005631617939010808108545)
  ·
    refine ⟨14254223713454258106081409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19005631617939010808108545 14254223713454258106081409)
    ·
      refine ⟨10690667785090693579561057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14254223713454258106081409 10690667785090693579561057)
      ·
        refine ⟨8018000838818020184670793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10690667785090693579561057 8018000838818020184670793)
        ·
          refine ⟨6013500629113515138503095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018000838818020184670793 6013500629113515138503095)
          ·
            refine ⟨9020250943670272707754643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013500629113515138503095 9020250943670272707754643)
            ·
              refine ⟨13530376415505409061631965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020250943670272707754643 13530376415505409061631965)
              ·
                refine ⟨5073891155814528398111987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13530376415505409061631965 5073891155814528398111987)
                ·
                  refine ⟨7610836733721792597167981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073891155814528398111987 7610836733721792597167981)
                  ·
                    refine ⟨2854063775145672223937993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7610836733721792597167981 2854063775145672223937993)
                    ·
                      refine ⟨2140547831359254167953495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854063775145672223937993 2140547831359254167953495)
                      ·
                        rfl

theorem cell23_4168702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4168702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168702 prefixEnd_4168702 := by exact prefixLift 4168702
  have htrace : WordTrace (prefixWord ++ tailWord_4168702) baseStart_4168702 baseEnd_4168702 := by
    simpa [prefixWord, tailWord_4168702, baseEnd_4168702] using wordTrace_append hprefix tailTrace_4168702
  have hstable : (prefixWord ++ tailWord_4168702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168702).length < 2 ^ (prefixWord ++ tailWord_4168702).sum := by decide
  have hdescent : baseEnd_4168702 < baseStart_4168702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168715 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 2, 2, 2]
def baseStart_4168715 : Nat := 118140960795 + 4168715 * 2 ^ 59
def prefixEnd_4168715 : Nat := 4983230072969 + 3 ^ 40 * 4168715 * 2
def baseEnd_4168715 : Nat := 2140554506607762617090935

theorem tailTrace_4168715 : CollatzResearch.WordTrace tailWord_4168715 prefixEnd_4168715 2140554506607762617090935 := by
  unfold tailWord_4168715
  simp only [CollatzResearch.WordTrace]
  refine ⟨152045527092464989685091599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101363684728309993123394399 152045527092464989685091599)
  ·
    refine ⟨228068290638697484527637399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152045527092464989685091599 228068290638697484527637399)
    ·
      refine ⟨342102435958046226791456099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228068290638697484527637399 342102435958046226791456099)
      ·
        refine ⟨513153653937069340187184149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342102435958046226791456099 513153653937069340187184149)
        ·
          refine ⟨24054077528300125321274257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 513153653937069340187184149 24054077528300125321274257)
          ·
            refine ⟨18040558146225093990955693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24054077528300125321274257 18040558146225093990955693)
            ·
              refine ⟨6765209304834410246608385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18040558146225093990955693 6765209304834410246608385)
              ·
                refine ⟨5073906978625807684956289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765209304834410246608385 5073906978625807684956289)
                ·
                  refine ⟨3805430233969355763717217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5073906978625807684956289 3805430233969355763717217)
                  ·
                    refine ⟨2854072675477016822787913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805430233969355763717217 2854072675477016822787913)
                    ·
                      refine ⟨2140554506607762617090935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854072675477016822787913 2140554506607762617090935)
                      ·
                        rfl

theorem cell23_4168715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2, 2].length) (baseStart_4168715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168715 prefixEnd_4168715 := by exact prefixLift 4168715
  have htrace : WordTrace (prefixWord ++ tailWord_4168715) baseStart_4168715 baseEnd_4168715 := by
    simpa [prefixWord, tailWord_4168715, baseEnd_4168715] using wordTrace_append hprefix tailTrace_4168715
  have hstable : (prefixWord ++ tailWord_4168715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168715).length < 2 ^ (prefixWord ++ tailWord_4168715).sum := by decide
  have hdescent : baseEnd_4168715 < baseStart_4168715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168732 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4168732 : Nat := 118140960795 + 4168732 * 2 ^ 59
def prefixEnd_4168732 : Nat := 4983230072969 + 3 ^ 40 * 4168732 * 2
def baseEnd_4168732 : Nat := 2140563235778889050578357

theorem tailTrace_4168732 : CollatzResearch.WordTrace tailWord_4168732 prefixEnd_4168732 2140563235778889050578357 := by
  unfold tailWord_4168732
  simp only [CollatzResearch.WordTrace]
  refine ⟨76023073566701700794230225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101364098088935601058973633 76023073566701700794230225)
  ·
    refine ⟨57017305175026275595672669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76023073566701700794230225 57017305175026275595672669)
    ·
      refine ⟨21381489440634853348377251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57017305175026275595672669 21381489440634853348377251)
      ·
        refine ⟨32072234160952280022565877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21381489440634853348377251 32072234160952280022565877)
        ·
          refine ⟨3006771952589276252115551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32072234160952280022565877 3006771952589276252115551)
          ·
            refine ⟨4510157928883914378173327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006771952589276252115551 4510157928883914378173327)
            ·
              refine ⟨6765236893325871567259991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510157928883914378173327 6765236893325871567259991)
              ·
                refine ⟨10147855339988807350889987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765236893325871567259991 10147855339988807350889987)
                ·
                  refine ⟨15221783009983211026334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10147855339988807350889987 15221783009983211026334981)
                  ·
                    refine ⟨2854084314371852067437809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15221783009983211026334981 2854084314371852067437809)
                    ·
                      refine ⟨2140563235778889050578357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854084314371852067437809 2140563235778889050578357)
                      ·
                        rfl

theorem cell23_4168732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4168732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168732 prefixEnd_4168732 := by exact prefixLift 4168732
  have htrace : WordTrace (prefixWord ++ tailWord_4168732) baseStart_4168732 baseEnd_4168732 := by
    simpa [prefixWord, tailWord_4168732, baseEnd_4168732] using wordTrace_append hprefix tailTrace_4168732
  have hstable : (prefixWord ++ tailWord_4168732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168732).length < 2 ^ (prefixWord ++ tailWord_4168732).sum := by decide
  have hdescent : baseEnd_4168732 < baseStart_4168732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168771 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4]
def baseStart_4168771 : Nat := 118140960795 + 4168771 * 2 ^ 59
def prefixEnd_4168771 : Nat := 4983230072969 + 3 ^ 40 * 4168771 * 2
def baseEnd_4168771 : Nat := 2140583261524414397990677

theorem tailTrace_4168771 : CollatzResearch.WordTrace tailWord_4168771 prefixEnd_4168771 2140583261524414397990677 := by
  unfold tailWord_4168771
  simp only [CollatzResearch.WordTrace]
  refine ⟨152047569580262111249130167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101365046386841407499420111 152047569580262111249130167)
  ·
    refine ⟨228071354370393166873695251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152047569580262111249130167 228071354370393166873695251)
    ·
      refine ⟨342107031555589750310542877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228071354370393166873695251 342107031555589750310542877)
      ·
        refine ⟨128290136833346156366453579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342107031555589750310542877 128290136833346156366453579)
        ·
          refine ⟨192435205250019234549680369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128290136833346156366453579 192435205250019234549680369)
          ·
            refine ⟨144326403937514425912260277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192435205250019234549680369 144326403937514425912260277)
            ·
              refine ⟨13530600369141977429274401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144326403937514425912260277 13530600369141977429274401)
              ·
                refine ⟨10147950276856483071955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13530600369141977429274401 10147950276856483071955801)
                ·
                  refine ⟨7610962707642362303966851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10147950276856483071955801 7610962707642362303966851)
                  ·
                    refine ⟨11416444061463543455950277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7610962707642362303966851 11416444061463543455950277)
                    ·
                      refine ⟨2140583261524414397990677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11416444061463543455950277 2140583261524414397990677)
                      ·
                        rfl

theorem cell23_4168771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_4168771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168771 prefixEnd_4168771 := by exact prefixLift 4168771
  have htrace : WordTrace (prefixWord ++ tailWord_4168771) baseStart_4168771 baseEnd_4168771 := by
    simpa [prefixWord, tailWord_4168771, baseEnd_4168771] using wordTrace_append hprefix tailTrace_4168771
  have hstable : (prefixWord ++ tailWord_4168771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168771).length < 2 ^ (prefixWord ++ tailWord_4168771).sum := by decide
  have hdescent : baseEnd_4168771 < baseStart_4168771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168784 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_4168784 : Nat := 118140960795 + 4168784 * 2 ^ 59
def prefixEnd_4168784 : Nat := 4983230072969 + 3 ^ 40 * 4168784 * 2
def baseEnd_4168784 : Nat := 2140589936772922847128117

theorem tailTrace_4168784 : CollatzResearch.WordTrace tailWord_4168784 prefixEnd_4168784 2140589936772922847128117 := by
  unfold tailWord_4168784
  simp only [CollatzResearch.WordTrace]
  refine ⟨76024021864607507234676703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101365362486143342979568937 76024021864607507234676703)
  ·
    refine ⟨114036032796911260852015055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76024021864607507234676703 114036032796911260852015055)
    ·
      refine ⟨171054049195366891278022583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114036032796911260852015055 171054049195366891278022583)
      ·
        refine ⟨256581073793050336917033875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171054049195366891278022583 256581073793050336917033875)
        ·
          refine ⟨384871610689575505375550813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256581073793050336917033875 384871610689575505375550813)
          ·
            refine ⟨144326854008590814515831555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384871610689575505375550813 144326854008590814515831555)
            ·
              refine ⟨216490281012886221773747333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144326854008590814515831555 216490281012886221773747333)
              ·
                refine ⟨40591927689916166582577625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216490281012886221773747333 40591927689916166582577625)
                ·
                  refine ⟨30443945767437124936933219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40591927689916166582577625 30443945767437124936933219)
                  ·
                    refine ⟨45665918651155687405399829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30443945767437124936933219 45665918651155687405399829)
                    ·
                      refine ⟨2140589936772922847128117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45665918651155687405399829 2140589936772922847128117)
                      ·
                        rfl

theorem cell23_4168784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_4168784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168784 prefixEnd_4168784 := by exact prefixLift 4168784
  have htrace : WordTrace (prefixWord ++ tailWord_4168784) baseStart_4168784 baseEnd_4168784 := by
    simpa [prefixWord, tailWord_4168784, baseEnd_4168784] using wordTrace_append hprefix tailTrace_4168784
  have hstable : (prefixWord ++ tailWord_4168784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168784).length < 2 ^ (prefixWord ++ tailWord_4168784).sum := by decide
  have hdescent : baseEnd_4168784 < baseStart_4168784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168788 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_4168788 : Nat := 118140960795 + 4168788 * 2 ^ 59
def prefixEnd_4168788 : Nat := 4983230072969 + 3 ^ 40 * 4168788 * 2
def baseEnd_4168788 : Nat := 2140591990695540831478099

theorem tailTrace_4168788 : CollatzResearch.WordTrace tailWord_4168788 prefixEnd_4168788 2140591990695540831478099 := by
  unfold tailWord_4168788
  simp only [CollatzResearch.WordTrace]
  refine ⟨76024094810600261576249509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101365459747467015434999345 76024094810600261576249509)
  ·
    refine ⟨14254517776987549045546783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76024094810600261576249509 14254517776987549045546783)
    ·
      refine ⟨21381776665481323568320175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14254517776987549045546783 21381776665481323568320175)
      ·
        refine ⟨32072664998221985352480263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21381776665481323568320175 32072664998221985352480263)
        ·
          refine ⟨48108997497332978028720395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32072664998221985352480263 48108997497332978028720395)
          ·
            refine ⟨72163496245999467043080593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48108997497332978028720395 72163496245999467043080593)
            ·
              refine ⟨54122622184499600282310445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72163496245999467043080593 54122622184499600282310445)
              ·
                refine ⟨20295983319187350105866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54122622184499600282310445 20295983319187350105866417)
                ·
                  refine ⟨15221987489390512579399813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20295983319187350105866417 15221987489390512579399813)
                  ·
                    refine ⟨2854122654260721108637465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15221987489390512579399813 2854122654260721108637465)
                    ·
                      refine ⟨2140591990695540831478099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854122654260721108637465 2140591990695540831478099)
                      ·
                        rfl

theorem cell23_4168788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_4168788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168788 prefixEnd_4168788 := by exact prefixLift 4168788
  have htrace : WordTrace (prefixWord ++ tailWord_4168788) baseStart_4168788 baseEnd_4168788 := by
    simpa [prefixWord, tailWord_4168788, baseEnd_4168788] using wordTrace_append hprefix tailTrace_4168788
  have hstable : (prefixWord ++ tailWord_4168788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168788).length < 2 ^ (prefixWord ++ tailWord_4168788).sum := by decide
  have hdescent : baseEnd_4168788 < baseStart_4168788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168791 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_4168791 : Nat := 118140960795 + 4168791 * 2 ^ 59
def prefixEnd_4168791 : Nat := 4983230072969 + 3 ^ 40 * 4168791 * 2
def baseEnd_4168791 : Nat := 2140593531137504319740585

theorem tailTrace_4168791 : CollatzResearch.WordTrace tailWord_4168791 prefixEnd_4168791 2140593531137504319740585 := by
  unfold tailWord_4168791
  simp only [CollatzResearch.WordTrace]
  refine ⟨152048299040189654664858227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101365532693459769776572151 152048299040189654664858227)
  ·
    refine ⟨228072448560284481997287341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152048299040189654664858227 228072448560284481997287341)
    ·
      refine ⟨85527168210106680748982753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228072448560284481997287341 85527168210106680748982753)
      ·
        refine ⟨64145376157580010561737065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85527168210106680748982753 64145376157580010561737065)
        ·
          refine ⟨48109032118185007921302799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64145376157580010561737065 48109032118185007921302799)
          ·
            refine ⟨72163548177277511881954199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48109032118185007921302799 72163548177277511881954199)
            ·
              refine ⟨108245322265916267822931299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72163548177277511881954199 108245322265916267822931299)
              ·
                refine ⟨162367983398874401734396949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108245322265916267822931299 162367983398874401734396949)
                ·
                  refine ⟨7610999221822237581299857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162367983398874401734396949 7610999221822237581299857)
                  ·
                    refine ⟨5708249416366678185974893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7610999221822237581299857 5708249416366678185974893)
                    ·
                      refine ⟨2140593531137504319740585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708249416366678185974893 2140593531137504319740585)
                      ·
                        rfl

theorem cell23_4168791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_4168791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168791 prefixEnd_4168791 := by exact prefixLift 4168791
  have htrace : WordTrace (prefixWord ++ tailWord_4168791) baseStart_4168791 baseEnd_4168791 := by
    simpa [prefixWord, tailWord_4168791, baseEnd_4168791] using wordTrace_append hprefix tailTrace_4168791
  have hstable : (prefixWord ++ tailWord_4168791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168791).length < 2 ^ (prefixWord ++ tailWord_4168791).sum := by decide
  have hdescent : baseEnd_4168791 < baseStart_4168791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168794 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_4168794 : Nat := 118140960795 + 4168794 * 2 ^ 59
def prefixEnd_4168794 : Nat := 4983230072969 + 3 ^ 40 * 4168794 * 2
def baseEnd_4168794 : Nat := 237843896842163089778119

theorem tailTrace_4168794 : CollatzResearch.WordTrace tailWord_4168794 prefixEnd_4168794 237843896842163089778119 := by
  unfold tailWord_4168794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38012102114794696544304359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101365605639452524118144957 38012102114794696544304359)
  ·
    refine ⟨57018153172192044816456539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38012102114794696544304359 57018153172192044816456539)
    ·
      refine ⟨85527229758288067224684809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57018153172192044816456539 85527229758288067224684809)
      ·
        refine ⟨64145422318716050418513607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85527229758288067224684809 64145422318716050418513607)
        ·
          refine ⟨96218133478074075627770411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64145422318716050418513607 96218133478074075627770411)
          ·
            refine ⟨144327200217111113441655617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96218133478074075627770411 144327200217111113441655617)
            ·
              refine ⟨108245400162833335081241713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144327200217111113441655617 108245400162833335081241713)
              ·
                refine ⟨81184050122125001310931285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108245400162833335081241713 81184050122125001310931285)
                ·
                  refine ⟨237843896842163089778119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81184050122125001310931285 237843896842163089778119)
                  ·
                    rfl

theorem cell23_4168794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_4168794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168794 prefixEnd_4168794 := by exact prefixLift 4168794
  have htrace : WordTrace (prefixWord ++ tailWord_4168794) baseStart_4168794 baseEnd_4168794 := by
    simpa [prefixWord, tailWord_4168794, baseEnd_4168794] using wordTrace_append hprefix tailTrace_4168794
  have hstable : (prefixWord ++ tailWord_4168794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168794).length < 2 ^ (prefixWord ++ tailWord_4168794).sum := by decide
  have hdescent : baseEnd_4168794 < baseStart_4168794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168841 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_4168841 : Nat := 118140960795 + 4168841 * 2 ^ 59
def prefixEnd_4168841 : Nat := 4983230072969 + 3 ^ 40 * 4168841 * 2
def baseEnd_4168841 : Nat := 713539735056743041371785

theorem tailTrace_4168841 : CollatzResearch.WordTrace tailWord_4168841 prefixEnd_4168841 713539735056743041371785 := by
  unfold tailWord_4168841
  simp only [CollatzResearch.WordTrace]
  refine ⟨152050122690008513204178377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101366748460005675469452251 152050122690008513204178377)
  ·
    refine ⟨114037592017506384903133783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152050122690008513204178377 114037592017506384903133783)
    ·
      refine ⟨171056388026259577354700675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114037592017506384903133783 171056388026259577354700675)
      ·
        refine ⟨256584582039389366032051013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171056388026259577354700675 256584582039389366032051013)
        ·
          refine ⟨48109609132385506131009565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256584582039389366032051013 48109609132385506131009565)
          ·
            refine ⟨18041103424644564799128587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48109609132385506131009565 18041103424644564799128587)
            ·
              refine ⟨27061655136966847198692881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18041103424644564799128587 27061655136966847198692881)
              ·
                refine ⟨20296241352725135399019661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27061655136966847198692881 20296241352725135399019661)
                ·
                  refine ⟨7611090507271925774632373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20296241352725135399019661 7611090507271925774632373)
                  ·
                    refine ⟨713539735056743041371785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7611090507271925774632373 713539735056743041371785)
                    ·
                      rfl

theorem cell23_4168841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_4168841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168841 prefixEnd_4168841 := by exact prefixLift 4168841
  have htrace : WordTrace (prefixWord ++ tailWord_4168841) baseStart_4168841 baseEnd_4168841 := by
    simpa [prefixWord, tailWord_4168841, baseEnd_4168841] using wordTrace_append hprefix tailTrace_4168841
  have hstable : (prefixWord ++ tailWord_4168841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168841).length < 2 ^ (prefixWord ++ tailWord_4168841).sum := by decide
  have hdescent : baseEnd_4168841 < baseStart_4168841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168855 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_4168855 : Nat := 118140960795 + 4168855 * 2 ^ 59
def prefixEnd_4168855 : Nat := 4983230072969 + 3 ^ 40 * 4168855 * 2
def baseEnd_4168855 : Nat := 2140626393899392069340291

theorem tailTrace_4168855 : CollatzResearch.WordTrace tailWord_4168855 prefixEnd_4168855 2140626393899392069340291 := by
  unfold tailWord_4168855
  simp only [CollatzResearch.WordTrace]
  refine ⟨152050633311957793595188019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101367088874638529063458679 152050633311957793595188019)
  ·
    refine ⟨228075949967936690392782029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152050633311957793595188019 228075949967936690392782029)
    ·
      refine ⟨85528481237976258897293261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228075949967936690392782029 85528481237976258897293261)
      ·
        refine ⟨32073180464241097086484973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85528481237976258897293261 32073180464241097086484973)
        ·
          refine ⟨12027442674090411407431865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32073180464241097086484973 12027442674090411407431865)
          ·
            refine ⟨9020582005567808555573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12027442674090411407431865 9020582005567808555573899)
            ·
              refine ⟨13530873008351712833360849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020582005567808555573899 13530873008351712833360849)
              ·
                refine ⟨10148154756263784625020637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13530873008351712833360849 10148154756263784625020637)
                ·
                  refine ⟨3805558033598919234382739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10148154756263784625020637 3805558033598919234382739)
                  ·
                    refine ⟨5708337050398378851574109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805558033598919234382739 5708337050398378851574109)
                    ·
                      refine ⟨2140626393899392069340291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708337050398378851574109 2140626393899392069340291)
                      ·
                        rfl

theorem cell23_4168855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_4168855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168855 prefixEnd_4168855 := by exact prefixLift 4168855
  have htrace : WordTrace (prefixWord ++ tailWord_4168855) baseStart_4168855 baseEnd_4168855 := by
    simpa [prefixWord, tailWord_4168855, baseEnd_4168855] using wordTrace_append hprefix tailTrace_4168855
  have hstable : (prefixWord ++ tailWord_4168855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168855).length < 2 ^ (prefixWord ++ tailWord_4168855).sum := by decide
  have hdescent : baseEnd_4168855 < baseStart_4168855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168858 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_4168858 : Nat := 118140960795 + 4168858 * 2 ^ 59
def prefixEnd_4168858 : Nat := 4983230072969 + 3 ^ 40 * 4168858 * 2
def baseEnd_4168858 : Nat := 713542644780451852534259

theorem tailTrace_4168858 : CollatzResearch.WordTrace tailWord_4168858 prefixEnd_4168858 713542644780451852534259 := by
  unfold tailWord_4168858
  simp only [CollatzResearch.WordTrace]
  refine ⟨38012685682736731276886807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101367161820631283405031485 38012685682736731276886807)
  ·
    refine ⟨57019028524105096915330211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38012685682736731276886807 57019028524105096915330211)
    ·
      refine ⟨85528542786157645372995317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57019028524105096915330211 85528542786157645372995317)
      ·
        refine ⟨8018300886202279253718311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85528542786157645372995317 8018300886202279253718311)
        ·
          refine ⟨12027451329303418880577467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018300886202279253718311 12027451329303418880577467)
          ·
            refine ⟨18041176993955128320866201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12027451329303418880577467 18041176993955128320866201)
            ·
              refine ⟨13530882745466346240649651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18041176993955128320866201 13530882745466346240649651)
              ·
                refine ⟨20296324118199519360974477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13530882745466346240649651 20296324118199519360974477)
                ·
                  refine ⟨7611121544324819760365429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20296324118199519360974477 7611121544324819760365429)
                  ·
                    refine ⟨713542644780451852534259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7611121544324819760365429 713542644780451852534259)
                    ·
                      rfl

theorem cell23_4168858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_4168858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168858 prefixEnd_4168858 := by exact prefixLift 4168858
  have htrace : WordTrace (prefixWord ++ tailWord_4168858) baseStart_4168858 baseEnd_4168858 := by
    simpa [prefixWord, tailWord_4168858, baseEnd_4168858] using wordTrace_append hprefix tailTrace_4168858
  have hstable : (prefixWord ++ tailWord_4168858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168858).length < 2 ^ (prefixWord ++ tailWord_4168858).sum := by decide
  have hdescent : baseEnd_4168858 < baseStart_4168858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168888 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_4168888 : Nat := 118140960795 + 4168888 * 2 ^ 59
def prefixEnd_4168888 : Nat := 4983230072969 + 3 ^ 40 * 4168888 * 2
def baseEnd_4168888 : Nat := 713547779586996813409213

theorem tailTrace_4168888 : CollatzResearch.WordTrace tailWord_4168888 prefixEnd_4168888 713547779586996813409213 := by
  unfold tailWord_4168888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76025918460419120115569659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101367891280558826820759545 76025918460419120115569659)
  ·
    refine ⟨114038877690628680173354489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76025918460419120115569659 114038877690628680173354489)
    ·
      refine ⟨85529158267971510130015867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114038877690628680173354489 85529158267971510130015867)
      ·
        refine ⟨128293737401957265195023801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85529158267971510130015867 128293737401957265195023801)
        ·
          refine ⟨96220303051467948896267851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128293737401957265195023801 96220303051467948896267851)
          ·
            refine ⟨144330454577201923344401777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96220303051467948896267851 144330454577201923344401777)
            ·
              refine ⟨108247840932901442508301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144330454577201923344401777 108247840932901442508301333)
              ·
                refine ⟨5074117543729755117576625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108247840932901442508301333 5074117543729755117576625)
                ·
                  refine ⟨3805588157797316338182469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074117543729755117576625 3805588157797316338182469)
                  ·
                    refine ⟨713547779586996813409213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805588157797316338182469 713547779586996813409213)
                    ·
                      rfl

theorem cell23_4168888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_4168888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168888 prefixEnd_4168888 := by exact prefixLift 4168888
  have htrace : WordTrace (prefixWord ++ tailWord_4168888) baseStart_4168888 baseEnd_4168888 := by
    simpa [prefixWord, tailWord_4168888, baseEnd_4168888] using wordTrace_append hprefix tailTrace_4168888
  have hstable : (prefixWord ++ tailWord_4168888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168888).length < 2 ^ (prefixWord ++ tailWord_4168888).sum := by decide
  have hdescent : baseEnd_4168888 < baseStart_4168888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168895 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 3, 2, 2]
def baseStart_4168895 : Nat := 118140960795 + 4168895 * 2 ^ 59
def prefixEnd_4168895 : Nat := 4983230072969 + 3 ^ 40 * 4168895 * 2
def baseEnd_4168895 : Nat := 2140646933125571912840107

theorem tailTrace_4168895 : CollatzResearch.WordTrace tailWord_4168895 prefixEnd_4168895 2140646933125571912840107 := by
  unfold tailWord_4168895
  simp only [CollatzResearch.WordTrace]
  refine ⟨152052092231812880426644139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101368061487875253617762759 152052092231812880426644139)
  ·
    refine ⟨228078138347719320639966209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152052092231812880426644139 228078138347719320639966209)
    ·
      refine ⟨171058603760789490479974657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228078138347719320639966209 171058603760789490479974657)
      ·
        refine ⟨128293952820592117859980993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171058603760789490479974657 128293952820592117859980993)
        ·
          refine ⟨96220464615444088394985745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128293952820592117859980993 96220464615444088394985745)
          ·
            refine ⟨72165348461583066296239309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96220464615444088394985745 72165348461583066296239309)
            ·
              refine ⟨27062005673093649861089741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72165348461583066296239309 27062005673093649861089741)
              ·
                refine ⟨10148252127410118697908653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27062005673093649861089741 10148252127410118697908653)
                ·
                  refine ⟨3805594547778794511715745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10148252127410118697908653 3805594547778794511715745)
                  ·
                    refine ⟨2854195910834095883786809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805594547778794511715745 2854195910834095883786809)
                    ·
                      refine ⟨2140646933125571912840107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854195910834095883786809 2140646933125571912840107)
                      ·
                        rfl

theorem cell23_4168895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_4168895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168895 prefixEnd_4168895 := by exact prefixLift 4168895
  have htrace : WordTrace (prefixWord ++ tailWord_4168895) baseStart_4168895 baseEnd_4168895 := by
    simpa [prefixWord, tailWord_4168895, baseEnd_4168895] using wordTrace_append hprefix tailTrace_4168895
  have hstable : (prefixWord ++ tailWord_4168895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168895).length < 2 ^ (prefixWord ++ tailWord_4168895).sum := by decide
  have hdescent : baseEnd_4168895 < baseStart_4168895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168909 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4168909 : Nat := 118140960795 + 4168909 * 2 ^ 59
def prefixEnd_4168909 : Nat := 4983230072969 + 3 ^ 40 * 4168909 * 2
def baseEnd_4168909 : Nat := 713551373951578286021681

theorem tailTrace_4168909 : CollatzResearch.WordTrace tailWord_4168909 prefixEnd_4168909 713551373951578286021681 := by
  unfold tailWord_4168909
  simp only [CollatzResearch.WordTrace]
  refine ⟨152052602853762160817653781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101368401902508107211769187 152052602853762160817653781)
  ·
    refine ⟨7127465758770101288327521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152052602853762160817653781 7127465758770101288327521)
    ·
      refine ⟨5345599319077575966245641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7127465758770101288327521 5345599319077575966245641)
      ·
        refine ⟨4009199489308181974684231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5345599319077575966245641 4009199489308181974684231)
        ·
          refine ⟨6013799233962272962026347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009199489308181974684231 6013799233962272962026347)
          ·
            refine ⟨9020698850943409443039521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013799233962272962026347 9020698850943409443039521)
            ·
              refine ⟨6765524138207557082279641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020698850943409443039521 6765524138207557082279641)
              ·
                refine ⟨5074143103655667811709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765524138207557082279641 5074143103655667811709731)
                ·
                  refine ⟨7611214655483501717564597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074143103655667811709731 7611214655483501717564597)
                  ·
                    refine ⟨713551373951578286021681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7611214655483501717564597 713551373951578286021681)
                    ·
                      rfl

theorem cell23_4168909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4168909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168909 prefixEnd_4168909 := by exact prefixLift 4168909
  have htrace : WordTrace (prefixWord ++ tailWord_4168909) baseStart_4168909 baseEnd_4168909 := by
    simpa [prefixWord, tailWord_4168909, baseEnd_4168909] using wordTrace_append hprefix tailTrace_4168909
  have hstable : (prefixWord ++ tailWord_4168909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168909).length < 2 ^ (prefixWord ++ tailWord_4168909).sum := by decide
  have hdescent : baseEnd_4168909 < baseStart_4168909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168929 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_4168929 : Nat := 118140960795 + 4168929 * 2 ^ 59
def prefixEnd_4168929 : Nat := 4983230072969 + 3 ^ 40 * 4168929 * 2
def baseEnd_4168929 : Nat := 2140664391467824779814951

theorem tailTrace_4168929 : CollatzResearch.WordTrace tailWord_4168929 prefixEnd_4168929 2140664391467824779814951 := by
  unfold tailWord_4168929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152053332313689704233381841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101368888209126469488921227 152053332313689704233381841)
  ·
    refine ⟨114039999235267278175036381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152053332313689704233381841 114039999235267278175036381)
    ·
      refine ⟨42764999713225229315638643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114039999235267278175036381 42764999713225229315638643)
      ·
        refine ⟨64147499569837843973457965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42764999713225229315638643 64147499569837843973457965)
        ·
          refine ⟨24055312338689191490046737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64147499569837843973457965 24055312338689191490046737)
          ·
            refine ⟨18041484254016893617535053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24055312338689191490046737 18041484254016893617535053)
            ·
              refine ⟨6765556595256335106575645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18041484254016893617535053 6765556595256335106575645)
              ·
                refine ⟨2537083723221125664965867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6765556595256335106575645 2537083723221125664965867)
                ·
                  refine ⟨3805625584831688497448801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537083723221125664965867 3805625584831688497448801)
                  ·
                    refine ⟨2854219188623766373086601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805625584831688497448801 2854219188623766373086601)
                    ·
                      refine ⟨2140664391467824779814951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854219188623766373086601 2140664391467824779814951)
                      ·
                        rfl

theorem cell23_4168929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_4168929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168929 prefixEnd_4168929 := by exact prefixLift 4168929
  have htrace : WordTrace (prefixWord ++ tailWord_4168929) baseStart_4168929 baseEnd_4168929 := by
    simpa [prefixWord, tailWord_4168929, baseEnd_4168929] using wordTrace_append hprefix tailTrace_4168929
  have hstable : (prefixWord ++ tailWord_4168929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168929).length < 2 ^ (prefixWord ++ tailWord_4168929).sum := by decide
  have hdescent : baseEnd_4168929 < baseStart_4168929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168935 : List Nat := [1, 1, 5, 3, 3, 1, 9]
def baseStart_4168935 : Nat := 118140960795 + 4168935 * 2 ^ 59
def prefixEnd_4168935 : Nat := 4983230072969 + 3 ^ 40 * 4168935 * 2
def baseEnd_4168935 : Nat := 26427993485824095757283

theorem tailTrace_4168935 : CollatzResearch.WordTrace tailWord_4168935 prefixEnd_4168935 26427993485824095757283 := by
  unfold tailWord_4168935
  simp only [CollatzResearch.WordTrace]
  refine ⟨152053551151667967258100259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101369034101111978172066839 152053551151667967258100259)
  ·
    refine ⟨228080326727501950887150389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152053551151667967258100259 228080326727501950887150389)
    ·
      refine ⟨21382530630703307895670349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228080326727501950887150389 21382530630703307895670349)
      ·
        refine ⟨8018448986513740460876381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21382530630703307895670349 8018448986513740460876381)
        ·
          refine ⟨3006918369942652672828643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8018448986513740460876381 3006918369942652672828643)
          ·
            refine ⟨4510377554913979009242965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006918369942652672828643 4510377554913979009242965)
            ·
              refine ⟨26427993485824095757283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4510377554913979009242965 26427993485824095757283)
              ·
                rfl

theorem cell23_4168935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 9].length) (baseStart_4168935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168935 prefixEnd_4168935 := by exact prefixLift 4168935
  have htrace : WordTrace (prefixWord ++ tailWord_4168935) baseStart_4168935 baseEnd_4168935 := by
    simpa [prefixWord, tailWord_4168935, baseEnd_4168935] using wordTrace_append hprefix tailTrace_4168935
  have hstable : (prefixWord ++ tailWord_4168935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168935).length < 2 ^ (prefixWord ++ tailWord_4168935).sum := by decide
  have hdescent : baseEnd_4168935 < baseStart_4168935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168945 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_4168945 : Nat := 118140960795 + 4168945 * 2 ^ 59
def prefixEnd_4168945 : Nat := 4983230072969 + 3 ^ 40 * 4168945 * 2
def baseEnd_4168945 : Nat := 2140672607158296717214877

theorem tailTrace_4168945 : CollatzResearch.WordTrace tailWord_4168945 prefixEnd_4168945 2140672607158296717214877 := by
  unfold tailWord_4168945
  simp only [CollatzResearch.WordTrace]
  refine ⟨152053915881631738965964289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101369277254421159310642859 152053915881631738965964289)
  ·
    refine ⟨114040436911223804224473217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152053915881631738965964289 114040436911223804224473217)
    ·
      refine ⟨85530327683417853168354913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114040436911223804224473217 85530327683417853168354913)
      ·
        refine ⟨64147745762563389876266185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85530327683417853168354913 64147745762563389876266185)
        ·
          refine ⟨48110809321922542407199639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64147745762563389876266185 48110809321922542407199639)
          ·
            refine ⟨72166213982883813610799459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48110809321922542407199639 72166213982883813610799459)
            ·
              refine ⟨108249320974325720416199189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72166213982883813610799459 108249320974325720416199189)
              ·
                refine ⟨5074186920671518144509337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108249320974325720416199189 5074186920671518144509337)
                ·
                  refine ⟨3805640190503638608382003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074186920671518144509337 3805640190503638608382003)
                  ·
                    refine ⟨5708460285755457912573005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805640190503638608382003 5708460285755457912573005)
                    ·
                      refine ⟨2140672607158296717214877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708460285755457912573005 2140672607158296717214877)
                      ·
                        rfl

theorem cell23_4168945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_4168945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168945 prefixEnd_4168945 := by exact prefixLift 4168945
  have htrace : WordTrace (prefixWord ++ tailWord_4168945) baseStart_4168945 baseEnd_4168945 := by
    simpa [prefixWord, tailWord_4168945, baseEnd_4168945] using wordTrace_append hprefix tailTrace_4168945
  have hstable : (prefixWord ++ tailWord_4168945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168945).length < 2 ^ (prefixWord ++ tailWord_4168945).sum := by decide
  have hdescent : baseEnd_4168945 < baseStart_4168945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168946 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4168946 : Nat := 118140960795 + 4168946 * 2 ^ 59
def prefixEnd_4168946 : Nat := 4983230072969 + 3 ^ 40 * 4168946 * 2
def baseEnd_4168946 : Nat := 2140673120638951213302373

theorem tailTrace_4168946 : CollatzResearch.WordTrace tailWord_4168946 prefixEnd_4168946 2140673120638951213302373 := by
  unfold tailWord_4168946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013488088657029034187673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101369301569752077424500461 38013488088657029034187673)
  ·
    refine ⟨28510116066492771775640755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38013488088657029034187673 28510116066492771775640755)
    ·
      refine ⟨42765174099739157663461133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28510116066492771775640755 42765174099739157663461133)
      ·
        refine ⟨16036940287402184123797925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42765174099739157663461133 16036940287402184123797925)
        ·
          refine ⟨3006926303887909523212111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16036940287402184123797925 3006926303887909523212111)
          ·
            refine ⟨4510389455831864284818167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006926303887909523212111 4510389455831864284818167)
            ·
              refine ⟨6765584183747796427227251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510389455831864284818167 6765584183747796427227251)
              ·
                refine ⟨10148376275621694640840877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765584183747796427227251 10148376275621694640840877)
                ·
                  refine ⟨3805641103358135490315329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10148376275621694640840877 3805641103358135490315329)
                  ·
                    refine ⟨2854230827518601617736497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805641103358135490315329 2854230827518601617736497)
                    ·
                      refine ⟨2140673120638951213302373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854230827518601617736497 2140673120638951213302373)
                      ·
                        rfl

theorem cell23_4168946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4168946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168946 prefixEnd_4168946 := by exact prefixLift 4168946
  have htrace : WordTrace (prefixWord ++ tailWord_4168946) baseStart_4168946 baseEnd_4168946 := by
    simpa [prefixWord, tailWord_4168946, baseEnd_4168946] using wordTrace_append hprefix tailTrace_4168946
  have hstable : (prefixWord ++ tailWord_4168946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168946).length < 2 ^ (prefixWord ++ tailWord_4168946).sum := by decide
  have hdescent : baseEnd_4168946 < baseStart_4168946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168951 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4168951 : Nat := 118140960795 + 4168951 * 2 ^ 59
def prefixEnd_4168951 : Nat := 4983230072969 + 3 ^ 40 * 4168951 * 2
def baseEnd_4168951 : Nat := 2140675688042223693739849

theorem tailTrace_4168951 : CollatzResearch.WordTrace tailWord_4168951 prefixEnd_4168951 2140675688042223693739849 := by
  unfold tailWord_4168951
  simp only [CollatzResearch.WordTrace]
  refine ⟨152054134719610001990682707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101369423146406667993788471 152054134719610001990682707)
  ·
    refine ⟨228081202079415002986024061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152054134719610001990682707 228081202079415002986024061)
    ·
      refine ⟨85530450779780626119759023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228081202079415002986024061 85530450779780626119759023)
      ·
        refine ⟨128295676169670939179638535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85530450779780626119759023 128295676169670939179638535)
        ·
          refine ⟨192443514254506408769457803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128295676169670939179638535 192443514254506408769457803)
          ·
            refine ⟨288665271381759613154186705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192443514254506408769457803 288665271381759613154186705)
            ·
              refine ⟨216498953536319709865640029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288665271381759613154186705 216498953536319709865640029)
              ·
                refine ⟨81187107576119891199615011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216498953536319709865640029 81187107576119891199615011)
                ·
                  refine ⟨121780661364179836799422517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81187107576119891199615011 121780661364179836799422517)
                  ·
                    refine ⟨11416937002891859699945861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121780661364179836799422517 11416937002891859699945861)
                    ·
                      refine ⟨2140675688042223693739849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11416937002891859699945861 2140675688042223693739849)
                      ·
                        rfl

theorem cell23_4168951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4168951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168951 prefixEnd_4168951 := by exact prefixLift 4168951
  have htrace : WordTrace (prefixWord ++ tailWord_4168951) baseStart_4168951 baseEnd_4168951 := by
    simpa [prefixWord, tailWord_4168951, baseEnd_4168951] using wordTrace_append hprefix tailTrace_4168951
  have hstable : (prefixWord ++ tailWord_4168951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168951).length < 2 ^ (prefixWord ++ tailWord_4168951).sum := by decide
  have hdescent : baseEnd_4168951 < baseStart_4168951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168972 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_4168972 : Nat := 118140960795 + 4168972 * 2 ^ 59
def prefixEnd_4168972 : Nat := 4983230072969 + 3 ^ 40 * 4168972 * 2
def baseEnd_4168972 : Nat := 2140686471135968111577253

theorem tailTrace_4168972 : CollatzResearch.WordTrace tailWord_4168972 prefixEnd_4168972 2140686471135968111577253 := by
  unfold tailWord_4168972
  simp only [CollatzResearch.WordTrace]
  refine ⟨76027450326266961288598585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101369933768355948384798113 76027450326266961288598585)
  ·
    refine ⟨57020587744700220966448939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76027450326266961288598585 57020587744700220966448939)
    ·
      refine ⟨85530881617050331449673409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57020587744700220966448939 85530881617050331449673409)
      ·
        refine ⟨64148161212787748587255057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85530881617050331449673409 64148161212787748587255057)
        ·
          refine ⟨48111120909590811440441293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64148161212787748587255057 48111120909590811440441293)
          ·
            refine ⟨18041670341096554290165485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48111120909590811440441293 18041670341096554290165485)
            ·
              refine ⟨6765626377911207858812057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18041670341096554290165485 6765626377911207858812057)
              ·
                refine ⟨5074219783433405894109043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765626377911207858812057 5074219783433405894109043)
                ·
                  refine ⟨7611329675150108841163565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074219783433405894109043 7611329675150108841163565)
                  ·
                    refine ⟨2854248628181290815436337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7611329675150108841163565 2854248628181290815436337)
                    ·
                      refine ⟨2140686471135968111577253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854248628181290815436337 2140686471135968111577253)
                      ·
                        rfl

theorem cell23_4168972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_4168972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168972 prefixEnd_4168972 := by exact prefixLift 4168972
  have htrace : WordTrace (prefixWord ++ tailWord_4168972) baseStart_4168972 baseEnd_4168972 := by
    simpa [prefixWord, tailWord_4168972, baseEnd_4168972] using wordTrace_append hprefix tailTrace_4168972
  have hstable : (prefixWord ++ tailWord_4168972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168972).length < 2 ^ (prefixWord ++ tailWord_4168972).sum := by decide
  have hdescent : baseEnd_4168972 < baseStart_4168972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168988 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4168988 : Nat := 118140960795 + 4168988 * 2 ^ 59
def prefixEnd_4168988 : Nat := 4983230072969 + 3 ^ 40 * 4168988 * 2
def baseEnd_4168988 : Nat := 2140694686826440048977179

theorem tailTrace_4168988 : CollatzResearch.WordTrace tailWord_4168988 prefixEnd_4168988 2140694686826440048977179 := by
  unfold tailWord_4168988
  simp only [CollatzResearch.WordTrace]
  refine ⟨76027742110237978654889809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101370322813650638206519745 76027742110237978654889809)
  ·
    refine ⟨57020806582678483991167357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76027742110237978654889809 57020806582678483991167357)
    ·
      refine ⟨21382802468504431496687759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57020806582678483991167357 21382802468504431496687759)
      ·
        refine ⟨32074203702756647245031639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21382802468504431496687759 32074203702756647245031639)
        ·
          refine ⟨48111305554134970867547459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32074203702756647245031639 48111305554134970867547459)
          ·
            refine ⟨72166958331202456301321189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48111305554134970867547459 72166958331202456301321189)
            ·
              refine ⟨13531304687100460556497723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72166958331202456301321189 13531304687100460556497723)
              ·
                refine ⟨20296957030650690834746585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531304687100460556497723 20296957030650690834746585)
                ·
                  refine ⟨15222717772988018126059939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20296957030650690834746585 15222717772988018126059939)
                  ·
                    refine ⟨22834076659482027189089909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15222717772988018126059939 22834076659482027189089909)
                    ·
                      refine ⟨2140694686826440048977179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22834076659482027189089909 2140694686826440048977179)
                      ·
                        rfl

theorem cell23_4168988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4168988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168988 prefixEnd_4168988 := by exact prefixLift 4168988
  have htrace : WordTrace (prefixWord ++ tailWord_4168988) baseStart_4168988 baseEnd_4168988 := by
    simpa [prefixWord, tailWord_4168988, baseEnd_4168988] using wordTrace_append hprefix tailTrace_4168988
  have hstable : (prefixWord ++ tailWord_4168988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168988).length < 2 ^ (prefixWord ++ tailWord_4168988).sum := by decide
  have hdescent : baseEnd_4168988 < baseStart_4168988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169025 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 7]
def baseStart_4169025 : Nat := 118140960795 + 4169025 * 2 ^ 59
def prefixEnd_4169025 : Nat := 4983230072969 + 3 ^ 40 * 4169025 * 2
def baseEnd_4169025 : Nat := 237857076178961822690501

theorem tailTrace_4169025 : CollatzResearch.WordTrace tailWord_4169025 prefixEnd_4169025 237857076178961822690501 := by
  unfold tailWord_4169025
  simp only [CollatzResearch.WordTrace]
  refine ⟨152056833721341912628876529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101371222480894608419251019 152056833721341912628876529)
  ·
    refine ⟨114042625291006434471657397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152056833721341912628876529 114042625291006434471657397)
    ·
      refine ⟨10691496121031853231717881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114042625291006434471657397 10691496121031853231717881)
      ·
        refine ⟨8018622090773889923788411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10691496121031853231717881 8018622090773889923788411)
        ·
          refine ⟨12027933136160834885682617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8018622090773889923788411 12027933136160834885682617)
          ·
            refine ⟨9020949852120626164261963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12027933136160834885682617 9020949852120626164261963)
            ·
              refine ⟨13531424778180939246392945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9020949852120626164261963 13531424778180939246392945)
              ·
                refine ⟨10148568583635704434794709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13531424778180939246392945 10148568583635704434794709)
                ·
                  refine ⟨237857076178961822690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10148568583635704434794709 237857076178961822690501)
                  ·
                    rfl

theorem cell23_4169025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_4169025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169025 prefixEnd_4169025 := by exact prefixLift 4169025
  have htrace : WordTrace (prefixWord ++ tailWord_4169025) baseStart_4169025 baseEnd_4169025 := by
    simpa [prefixWord, tailWord_4169025, baseEnd_4169025] using wordTrace_append hprefix tailTrace_4169025
  have hstable : (prefixWord ++ tailWord_4169025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169025).length < 2 ^ (prefixWord ++ tailWord_4169025).sum := by decide
  have hdescent : baseEnd_4169025 < baseStart_4169025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169038 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_4169038 : Nat := 118140960795 + 4169038 * 2 ^ 59
def prefixEnd_4169038 : Nat := 4983230072969 + 3 ^ 40 * 4169038 * 2
def baseEnd_4169038 : Nat := 713573453619721617783983

theorem tailTrace_4169038 : CollatzResearch.WordTrace tailWord_4169038 prefixEnd_4169038 713573453619721617783983 := by
  unfold tailWord_4169038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19007163483786851981137471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101371538580196543899399845 19007163483786851981137471)
  ·
    refine ⟨28510745225680277971706207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19007163483786851981137471 28510745225680277971706207)
    ·
      refine ⟨42766117838520416957559311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28510745225680277971706207 42766117838520416957559311)
      ·
        refine ⟨64149176757780625436338967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42766117838520416957559311 64149176757780625436338967)
        ·
          refine ⟨96223765136670938154508451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64149176757780625436338967 96223765136670938154508451)
          ·
            refine ⟨144335647705006407231762677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96223765136670938154508451 144335647705006407231762677)
            ·
              refine ⟨13531466972344350677977751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144335647705006407231762677 13531466972344350677977751)
              ·
                refine ⟨20297200458516526016966627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531466972344350677977751 20297200458516526016966627)
                ·
                  refine ⟨30445800687774789025449941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20297200458516526016966627 30445800687774789025449941)
                  ·
                    refine ⟨713573453619721617783983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30445800687774789025449941 713573453619721617783983)
                    ·
                      rfl

theorem cell23_4169038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_4169038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169038 prefixEnd_4169038 := by exact prefixLift 4169038
  have htrace : WordTrace (prefixWord ++ tailWord_4169038) baseStart_4169038 baseEnd_4169038 := by
    simpa [prefixWord, tailWord_4169038, baseEnd_4169038] using wordTrace_append hprefix tailTrace_4169038
  have hstable : (prefixWord ++ tailWord_4169038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169038).length < 2 ^ (prefixWord ++ tailWord_4169038).sum := by decide
  have hdescent : baseEnd_4169038 < baseStart_4169038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169053 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4169053 : Nat := 118140960795 + 4169053 * 2 ^ 59
def prefixEnd_4169053 : Nat := 4983230072969 + 3 ^ 40 * 4169053 * 2
def baseEnd_4169053 : Nat := 2140728063068982294664381

theorem tailTrace_4169053 : CollatzResearch.WordTrace tailWord_4169053 prefixEnd_4169053 2140728063068982294664381 := by
  unfold tailWord_4169053
  simp only [CollatzResearch.WordTrace]
  refine ⟨152057854965240473410895813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101371903310160315607263875 152057854965240473410895813)
  ·
    refine ⟨28510847805982588764542965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152057854965240473410895813 28510847805982588764542965)
    ·
      refine ⟨2672891981810867696675903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28510847805982588764542965 2672891981810867696675903)
      ·
        refine ⟨4009337972716301545013855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672891981810867696675903 4009337972716301545013855)
        ·
          refine ⟨6014006959074452317520783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009337972716301545013855 6014006959074452317520783)
          ·
            refine ⟨9021010438611678476281175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014006959074452317520783 9021010438611678476281175)
            ·
              refine ⟨13531515657917517714421763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021010438611678476281175 13531515657917517714421763)
              ·
                refine ⟨20297273486876276571632645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531515657917517714421763 20297273486876276571632645)
                ·
                  refine ⟨3805738778789301857181121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20297273486876276571632645 3805738778789301857181121)
                  ·
                    refine ⟨2854304084091976392885841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3805738778789301857181121 2854304084091976392885841)
                    ·
                      refine ⟨2140728063068982294664381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854304084091976392885841 2140728063068982294664381)
                      ·
                        rfl

theorem cell23_4169053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4169053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169053 prefixEnd_4169053 := by exact prefixLift 4169053
  have htrace : WordTrace (prefixWord ++ tailWord_4169053) baseStart_4169053 baseEnd_4169053 := by
    simpa [prefixWord, tailWord_4169053, baseEnd_4169053] using wordTrace_append hprefix tailTrace_4169053
  have hstable : (prefixWord ++ tailWord_4169053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169053).length < 2 ^ (prefixWord ++ tailWord_4169053).sum := by decide
  have hdescent : baseEnd_4169053 < baseStart_4169053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169085 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_4169085 : Nat := 118140960795 + 4169085 * 2 ^ 59
def prefixEnd_4169085 : Nat := 4983230072969 + 3 ^ 40 * 4169085 * 2
def baseEnd_4169085 : Nat := 713581498149975389821411

theorem tailTrace_4169085 : CollatzResearch.WordTrace tailWord_4169085 prefixEnd_4169085 713581498149975389821411 := by
  unfold tailWord_4169085
  simp only [CollatzResearch.WordTrace]
  refine ⟨152059022101124542876060709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101372681400749695250707139 152059022101124542876060709)
  ·
    refine ⟨28511066643960851789261383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152059022101124542876060709 28511066643960851789261383)
    ·
      refine ⟨42766599965941277683892075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28511066643960851789261383 42766599965941277683892075)
      ·
        refine ⟨64149899948911916525838113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42766599965941277683892075 64149899948911916525838113)
        ·
          refine ⟨48112424961683937394378585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64149899948911916525838113 48112424961683937394378585)
          ·
            refine ⟨36084318721262953045783939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48112424961683937394378585 36084318721262953045783939)
            ·
              refine ⟨54126478081894429568675909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36084318721262953045783939 54126478081894429568675909)
              ·
                refine ⟨10148714640355205544126733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54126478081894429568675909 10148714640355205544126733)
                ·
                  refine ⟨3805767990133202079047525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10148714640355205544126733 3805767990133202079047525)
                  ·
                    refine ⟨713581498149975389821411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805767990133202079047525 713581498149975389821411)
                    ·
                      rfl

theorem cell23_4169085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_4169085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169085 prefixEnd_4169085 := by exact prefixLift 4169085
  have htrace : WordTrace (prefixWord ++ tailWord_4169085) baseStart_4169085 baseEnd_4169085 := by
    simpa [prefixWord, tailWord_4169085, baseEnd_4169085] using wordTrace_append hprefix tailTrace_4169085
  have hstable : (prefixWord ++ tailWord_4169085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169085).length < 2 ^ (prefixWord ++ tailWord_4169085).sum := by decide
  have hdescent : baseEnd_4169085 < baseStart_4169085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169095 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_4169095 : Nat := 118140960795 + 4169095 * 2 ^ 59
def prefixEnd_4169095 : Nat := 4983230072969 + 3 ^ 40 * 4169095 * 2
def baseEnd_4169095 : Nat := 2140749629256471130339187

theorem tailTrace_4169095 : CollatzResearch.WordTrace tailWord_4169095 prefixEnd_4169095 2140749629256471130339187 := by
  unfold tailWord_4169095
  simp only [CollatzResearch.WordTrace]
  refine ⟨152059386831088314583924739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101372924554058876389283159 152059386831088314583924739)
  ·
    refine ⟨228089080246632471875887109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152059386831088314583924739 228089080246632471875887109)
    ·
      refine ⟨42766702546243588476728833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228089080246632471875887109 42766702546243588476728833)
      ·
        refine ⟨32075026909682691357546625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42766702546243588476728833 32075026909682691357546625)
        ·
          refine ⟨24056270182262018518159969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32075026909682691357546625 24056270182262018518159969)
          ·
            refine ⟨18042202636696513888619977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24056270182262018518159969 18042202636696513888619977)
            ·
              refine ⟨13531651977522385416464983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18042202636696513888619977 13531651977522385416464983)
              ·
                refine ⟨20297477966283578124697475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13531651977522385416464983 20297477966283578124697475)
                ·
                  refine ⟨30446216949425367187046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20297477966283578124697475 30446216949425367187046213)
                  ·
                    refine ⟨5708665678017256347571165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30446216949425367187046213 5708665678017256347571165)
                    ·
                      refine ⟨2140749629256471130339187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708665678017256347571165 2140749629256471130339187)
                      ·
                        rfl

theorem cell23_4169095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_4169095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169095 prefixEnd_4169095 := by exact prefixLift 4169095
  have htrace : WordTrace (prefixWord ++ tailWord_4169095) baseStart_4169095 baseEnd_4169095 := by
    simpa [prefixWord, tailWord_4169095, baseEnd_4169095] using wordTrace_append hprefix tailTrace_4169095
  have hstable : (prefixWord ++ tailWord_4169095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169095).length < 2 ^ (prefixWord ++ tailWord_4169095).sum := by decide
  have hdescent : baseEnd_4169095 < baseStart_4169095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169135 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 5, 2]
def baseStart_4169135 : Nat := 118140960795 + 4169135 * 2 ^ 59
def prefixEnd_4169135 : Nat := 4983230072969 + 3 ^ 40 * 4169135 * 2
def baseEnd_4169135 : Nat := 2140770168482650973839003

theorem tailTrace_4169135 : CollatzResearch.WordTrace tailWord_4169135 prefixEnd_4169135 2140770168482650973839003 := by
  unfold tailWord_4169135
  simp only [CollatzResearch.WordTrace]
  refine ⟨152060845750943401415380859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101373897167295600943587239 152060845750943401415380859)
  ·
    refine ⟨228091268626415102123071289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152060845750943401415380859 228091268626415102123071289)
    ·
      refine ⟨171068451469811326592303467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228091268626415102123071289 171068451469811326592303467)
      ·
        refine ⟨256602677204716989888455201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171068451469811326592303467 256602677204716989888455201)
        ·
          refine ⟨192452007903537742416341401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256602677204716989888455201 192452007903537742416341401)
          ·
            refine ⟨144339005927653306812256051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192452007903537742416341401 144339005927653306812256051)
            ·
              refine ⟨216508508891479960218384077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144339005927653306812256051 216508508891479960218384077)
              ·
                refine ⟨81190690834304985081894029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216508508891479960218384077 81190690834304985081894029)
                ·
                  refine ⟨30446509062864369405710261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81190690834304985081894029 30446509062864369405710261)
                  ·
                    refine ⟨2854360224643534631785337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30446509062864369405710261 2854360224643534631785337)
                    ·
                      refine ⟨2140770168482650973839003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854360224643534631785337 2140770168482650973839003)
                      ·
                        rfl

theorem cell23_4169135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5, 2].length) (baseStart_4169135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169135 prefixEnd_4169135 := by exact prefixLift 4169135
  have htrace : WordTrace (prefixWord ++ tailWord_4169135) baseStart_4169135 baseEnd_4169135 := by
    simpa [prefixWord, tailWord_4169135, baseEnd_4169135] using wordTrace_append hprefix tailTrace_4169135
  have hstable : (prefixWord ++ tailWord_4169135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169135).length < 2 ^ (prefixWord ++ tailWord_4169135).sum := by decide
  have hdescent : baseEnd_4169135 < baseStart_4169135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169138 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4169138 : Nat := 118140960795 + 4169138 * 2 ^ 59
def prefixEnd_4169138 : Nat := 4983230072969 + 3 ^ 40 * 4169138 * 2
def baseEnd_4169138 : Nat := 2140771708924614462101489

theorem tailTrace_4169138 : CollatzResearch.WordTrace tailWord_4169138 prefixEnd_4169138 2140771708924614462101489 := by
  unfold tailWord_4169138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015238792483133231935017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101373970113288355285160045 38015238792483133231935017)
  ·
    refine ⟨28511429094362349923951263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38015238792483133231935017 28511429094362349923951263)
    ·
      refine ⟨42767143641543524885926895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28511429094362349923951263 42767143641543524885926895)
      ·
        refine ⟨64150715462315287328890343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42767143641543524885926895 64150715462315287328890343)
        ·
          refine ⟨96226073193472930993335515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64150715462315287328890343 96226073193472930993335515)
          ·
            refine ⟨144339109790209396490003273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96226073193472930993335515 144339109790209396490003273)
            ·
              refine ⟨108254332342657047367502455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144339109790209396490003273 108254332342657047367502455)
              ·
                refine ⟨162381498513985571051253683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108254332342657047367502455 162381498513985571051253683)
                ·
                  refine ⟨243572247770978356576880525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162381498513985571051253683 243572247770978356576880525)
                  ·
                    refine ⟨91339592914116883716330197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243572247770978356576880525 91339592914116883716330197)
                    ·
                      refine ⟨2140771708924614462101489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91339592914116883716330197 2140771708924614462101489)
                      ·
                        rfl

theorem cell23_4169138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4169138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169138 prefixEnd_4169138 := by exact prefixLift 4169138
  have htrace : WordTrace (prefixWord ++ tailWord_4169138) baseStart_4169138 baseEnd_4169138 := by
    simpa [prefixWord, tailWord_4169138, baseEnd_4169138] using wordTrace_append hprefix tailTrace_4169138
  have hstable : (prefixWord ++ tailWord_4169138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169138).length < 2 ^ (prefixWord ++ tailWord_4169138).sum := by decide
  have hdescent : baseEnd_4169138 < baseStart_4169138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169152 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2]
def baseStart_4169152 : Nat := 118140960795 + 4169152 * 2 ^ 59
def prefixEnd_4169152 : Nat := 4983230072969 + 3 ^ 40 * 4169152 * 2
def baseEnd_4169152 : Nat := 2140778897653777407326425

theorem tailTrace_4169152 : CollatzResearch.WordTrace tailWord_4169152 prefixEnd_4169152 2140778897653777407326425 := by
  unfold tailWord_4169152
  simp only [CollatzResearch.WordTrace]
  refine ⟨76030732895940906659374855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101374310527921208879166473 76030732895940906659374855)
  ·
    refine ⟨114046099343911359989062283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76030732895940906659374855 114046099343911359989062283)
    ·
      refine ⟨171069149015867039983593425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114046099343911359989062283 171069149015867039983593425)
      ·
        refine ⟨128301861761900279987695069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171069149015867039983593425 128301861761900279987695069)
        ·
          refine ⟨48113198160712604995385651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128301861761900279987695069 48113198160712604995385651)
          ·
            refine ⟨72169797241068907493078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48113198160712604995385651 72169797241068907493078477)
            ·
              refine ⟨27063673965400840309904429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72169797241068907493078477 27063673965400840309904429)
              ·
                refine ⟨10148877737025315116214161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27063673965400840309904429 10148877737025315116214161)
                ·
                  refine ⟨7611658302768986337160621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10148877737025315116214161 7611658302768986337160621)
                  ·
                    refine ⟨2854371863538369876435233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7611658302768986337160621 2854371863538369876435233)
                    ·
                      refine ⟨2140778897653777407326425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854371863538369876435233 2140778897653777407326425)
                      ·
                        rfl

theorem cell23_4169152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_4169152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169152 prefixEnd_4169152 := by exact prefixLift 4169152
  have htrace : WordTrace (prefixWord ++ tailWord_4169152) baseStart_4169152 baseEnd_4169152 := by
    simpa [prefixWord, tailWord_4169152, baseEnd_4169152] using wordTrace_append hprefix tailTrace_4169152
  have hstable : (prefixWord ++ tailWord_4169152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169152).length < 2 ^ (prefixWord ++ tailWord_4169152).sum := by decide
  have hdescent : baseEnd_4169152 < baseStart_4169152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169159 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_4169159 : Nat := 118140960795 + 4169159 * 2 ^ 59
def prefixEnd_4169159 : Nat := 4983230072969 + 3 ^ 40 * 4169159 * 2
def baseEnd_4169159 : Nat := 2140782492018358879938893

theorem tailTrace_4169159 : CollatzResearch.WordTrace tailWord_4169159 prefixEnd_4169159 2140782492018358879938893 := by
  unfold tailWord_4169159
  simp only [CollatzResearch.WordTrace]
  refine ⟨152061721102856453514254531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101374480735237635676169687 152061721102856453514254531)
  ·
    refine ⟨228092581654284680271381797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152061721102856453514254531 228092581654284680271381797)
    ·
      refine ⟨42767359060178377550884087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228092581654284680271381797 42767359060178377550884087)
      ·
        refine ⟨64151038590267566326326131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42767359060178377550884087 64151038590267566326326131)
        ·
          refine ⟨96226557885401349489489197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64151038590267566326326131 96226557885401349489489197)
          ·
            refine ⟨36084959207025506058558449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96226557885401349489489197 36084959207025506058558449)
            ·
              refine ⟨27063719405269129543918837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36084959207025506058558449 27063719405269129543918837)
              ·
                refine ⟨2537223694243980894742391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27063719405269129543918837 2537223694243980894742391)
                ·
                  refine ⟨3805835541365971342113587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537223694243980894742391 3805835541365971342113587)
                  ·
                    refine ⟨5708753312048957013170381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805835541365971342113587 5708753312048957013170381)
                    ·
                      refine ⟨2140782492018358879938893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708753312048957013170381 2140782492018358879938893)
                      ·
                        rfl

theorem cell23_4169159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_4169159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169159 prefixEnd_4169159 := by exact prefixLift 4169159
  have htrace : WordTrace (prefixWord ++ tailWord_4169159) baseStart_4169159 baseEnd_4169159 := by
    simpa [prefixWord, tailWord_4169159, baseEnd_4169159] using wordTrace_append hprefix tailTrace_4169159
  have hstable : (prefixWord ++ tailWord_4169159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169159).length < 2 ^ (prefixWord ++ tailWord_4169159).sum := by decide
  have hdescent : baseEnd_4169159 < baseStart_4169159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169175 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 4, 4]
def baseStart_4169175 : Nat := 118140960795 + 4169175 * 2 ^ 59
def prefixEnd_4169175 : Nat := 4983230072969 + 3 ^ 40 * 4169175 * 2
def baseEnd_4169175 : Nat := 713596902569610272446273

theorem tailTrace_4169175 : CollatzResearch.WordTrace tailWord_4169175 prefixEnd_4169175 713596902569610272446273 := by
  unfold tailWord_4169175
  simp only [CollatzResearch.WordTrace]
  refine ⟨152062304670798488246836979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101374869780532325497891319 152062304670798488246836979)
  ·
    refine ⟨228093457006197732370255469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152062304670798488246836979 228093457006197732370255469)
    ·
      refine ⟨85535046377324149638845801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228093457006197732370255469 85535046377324149638845801)
      ·
        refine ⟨64151284782993112229134351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85535046377324149638845801 64151284782993112229134351)
        ·
          refine ⟨96226927174489668343701527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64151284782993112229134351 96226927174489668343701527)
          ·
            refine ⟨144340390761734502515552291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96226927174489668343701527 144340390761734502515552291)
            ·
              refine ⟨216510586142601753773328437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144340390761734502515552291 216510586142601753773328437)
              ·
                refine ⟨20297867450868914416249541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216510586142601753773328437 20297867450868914416249541)
                ·
                  refine ⟨3805850147037921453046789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20297867450868914416249541 3805850147037921453046789)
                  ·
                    refine ⟨713596902569610272446273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805850147037921453046789 713596902569610272446273)
                    ·
                      rfl

theorem cell23_4169175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_4169175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169175 prefixEnd_4169175 := by exact prefixLift 4169175
  have htrace : WordTrace (prefixWord ++ tailWord_4169175) baseStart_4169175 baseEnd_4169175 := by
    simpa [prefixWord, tailWord_4169175, baseEnd_4169175] using wordTrace_append hprefix tailTrace_4169175
  have hstable : (prefixWord ++ tailWord_4169175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169175).length < 2 ^ (prefixWord ++ tailWord_4169175).sum := by decide
  have hdescent : baseEnd_4169175 < baseStart_4169175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169176 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4169176 : Nat := 118140960795 + 4169176 * 2 ^ 59
def prefixEnd_4169176 : Nat := 4983230072969 + 3 ^ 40 * 4169176 * 2
def baseEnd_4169176 : Nat := 2140791221189485313426315

theorem tailTrace_4169176 : CollatzResearch.WordTrace tailWord_4169176 prefixEnd_4169176 2140791221189485313426315 := by
  unfold tailWord_4169176
  simp only [CollatzResearch.WordTrace]
  refine ⟨76031170571897432708811691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101374894095863243611748921 76031170571897432708811691)
  ·
    refine ⟨114046755857846149063217537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76031170571897432708811691 114046755857846149063217537)
    ·
      refine ⟨85535066893384611797413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114046755857846149063217537 85535066893384611797413153)
      ·
        refine ⟨64151300170038458848059865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85535066893384611797413153 64151300170038458848059865)
        ·
          refine ⟨48113475127528844136044899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64151300170038458848059865 48113475127528844136044899)
          ·
            refine ⟨72170212691293266204067349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48113475127528844136044899 72170212691293266204067349)
            ·
              refine ⟨3382978719904371853315657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72170212691293266204067349 3382978719904371853315657)
              ·
                refine ⟨2537234039928278889986743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382978719904371853315657 2537234039928278889986743)
                ·
                  refine ⟨3805851059892418334980115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537234039928278889986743 3805851059892418334980115)
                  ·
                    refine ⟨5708776589838627502470173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805851059892418334980115 5708776589838627502470173)
                    ·
                      refine ⟨2140791221189485313426315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708776589838627502470173 2140791221189485313426315)
                      ·
                        rfl

theorem cell23_4169176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4169176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169176 prefixEnd_4169176 := by exact prefixLift 4169176
  have htrace : WordTrace (prefixWord ++ tailWord_4169176) baseStart_4169176 baseEnd_4169176 := by
    simpa [prefixWord, tailWord_4169176, baseEnd_4169176] using wordTrace_append hprefix tailTrace_4169176
  have hstable : (prefixWord ++ tailWord_4169176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169176).length < 2 ^ (prefixWord ++ tailWord_4169176).sum := by decide
  have hdescent : baseEnd_4169176 < baseStart_4169176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169192 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4169192 : Nat := 118140960795 + 4169192 * 2 ^ 59
def prefixEnd_4169192 : Nat := 4983230072969 + 3 ^ 40 * 4169192 * 2
def baseEnd_4169192 : Nat := 713599812293319083608747

theorem tailTrace_4169192 : CollatzResearch.WordTrace tailWord_4169192 prefixEnd_4169192 713599812293319083608747 := by
  unfold tailWord_4169192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76031462355868450075102915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101375283141157933433470553 76031462355868450075102915)
  ·
    refine ⟨114047193533802675112654373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76031462355868450075102915 114047193533802675112654373)
    ·
      refine ⟨21383848787588001583622695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114047193533802675112654373 21383848787588001583622695)
      ·
        refine ⟨32075773181382002375434043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21383848787588001583622695 32075773181382002375434043)
        ·
          refine ⟨48113659772073003563151065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32075773181382002375434043 48113659772073003563151065)
          ·
            refine ⟨36085244829054752672363299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48113659772073003563151065 36085244829054752672363299)
            ·
              refine ⟨54127867243582129008544949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36085244829054752672363299 54127867243582129008544949)
              ·
                refine ⟨5074487554085824594551089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54127867243582129008544949 5074487554085824594551089)
                ·
                  refine ⟨3805865665564368445913317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074487554085824594551089 3805865665564368445913317)
                  ·
                    refine ⟨713599812293319083608747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3805865665564368445913317 713599812293319083608747)
                    ·
                      rfl

theorem cell23_4169192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4169192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169192 prefixEnd_4169192 := by exact prefixLift 4169192
  have htrace : WordTrace (prefixWord ++ tailWord_4169192) baseStart_4169192 baseEnd_4169192 := by
    simpa [prefixWord, tailWord_4169192, baseEnd_4169192] using wordTrace_append hprefix tailTrace_4169192
  have hstable : (prefixWord ++ tailWord_4169192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169192).length < 2 ^ (prefixWord ++ tailWord_4169192).sum := by decide
  have hdescent : baseEnd_4169192 < baseStart_4169192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169215 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_4169215 : Nat := 118140960795 + 4169215 * 2 ^ 59
def prefixEnd_4169215 : Nat := 4983230072969 + 3 ^ 40 * 4169215 * 2
def baseEnd_4169215 : Nat := 2140811246935010660838635

theorem tailTrace_4169215 : CollatzResearch.WordTrace tailWord_4169215 prefixEnd_4169215 2140811246935010660838635 := by
  unfold tailWord_4169215
  simp only [CollatzResearch.WordTrace]
  refine ⟨152063763590653575078293099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101375842393769050052195399 152063763590653575078293099)
  ·
    refine ⟨228095645385980362617439649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152063763590653575078293099 228095645385980362617439649)
    ·
      refine ⟨171071734039485271963079737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228095645385980362617439649 171071734039485271963079737)
      ·
        refine ⟨128303800529613953972309803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171071734039485271963079737 128303800529613953972309803)
        ·
          refine ⟨192455700794420930958464705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128303800529613953972309803 192455700794420930958464705)
          ·
            refine ⟨144341775595815698218848529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192455700794420930958464705 144341775595815698218848529)
            ·
              refine ⟨108256331696861773664136397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144341775595815698218848529 108256331696861773664136397)
              ·
                refine ⟨40596124386323165124051149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108256331696861773664136397 40596124386323165124051149)
                ·
                  refine ⟨15223546644871186921519181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40596124386323165124051149 15223546644871186921519181)
                  ·
                    refine ⟨5708829991826695095569693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15223546644871186921519181 5708829991826695095569693)
                    ·
                      refine ⟨2140811246935010660838635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708829991826695095569693 2140811246935010660838635)
                      ·
                        rfl

theorem cell23_4169215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_4169215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169215 prefixEnd_4169215 := by exact prefixLift 4169215
  have htrace : WordTrace (prefixWord ++ tailWord_4169215) baseStart_4169215 baseEnd_4169215 := by
    simpa [prefixWord, tailWord_4169215, baseEnd_4169215] using wordTrace_append hprefix tailTrace_4169215
  have hstable : (prefixWord ++ tailWord_4169215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169215).length < 2 ^ (prefixWord ++ tailWord_4169215).sum := by decide
  have hdescent : baseEnd_4169215 < baseStart_4169215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169249 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4169249 : Nat := 118140960795 + 4169249 * 2 ^ 59
def prefixEnd_4169249 : Nat := 4983230072969 + 3 ^ 40 * 4169249 * 2
def baseEnd_4169249 : Nat := 2140828705277263527813479

theorem tailTrace_4169249 : CollatzResearch.WordTrace tailWord_4169249 prefixEnd_4169249 2140828705277263527813479 := by
  unfold tailWord_4169249
  simp only [CollatzResearch.WordTrace]
  refine ⟨152065003672530398885030801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101376669115020265923353867 152065003672530398885030801)
  ·
    refine ⟨114048752754397799163773101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152065003672530398885030801 114048752754397799163773101)
    ·
      refine ⟨42768282282899174686414913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114048752754397799163773101 42768282282899174686414913)
      ·
        refine ⟨32076211712174381014811185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42768282282899174686414913 32076211712174381014811185)
        ·
          refine ⟨24057158784130785761108389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32076211712174381014811185 24057158784130785761108389)
          ·
            refine ⟨4510717272024522330207823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24057158784130785761108389 4510717272024522330207823)
            ·
              refine ⟨6766075908036783495311735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510717272024522330207823 6766075908036783495311735)
              ·
                refine ⟨10149113862055175242967603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766075908036783495311735 10149113862055175242967603)
                ·
                  refine ⟨15223670793082762864451405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10149113862055175242967603 15223670793082762864451405)
                  ·
                    refine ⟨5708876547406036074169277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15223670793082762864451405 5708876547406036074169277)
                    ·
                      refine ⟨2140828705277263527813479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5708876547406036074169277 2140828705277263527813479)
                      ·
                        rfl

theorem cell23_4169249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4169249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169249 prefixEnd_4169249 := by exact prefixLift 4169249
  have htrace : WordTrace (prefixWord ++ tailWord_4169249) baseStart_4169249 baseEnd_4169249 := by
    simpa [prefixWord, tailWord_4169249, baseEnd_4169249] using wordTrace_append hprefix tailTrace_4169249
  have hstable : (prefixWord ++ tailWord_4169249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169249).length < 2 ^ (prefixWord ++ tailWord_4169249).sum := by decide
  have hdescent : baseEnd_4169249 < baseStart_4169249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169256 : List Nat := [2, 1, 5, 2, 3, 1, 2, 7]
def baseStart_4169256 : Nat := 118140960795 + 4169256 * 2 ^ 59
def prefixEnd_4169256 : Nat := 4983230072969 + 3 ^ 40 * 4169256 * 2
def baseEnd_4169256 : Nat := 79290085171920185200961

theorem tailTrace_4169256 : CollatzResearch.WordTrace tailWord_4169256 prefixEnd_4169256 79290085171920185200961 := by
  unfold tailWord_4169256
  simp only [CollatzResearch.WordTrace]
  refine ⟨76032629491752519540267811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101376839322336692720357081 76032629491752519540267811)
  ·
    refine ⟨114048944237628779310401717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76032629491752519540267811 114048944237628779310401717)
    ·
      refine ⟨10692088522277698060350161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114048944237628779310401717 10692088522277698060350161)
      ·
        refine ⟨8019066391708273545262621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692088522277698060350161 8019066391708273545262621)
        ·
          refine ⟨3007149896890602579473483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8019066391708273545262621 3007149896890602579473483)
          ·
            refine ⟨4510724845335903869210225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007149896890602579473483 4510724845335903869210225)
            ·
              refine ⟨3383043634001927901907669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510724845335903869210225 3383043634001927901907669)
              ·
                refine ⟨79290085171920185200961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383043634001927901907669 79290085171920185200961)
                ·
                  rfl

theorem cell23_4169256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 7].length) (baseStart_4169256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169256 prefixEnd_4169256 := by exact prefixLift 4169256
  have htrace : WordTrace (prefixWord ++ tailWord_4169256) baseStart_4169256 baseEnd_4169256 := by
    simpa [prefixWord, tailWord_4169256, baseEnd_4169256] using wordTrace_append hprefix tailTrace_4169256
  have hstable : (prefixWord ++ tailWord_4169256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169256).length < 2 ^ (prefixWord ++ tailWord_4169256).sum := by decide
  have hdescent : baseEnd_4169256 < baseStart_4169256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169262 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4169262 : Nat := 118140960795 + 4169262 * 2 ^ 59
def prefixEnd_4169262 : Nat := 4983230072969 + 3 ^ 40 * 4169262 * 2
def baseEnd_4169262 : Nat := 2140835380525771976950919

theorem tailTrace_4169262 : CollatzResearch.WordTrace tailWord_4169262 prefixEnd_4169262 2140835380525771976950919 := by
  unfold tailWord_4169262
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008184727685412763156755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101376985214322201403502693 19008184727685412763156755)
  ·
    refine ⟨28512277091528119144735133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008184727685412763156755 28512277091528119144735133)
    ·
      refine ⟨10692103909323044679275675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28512277091528119144735133 10692103909323044679275675)
      ·
        refine ⟨16038155863984567018913513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692103909323044679275675 16038155863984567018913513)
        ·
          refine ⟨12028616897988425264185135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16038155863984567018913513 12028616897988425264185135)
          ·
            refine ⟨18042925346982637896277703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12028616897988425264185135 18042925346982637896277703)
            ·
              refine ⟨27064388020473956844416555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18042925346982637896277703 27064388020473956844416555)
              ·
                refine ⟨40596582030710935266624833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27064388020473956844416555 40596582030710935266624833)
                ·
                  refine ⟨30447436523033201449968625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40596582030710935266624833 30447436523033201449968625)
                  ·
                    refine ⟨22835577392274901087476469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30447436523033201449968625 22835577392274901087476469)
                    ·
                      refine ⟨2140835380525771976950919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22835577392274901087476469 2140835380525771976950919)
                      ·
                        rfl

theorem cell23_4169262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4169262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169262 prefixEnd_4169262 := by exact prefixLift 4169262
  have htrace : WordTrace (prefixWord ++ tailWord_4169262) baseStart_4169262 baseEnd_4169262 := by
    simpa [prefixWord, tailWord_4169262, baseEnd_4169262] using wordTrace_append hprefix tailTrace_4169262
  have hstable : (prefixWord ++ tailWord_4169262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169262).length < 2 ^ (prefixWord ++ tailWord_4169262).sum := by decide
  have hdescent : baseEnd_4169262 < baseStart_4169262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169389 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4169389 : Nat := 118140960795 + 4169389 * 2 ^ 59
def prefixEnd_4169389 : Nat := 4983230072969 + 3 ^ 40 * 4169389 * 2
def baseEnd_4169389 : Nat := 713633530856297660020945

theorem tailTrace_4169389 : CollatzResearch.WordTrace tailWord_4169389 prefixEnd_4169389 713633530856297660020945 := by
  unfold tailWord_4169389
  simp only [CollatzResearch.WordTrace]
  refine ⟨152070109892023202795127221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101380073261348801863418147 152070109892023202795127221)
  ·
    refine ⟨14256572802377175262043177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152070109892023202795127221 14256572802377175262043177)
    ·
      refine ⟨10692429601782881446532383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256572802377175262043177 10692429601782881446532383)
      ·
        refine ⟨16038644402674322169798575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692429601782881446532383 16038644402674322169798575)
        ·
          refine ⟨24057966604011483254697863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16038644402674322169798575 24057966604011483254697863)
          ·
            refine ⟨36086949906017224882046795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24057966604011483254697863 36086949906017224882046795)
            ·
              refine ⟨54130424859025837323070193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36086949906017224882046795 54130424859025837323070193)
              ·
                refine ⟨40597818644269377992302645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54130424859025837323070193 40597818644269377992302645)
                ·
                  refine ⟨3806045497900254186778373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40597818644269377992302645 3806045497900254186778373)
                  ·
                    refine ⟨713633530856297660020945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806045497900254186778373 713633530856297660020945)
                    ·
                      rfl

theorem cell23_4169389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4169389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169389 prefixEnd_4169389 := by exact prefixLift 4169389
  have htrace : WordTrace (prefixWord ++ tailWord_4169389) baseStart_4169389 baseEnd_4169389 := by
    simpa [prefixWord, tailWord_4169389, baseEnd_4169389] using wordTrace_append hprefix tailTrace_4169389
  have hstable : (prefixWord ++ tailWord_4169389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169389).length < 2 ^ (prefixWord ++ tailWord_4169389).sum := by decide
  have hdescent : baseEnd_4169389 < baseStart_4169389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169402 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_4169402 : Nat := 118140960795 + 4169402 * 2 ^ 59
def prefixEnd_4169402 : Nat := 4983230072969 + 3 ^ 40 * 4169402 * 2
def baseEnd_4169402 : Nat := 237878585313044603244475

theorem tailTrace_4169402 : CollatzResearch.WordTrace tailWord_4169402 prefixEnd_4169402 237878585313044603244475 := by
  unfold tailWord_4169402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38017646010244026503837615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101380389360650737343566973 38017646010244026503837615)
  ·
    refine ⟨57026469015366039755756423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38017646010244026503837615 57026469015366039755756423)
    ·
      refine ⟨85539703523049059633634635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57026469015366039755756423 85539703523049059633634635)
      ·
        refine ⟨128309555284573589450451953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85539703523049059633634635 128309555284573589450451953)
        ·
          refine ⟨96232166463430192087838965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128309555284573589450451953 96232166463430192087838965)
          ·
            refine ⟨9021765605946580508234903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96232166463430192087838965 9021765605946580508234903)
            ·
              refine ⟨13532648408919870762352355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9021765605946580508234903 13532648408919870762352355)
              ·
                refine ⟨20298972613379806143528533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13532648408919870762352355 20298972613379806143528533)
                ·
                  refine ⟨237878585313044603244475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20298972613379806143528533 237878585313044603244475)
                  ·
                    rfl

theorem cell23_4169402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_4169402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169402 prefixEnd_4169402 := by exact prefixLift 4169402
  have htrace : WordTrace (prefixWord ++ tailWord_4169402) baseStart_4169402 baseEnd_4169402 := by
    simpa [prefixWord, tailWord_4169402, baseEnd_4169402] using wordTrace_append hprefix tailTrace_4169402
  have hstable : (prefixWord ++ tailWord_4169402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169402).length < 2 ^ (prefixWord ++ tailWord_4169402).sum := by decide
  have hdescent : baseEnd_4169402 < baseStart_4169402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169406 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4169406 : Nat := 118140960795 + 4169406 * 2 ^ 59
def prefixEnd_4169406 : Nat := 4983230072969 + 3 ^ 40 * 4169406 * 2
def baseEnd_4169406 : Nat := 713636440580006471183419

theorem tailTrace_4169406 : CollatzResearch.WordTrace tailWord_4169406 prefixEnd_4169406 713636440580006471183419 := by
  unfold tailWord_4169406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008841241620201837312009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101380486621974409798997381 19008841241620201837312009)
  ·
    refine ⟨14256630931215151377984007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19008841241620201837312009 14256630931215151377984007)
    ·
      refine ⟨21384946396822727066976011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256630931215151377984007 21384946396822727066976011)
      ·
        refine ⟨32077419595234090600464017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384946396822727066976011 32077419595234090600464017)
        ·
          refine ⟨24058064696425567950348013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32077419595234090600464017 24058064696425567950348013)
          ·
            refine ⟨9021774261159587981380505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24058064696425567950348013 9021774261159587981380505)
            ·
              refine ⟨6766330695869690986035379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021774261159587981380505 6766330695869690986035379)
              ·
                refine ⟨10149496043804536479053069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766330695869690986035379 10149496043804536479053069)
                ·
                  refine ⟨3806061016426701179644901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10149496043804536479053069 3806061016426701179644901)
                  ·
                    refine ⟨713636440580006471183419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806061016426701179644901 713636440580006471183419)
                    ·
                      rfl

theorem cell23_4169406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4169406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169406 prefixEnd_4169406 := by exact prefixLift 4169406
  have htrace : WordTrace (prefixWord ++ tailWord_4169406) baseStart_4169406 baseEnd_4169406 := by
    simpa [prefixWord, tailWord_4169406, baseEnd_4169406] using wordTrace_append hprefix tailTrace_4169406
  have hstable : (prefixWord ++ tailWord_4169406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169406).length < 2 ^ (prefixWord ++ tailWord_4169406).sum := by decide
  have hdescent : baseEnd_4169406 < baseStart_4169406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169422 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4169422 : Nat := 118140960795 + 4169422 * 2 ^ 59
def prefixEnd_4169422 : Nat := 4983230072969 + 3 ^ 40 * 4169422 * 2
def baseEnd_4169422 : Nat := 2140917537430491350950183

theorem tailTrace_4169422 : CollatzResearch.WordTrace tailWord_4169422 prefixEnd_4169422 2140917537430491350950183 := by
  unfold tailWord_4169422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19008914187612956178884815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101380875667269099620719013 19008914187612956178884815)
  ·
    refine ⟨28513371281419434268327223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19008914187612956178884815 28513371281419434268327223)
    ·
      refine ⟨42770056922129151402490835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513371281419434268327223 42770056922129151402490835)
      ·
        refine ⟨64155085383193727103736253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42770056922129151402490835 64155085383193727103736253)
        ·
          refine ⟨24058157018697647663901095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64155085383193727103736253 24058157018697647663901095)
          ·
            refine ⟨36087235528046471495851643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24058157018697647663901095 36087235528046471495851643)
            ·
              refine ⟨54130853292069707243777465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36087235528046471495851643 54130853292069707243777465)
              ·
                refine ⟨40598139969052280432833099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54130853292069707243777465 40598139969052280432833099)
                ·
                  refine ⟨60897209953578420649249649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40598139969052280432833099 60897209953578420649249649)
                  ·
                    refine ⟨45672907465183815486937237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60897209953578420649249649 45672907465183815486937237)
                    ·
                      refine ⟨2140917537430491350950183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45672907465183815486937237 2140917537430491350950183)
                      ·
                        rfl

theorem cell23_4169422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4169422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169422 prefixEnd_4169422 := by exact prefixLift 4169422
  have htrace : WordTrace (prefixWord ++ tailWord_4169422) baseStart_4169422 baseEnd_4169422 := by
    simpa [prefixWord, tailWord_4169422, baseEnd_4169422] using wordTrace_append hprefix tailTrace_4169422
  have hstable : (prefixWord ++ tailWord_4169422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169422).length < 2 ^ (prefixWord ++ tailWord_4169422).sum := by decide
  have hdescent : baseEnd_4169422 < baseStart_4169422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169439 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 5, 2]
def baseStart_4169439 : Nat := 118140960795 + 4169439 * 2 ^ 59
def prefixEnd_4169439 : Nat := 4983230072969 + 3 ^ 40 * 4169439 * 2
def baseEnd_4169439 : Nat := 2140926266601617784437605

theorem tailTrace_4169439 : CollatzResearch.WordTrace tailWord_4169439 prefixEnd_4169439 2140926266601617784437605 := by
  unfold tailWord_4169439
  simp only [CollatzResearch.WordTrace]
  refine ⟨152071933541842061334447371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101381289027894707556298247 152071933541842061334447371)
  ·
    refine ⟨228107900312763092001671057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152071933541842061334447371 228107900312763092001671057)
    ·
      refine ⟨171080925234572319001253293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228107900312763092001671057 171080925234572319001253293)
      ·
        refine ⟨64155346962964619625469985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171080925234572319001253293 64155346962964619625469985)
        ·
          refine ⟨48116510222223464719102489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64155346962964619625469985 48116510222223464719102489)
          ·
            refine ⟨36087382666667598539326867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48116510222223464719102489 36087382666667598539326867)
            ·
              refine ⟨54131074000001397808990301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36087382666667598539326867 54131074000001397808990301)
              ·
                refine ⟨20299152750000524178371363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54131074000001397808990301 20299152750000524178371363)
                ·
                  refine ⟨30448729125000786267557045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20299152750000524178371363 30448729125000786267557045)
                  ·
                    refine ⟨2854568355468823712583473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30448729125000786267557045 2854568355468823712583473)
                    ·
                      refine ⟨2140926266601617784437605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854568355468823712583473 2140926266601617784437605)
                      ·
                        rfl

theorem cell23_4169439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_4169439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169439 prefixEnd_4169439 := by exact prefixLift 4169439
  have htrace : WordTrace (prefixWord ++ tailWord_4169439) baseStart_4169439 baseEnd_4169439 := by
    simpa [prefixWord, tailWord_4169439, baseEnd_4169439] using wordTrace_append hprefix tailTrace_4169439
  have hstable : (prefixWord ++ tailWord_4169439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169439).length < 2 ^ (prefixWord ++ tailWord_4169439).sum := by decide
  have hdescent : baseEnd_4169439 < baseStart_4169439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169469 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_4169469 : Nat := 118140960795 + 4169469 * 2 ^ 59
def prefixEnd_4169469 : Nat := 4983230072969 + 3 ^ 40 * 4169469 * 2
def baseEnd_4169469 : Nat := 2140941671021252667062467

theorem tailTrace_4169469 : CollatzResearch.WordTrace tailWord_4169469 prefixEnd_4169469 2140941671021252667062467 := by
  unfold tailWord_4169469
  simp only [CollatzResearch.WordTrace]
  refine ⟨152073027731733376458039461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101382018487822250972026307 152073027731733376458039461)
  ·
    refine ⟨28513692699700008085882399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152073027731733376458039461 28513692699700008085882399)
    ·
      refine ⟨42770539049550012128823599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513692699700008085882399 42770539049550012128823599)
      ·
        refine ⟨64155808574325018193235399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42770539049550012128823599 64155808574325018193235399)
        ·
          refine ⟨96233712861487527289853099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64155808574325018193235399 96233712861487527289853099)
          ·
            refine ⟨144350569292231290934779649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96233712861487527289853099 144350569292231290934779649)
            ·
              refine ⟨108262926969173468201084737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144350569292231290934779649 108262926969173468201084737)
              ·
                refine ⟨81197195226880101150813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108262926969173468201084737 81197195226880101150813553)
                ·
                  refine ⟨60897896420160075863110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81197195226880101150813553 60897896420160075863110165)
                  ·
                    refine ⟨2854588894695003556083289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60897896420160075863110165 2854588894695003556083289)
                    ·
                      refine ⟨2140941671021252667062467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854588894695003556083289 2140941671021252667062467)
                      ·
                        rfl

theorem cell23_4169469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_4169469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169469 prefixEnd_4169469 := by exact prefixLift 4169469
  have htrace : WordTrace (prefixWord ++ tailWord_4169469) baseStart_4169469 baseEnd_4169469 := by
    simpa [prefixWord, tailWord_4169469, baseEnd_4169469] using wordTrace_append hprefix tailTrace_4169469
  have hstable : (prefixWord ++ tailWord_4169469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169469).length < 2 ^ (prefixWord ++ tailWord_4169469).sum := by decide
  have hdescent : baseEnd_4169469 < baseStart_4169469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169470 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_4169470 : Nat := 118140960795 + 4169470 * 2 ^ 59
def prefixEnd_4169470 : Nat := 4983230072969 + 3 ^ 40 * 4169470 * 2
def baseEnd_4169470 : Nat := 237882464944656351461107

theorem tailTrace_4169470 : CollatzResearch.WordTrace tailWord_4169470 prefixEnd_4169470 237882464944656351461107 := by
  unfold tailWord_4169470
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009133025591219203603233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101382042803153169085883909 19009133025591219203603233)
  ·
    refine ⟨14256849769193414402702425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19009133025591219203603233 14256849769193414402702425)
    ·
      refine ⟨10692637326895060802026819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256849769193414402702425 10692637326895060802026819)
      ·
        refine ⟨16038955990342591203040229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692637326895060802026819 16038955990342591203040229)
        ·
          refine ⟨3007304248189235850570043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16038955990342591203040229 3007304248189235850570043)
          ·
            refine ⟨4510956372283853775855065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007304248189235850570043 4510956372283853775855065)
            ·
              refine ⟨3383217279212890331891299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4510956372283853775855065 3383217279212890331891299)
              ·
                refine ⟨5074825918819335497836949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383217279212890331891299 5074825918819335497836949)
                ·
                  refine ⟨237882464944656351461107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5074825918819335497836949 237882464944656351461107)
                  ·
                    rfl

theorem cell23_4169470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_4169470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169470 prefixEnd_4169470 := by exact prefixLift 4169470
  have htrace : WordTrace (prefixWord ++ tailWord_4169470) baseStart_4169470 baseEnd_4169470 := by
    simpa [prefixWord, tailWord_4169470, baseEnd_4169470] using wordTrace_append hprefix tailTrace_4169470
  have hstable : (prefixWord ++ tailWord_4169470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169470).length < 2 ^ (prefixWord ++ tailWord_4169470).sum := by decide
  have hdescent : baseEnd_4169470 < baseStart_4169470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169486 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4169486 : Nat := 118140960795 + 4169486 * 2 ^ 59
def prefixEnd_4169486 : Nat := 4983230072969 + 3 ^ 40 * 4169486 * 2
def baseEnd_4169486 : Nat := 2140950400192379100549889

theorem tailTrace_4169486 : CollatzResearch.WordTrace tailWord_4169486 prefixEnd_4169486 2140950400192379100549889 := by
  unfold tailWord_4169486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009205971583973545176039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101382431848447858907605541 19009205971583973545176039)
  ·
    refine ⟨28513808957375960317764059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19009205971583973545176039 28513808957375960317764059)
    ·
      refine ⟨42770713436063940476646089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513808957375960317764059 42770713436063940476646089)
      ·
        refine ⟨32078035077047955357484567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42770713436063940476646089 32078035077047955357484567)
        ·
          refine ⟨48117052615571933036226851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32078035077047955357484567 48117052615571933036226851)
          ·
            refine ⟨72175578923357899554340277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48117052615571933036226851 72175578923357899554340277)
            ·
              refine ⟨6766460524064803083219401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72175578923357899554340277 6766460524064803083219401)
              ·
                refine ⟨5074845393048602312414551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766460524064803083219401 5074845393048602312414551)
                ·
                  refine ⟨7612268089572903468621827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5074845393048602312414551 7612268089572903468621827)
                  ·
                    refine ⟨11418402134359355202932741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7612268089572903468621827 11418402134359355202932741)
                    ·
                      refine ⟨2140950400192379100549889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11418402134359355202932741 2140950400192379100549889)
                      ·
                        rfl

theorem cell23_4169486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4169486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169486 prefixEnd_4169486 := by exact prefixLift 4169486
  have htrace : WordTrace (prefixWord ++ tailWord_4169486) baseStart_4169486 baseEnd_4169486 := by
    simpa [prefixWord, tailWord_4169486, baseEnd_4169486] using wordTrace_append hprefix tailTrace_4169486
  have hstable : (prefixWord ++ tailWord_4169486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169486).length < 2 ^ (prefixWord ++ tailWord_4169486).sum := by decide
  have hdescent : baseEnd_4169486 < baseStart_4169486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169490 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4169490 : Nat := 118140960795 + 4169490 * 2 ^ 59
def prefixEnd_4169490 : Nat := 4983230072969 + 3 ^ 40 * 4169490 * 2
def baseEnd_4169490 : Nat := 2140952454114997084899871

theorem tailTrace_4169490 : CollatzResearch.WordTrace tailWord_4169490 prefixEnd_4169490 2140952454114997084899871 := by
  unfold tailWord_4169490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38018448416164324261138481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101382529109771531363035949 38018448416164324261138481)
  ·
    refine ⟨28513836312123243195853861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38018448416164324261138481 28513836312123243195853861)
    ·
      refine ⟨5346344308523108099222599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28513836312123243195853861 5346344308523108099222599)
      ·
        refine ⟨8019516462784662148833899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5346344308523108099222599 8019516462784662148833899)
        ·
          refine ⟨12029274694176993223250849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019516462784662148833899 12029274694176993223250849)
          ·
            refine ⟨9021956020632744917438137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12029274694176993223250849 9021956020632744917438137)
            ·
              refine ⟨6766467015474558688078603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9021956020632744917438137 6766467015474558688078603)
              ·
                refine ⟨10149700523211838032117905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766467015474558688078603 10149700523211838032117905)
                ·
                  refine ⟨7612275392408878524088429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10149700523211838032117905 7612275392408878524088429)
                  ·
                    refine ⟨2854603272153329446533161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7612275392408878524088429 2854603272153329446533161)
                    ·
                      refine ⟨2140952454114997084899871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854603272153329446533161 2140952454114997084899871)
                      ·
                        rfl

theorem cell23_4169490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4169490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169490 prefixEnd_4169490 := by exact prefixLift 4169490
  have htrace : WordTrace (prefixWord ++ tailWord_4169490) baseStart_4169490 baseEnd_4169490 := by
    simpa [prefixWord, tailWord_4169490, baseEnd_4169490] using wordTrace_append hprefix tailTrace_4169490
  have hstable : (prefixWord ++ tailWord_4169490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169490).length < 2 ^ (prefixWord ++ tailWord_4169490).sum := by decide
  have hdescent : baseEnd_4169490 < baseStart_4169490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169526 : List Nat := [5, 1, 2, 2, 1, 1, 3, 8]
def baseStart_4169526 : Nat := 118140960795 + 4169526 * 2 ^ 59
def prefixEnd_4169526 : Nat := 4983230072969 + 3 ^ 40 * 4169526 * 2
def baseEnd_4169526 : Nat := 79295219978465146075915

theorem tailTrace_4169526 : CollatzResearch.WordTrace tailWord_4169526 prefixEnd_4169526 79295219978465146075915 := by
  unfold tailWord_4169526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504694168282929699554027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101383404461684583461909621 9504694168282929699554027)
  ·
    refine ⟨14257041252424394549331041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9504694168282929699554027 14257041252424394549331041)
    ·
      refine ⟨10692780939318295911998281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257041252424394549331041 10692780939318295911998281)
      ·
        refine ⟨8019585704488721933998711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10692780939318295911998281 8019585704488721933998711)
        ·
          refine ⟨12029378556733082900998067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8019585704488721933998711 12029378556733082900998067)
          ·
            refine ⟨18044067835099624351497101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029378556733082900998067 18044067835099624351497101)
            ·
              refine ⟨6766525438162359131811413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18044067835099624351497101 6766525438162359131811413)
              ·
                refine ⟨79295219978465146075915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6766525438162359131811413 79295219978465146075915)
                ·
                  rfl

theorem cell23_4169526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_4169526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169526 prefixEnd_4169526 := by exact prefixLift 4169526
  have htrace : WordTrace (prefixWord ++ tailWord_4169526) baseStart_4169526 baseEnd_4169526 := by
    simpa [prefixWord, tailWord_4169526, baseEnd_4169526] using wordTrace_append hprefix tailTrace_4169526
  have hstable : (prefixWord ++ tailWord_4169526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169526).length < 2 ^ (prefixWord ++ tailWord_4169526).sum := by decide
  have hdescent : baseEnd_4169526 < baseStart_4169526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169546 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_4169546 : Nat := 118140960795 + 4169546 * 2 ^ 59
def prefixEnd_4169546 : Nat := 4983230072969 + 3 ^ 40 * 4169546 * 2
def baseEnd_4169546 : Nat := 2140981209031648865799613

theorem tailTrace_4169546 : CollatzResearch.WordTrace tailWord_4169546 prefixEnd_4169546 2140981209031648865799613 := by
  unfold tailWord_4169546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38018959038113604652148123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101383890768302945739061661 38018959038113604652148123)
  ·
    refine ⟨57028438557170406978222185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38018959038113604652148123 57028438557170406978222185)
    ·
      refine ⟨42771328917877805233666639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57028438557170406978222185 42771328917877805233666639)
      ·
        refine ⟨64156993376816707850499959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42771328917877805233666639 64156993376816707850499959)
        ·
          refine ⟨96235490065225061775749939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64156993376816707850499959 96235490065225061775749939)
          ·
            refine ⟨144353235097837592663624909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96235490065225061775749939 144353235097837592663624909)
            ·
              refine ⟨54132463161689097248859341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144353235097837592663624909 54132463161689097248859341)
              ·
                refine ⟨20299673685633411468322253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54132463161689097248859341 20299673685633411468322253)
                ·
                  refine ⟨7612377632112529300620845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20299673685633411468322253 7612377632112529300620845)
                  ·
                    refine ⟨2854641612042198487732817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7612377632112529300620845 2854641612042198487732817)
                    ·
                      refine ⟨2140981209031648865799613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854641612042198487732817 2140981209031648865799613)
                      ·
                        rfl

theorem cell23_4169546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_4169546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169546 prefixEnd_4169546 := by exact prefixLift 4169546
  have htrace : WordTrace (prefixWord ++ tailWord_4169546) baseStart_4169546 baseEnd_4169546 := by
    simpa [prefixWord, tailWord_4169546, baseEnd_4169546] using wordTrace_append hprefix tailTrace_4169546
  have hstable : (prefixWord ++ tailWord_4169546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169546).length < 2 ^ (prefixWord ++ tailWord_4169546).sum := by decide
  have hdescent : baseEnd_4169546 < baseStart_4169546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169552 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_4169552 : Nat := 118140960795 + 4169552 * 2 ^ 59
def prefixEnd_4169552 : Nat := 4983230072969 + 3 ^ 40 * 4169552 * 2
def baseEnd_4169552 : Nat := 713661429971858614108195

theorem tailTrace_4169552 : CollatzResearch.WordTrace tailWord_4169552 prefixEnd_4169552 713661429971858614108195 := by
  unfold tailWord_4169552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76038027495216340816655455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101384036660288454422207273 76038027495216340816655455)
  ·
    refine ⟨114057041242824511224983183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76038027495216340816655455 114057041242824511224983183)
    ·
      refine ⟨171085561864236766837474775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114057041242824511224983183 171085561864236766837474775)
      ·
        refine ⟨256628342796355150256212163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171085561864236766837474775 256628342796355150256212163)
        ·
          refine ⟨384942514194532725384318245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256628342796355150256212163 384942514194532725384318245)
          ·
            refine ⟨72176721411474886009559671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384942514194532725384318245 72176721411474886009559671)
            ·
              refine ⟨108265082117212329014339507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72176721411474886009559671 108265082117212329014339507)
              ·
                refine ⟨162397623175818493521509261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108265082117212329014339507 162397623175818493521509261)
                ·
                  refine ⟨60899108690931935070565973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162397623175818493521509261 60899108690931935070565973)
                  ·
                    refine ⟨713661429971858614108195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60899108690931935070565973 713661429971858614108195)
                    ·
                      rfl

theorem cell23_4169552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_4169552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169552 prefixEnd_4169552 := by exact prefixLift 4169552
  have htrace : WordTrace (prefixWord ++ tailWord_4169552) baseStart_4169552 baseEnd_4169552 := by
    simpa [prefixWord, tailWord_4169552, baseEnd_4169552] using wordTrace_append hprefix tailTrace_4169552
  have hstable : (prefixWord ++ tailWord_4169552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169552).length < 2 ^ (prefixWord ++ tailWord_4169552).sum := by decide
  have hdescent : baseEnd_4169552 < baseStart_4169552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169570 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4169570 : Nat := 118140960795 + 4169570 * 2 ^ 59
def prefixEnd_4169570 : Nat := 4983230072969 + 3 ^ 40 * 4169570 * 2
def baseEnd_4169570 : Nat := 2140993532567356771899503

theorem tailTrace_4169570 : CollatzResearch.WordTrace tailWord_4169570 prefixEnd_4169570 2140993532567356771899503 := by
  unfold tailWord_4169570
  simp only [CollatzResearch.WordTrace]
  refine ⟨38019177876091867676866541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101384474336244980471644109 38019177876091867676866541)
  ·
    refine ⟨14257191703534450378824953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38019177876091867676866541 14257191703534450378824953)
    ·
      refine ⟨10692893777650837784118715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14257191703534450378824953 10692893777650837784118715)
      ·
        refine ⟨16039340666476256676178073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10692893777650837784118715 16039340666476256676178073)
        ·
          refine ⟨12029505499857192507133555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16039340666476256676178073 12029505499857192507133555)
          ·
            refine ⟨18044258249785788760700333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12029505499857192507133555 18044258249785788760700333)
            ·
              refine ⟨6766596843669670785262625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18044258249785788760700333 6766596843669670785262625)
              ·
                refine ⟨5074947632752253088946969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766596843669670785262625 5074947632752253088946969)
                ·
                  refine ⟨3806210724564189816710227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5074947632752253088946969 3806210724564189816710227)
                  ·
                    refine ⟨5709316086846284725065341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806210724564189816710227 5709316086846284725065341)
                    ·
                      refine ⟨2140993532567356771899503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709316086846284725065341 2140993532567356771899503)
                      ·
                        rfl

theorem cell23_4169570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4169570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169570 prefixEnd_4169570 := by exact prefixLift 4169570
  have htrace : WordTrace (prefixWord ++ tailWord_4169570) baseStart_4169570 baseEnd_4169570 := by
    simpa [prefixWord, tailWord_4169570, baseEnd_4169570] using wordTrace_append hprefix tailTrace_4169570
  have hstable : (prefixWord ++ tailWord_4169570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169570).length < 2 ^ (prefixWord ++ tailWord_4169570).sum := by decide
  have hdescent : baseEnd_4169570 < baseStart_4169570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169633 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 7]
def baseStart_4169633 : Nat := 118140960795 + 4169633 * 2 ^ 59
def prefixEnd_4169633 : Nat := 4983230072969 + 3 ^ 40 * 4169633 * 2
def baseEnd_4169633 : Nat := 237891764649843336156857

theorem tailTrace_4169633 : CollatzResearch.WordTrace tailWord_4169633 prefixEnd_4169633 237891764649843336156857 := by
  unfold tailWord_4169633
  simp only [CollatzResearch.WordTrace]
  refine ⟨152079009303139232467009553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101386006202092821644673035 152079009303139232467009553)
  ·
    refine ⟨114059256977354424350257165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152079009303139232467009553 114059256977354424350257165)
    ·
      refine ⟨42772221366507909131346437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114059256977354424350257165 42772221366507909131346437)
      ·
        refine ⟨8019791506220232962127457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42772221366507909131346437 8019791506220232962127457)
        ·
          refine ⟨6014843629665174721595593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8019791506220232962127457 6014843629665174721595593)
          ·
            refine ⟨4511132722248881041196695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6014843629665174721595593 4511132722248881041196695)
            ·
              refine ⟨6766699083373321561795043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511132722248881041196695 6766699083373321561795043)
              ·
                refine ⟨10150048625059982342692565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766699083373321561795043 10150048625059982342692565)
                ·
                  refine ⟨237891764649843336156857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10150048625059982342692565 237891764649843336156857)
                  ·
                    rfl

theorem cell23_4169633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_4169633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169633 prefixEnd_4169633 := by exact prefixLift 4169633
  have htrace : WordTrace (prefixWord ++ tailWord_4169633) baseStart_4169633 baseEnd_4169633 := by
    simpa [prefixWord, tailWord_4169633, baseEnd_4169633] using wordTrace_append hprefix tailTrace_4169633
  have hstable : (prefixWord ++ tailWord_4169633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169633).length < 2 ^ (prefixWord ++ tailWord_4169633).sum := by decide
  have hdescent : baseEnd_4169633 < baseStart_4169633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169679 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_4169679 : Nat := 118140960795 + 4169679 * 2 ^ 59
def prefixEnd_4169679 : Nat := 4983230072969 + 3 ^ 40 * 4169679 * 2
def baseEnd_4169679 : Nat := 2141049501958696845436501

theorem tailTrace_4169679 : CollatzResearch.WordTrace tailWord_4169679 prefixEnd_4169679 2141049501958696845436501 := by
  unfold tailWord_4169679
  simp only [CollatzResearch.WordTrace]
  refine ⟨152080687060972582323184091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101387124707315054882122727 152080687060972582323184091)
  ·
    refine ⟨228121030591458873484776137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152080687060972582323184091 228121030591458873484776137)
    ·
      refine ⟨171090772943594155113582103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228121030591458873484776137 171090772943594155113582103)
      ·
        refine ⟨256636159415391232670373155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171090772943594155113582103 256636159415391232670373155)
        ·
          refine ⟨384954239123086849005559733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256636159415391232670373155 384954239123086849005559733)
          ·
            refine ⟨36089459917789392094271225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384954239123086849005559733 36089459917789392094271225)
            ·
              refine ⟨27067094938342044070703419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36089459917789392094271225 27067094938342044070703419)
              ·
                refine ⟨40600642407513066106055129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27067094938342044070703419 40600642407513066106055129)
                ·
                  refine ⟨30450481805634799579541347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40600642407513066106055129 30450481805634799579541347)
                  ·
                    refine ⟨45675722708452199369312021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30450481805634799579541347 45675722708452199369312021)
                    ·
                      refine ⟨2141049501958696845436501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45675722708452199369312021 2141049501958696845436501)
                      ·
                        rfl

theorem cell23_4169679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_4169679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169679 prefixEnd_4169679 := by exact prefixLift 4169679
  have htrace : WordTrace (prefixWord ++ tailWord_4169679) baseStart_4169679 baseEnd_4169679 := by
    simpa [prefixWord, tailWord_4169679, baseEnd_4169679] using wordTrace_append hprefix tailTrace_4169679
  have hstable : (prefixWord ++ tailWord_4169679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169679).length < 2 ^ (prefixWord ++ tailWord_4169679).sum := by decide
  have hdescent : baseEnd_4169679 < baseStart_4169679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169706 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_4169706 : Nat := 118140960795 + 4169706 * 2 ^ 59
def prefixEnd_4169706 : Nat := 4983230072969 + 3 ^ 40 * 4169706 * 2
def baseEnd_4169706 : Nat := 237895929548485359977653

theorem tailTrace_4169706 : CollatzResearch.WordTrace tailWord_4169706 prefixEnd_4169706 237895929548485359977653 := by
  unfold tailWord_4169706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38020417957968691483604243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101387781221249843956277981 38020417957968691483604243)
  ·
    refine ⟨57030626936953037225406365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38020417957968691483604243 57030626936953037225406365)
    ·
      refine ⟨21386485101357388959527387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57030626936953037225406365 21386485101357388959527387)
      ·
        refine ⟨32079727652036083439291081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21386485101357388959527387 32079727652036083439291081)
        ·
          refine ⟨24059795739027062579468311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32079727652036083439291081 24059795739027062579468311)
          ·
            refine ⟨36089693608540593869202467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24059795739027062579468311 36089693608540593869202467)
            ·
              refine ⟨54134540412810890803803701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36089693608540593869202467 54134540412810890803803701)
              ·
                refine ⟨5075113163701021012856597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54134540412810890803803701 5075113163701021012856597)
                ·
                  refine ⟨237895929548485359977653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5075113163701021012856597 237895929548485359977653)
                  ·
                    rfl

theorem cell23_4169706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_4169706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169706 prefixEnd_4169706 := by exact prefixLift 4169706
  have htrace : WordTrace (prefixWord ++ tailWord_4169706) baseStart_4169706 baseEnd_4169706 := by
    simpa [prefixWord, tailWord_4169706, baseEnd_4169706] using wordTrace_append hprefix tailTrace_4169706
  have hstable : (prefixWord ++ tailWord_4169706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169706).length < 2 ^ (prefixWord ++ tailWord_4169706).sum := by decide
  have hdescent : baseEnd_4169706 < baseStart_4169706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169770 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4169770 : Nat := 118140960795 + 4169770 * 2 ^ 59
def prefixEnd_4169770 : Nat := 4983230072969 + 3 ^ 40 * 4169770 * 2
def baseEnd_4169770 : Nat := 713698742899418663132861

theorem tailTrace_4169770 : CollatzResearch.WordTrace tailWord_4169770 prefixEnd_4169770 713698742899418663132861 := by
  unfold tailWord_4169770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38021001525910726216186691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101389337402428603243164509 38021001525910726216186691)
  ·
    refine ⟨57031502288866089324280037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38021001525910726216186691 57031502288866089324280037)
    ·
      refine ⟨10693406679162391748302507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57031502288866089324280037 10693406679162391748302507)
      ·
        refine ⟨16040110018743587622453761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693406679162391748302507 16040110018743587622453761)
        ·
          refine ⟨12030082514057690716840321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040110018743587622453761 12030082514057690716840321)
          ·
            refine ⟨9022561885543268037630241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12030082514057690716840321 9022561885543268037630241)
            ·
              refine ⟨6766921414157451028222681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9022561885543268037630241 6766921414157451028222681)
              ·
                refine ⟨5075191060618088271167011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6766921414157451028222681 5075191060618088271167011)
                ·
                  refine ⟨7612786590927132406750517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075191060618088271167011 7612786590927132406750517)
                  ·
                    refine ⟨713698742899418663132861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7612786590927132406750517 713698742899418663132861)
                    ·
                      rfl

theorem cell23_4169770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4169770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169770 prefixEnd_4169770 := by exact prefixLift 4169770
  have htrace : WordTrace (prefixWord ++ tailWord_4169770) baseStart_4169770 baseEnd_4169770 := by
    simpa [prefixWord, tailWord_4169770, baseEnd_4169770] using wordTrace_append hprefix tailTrace_4169770
  have hstable : (prefixWord ++ tailWord_4169770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169770).length < 2 ^ (prefixWord ++ tailWord_4169770).sum := by decide
  have hdescent : baseEnd_4169770 < baseStart_4169770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169784 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_4169784 : Nat := 118140960795 + 4169784 * 2 ^ 59
def prefixEnd_4169784 : Nat := 4983230072969 + 3 ^ 40 * 4169784 * 2
def baseEnd_4169784 : Nat := 2141103417427418934623519

theorem tailTrace_4169784 : CollatzResearch.WordTrace tailWord_4169784 prefixEnd_4169784 2141103417427418934623519 := by
  unfold tailWord_4169784
  simp only [CollatzResearch.WordTrace]
  refine ⟨76042258362796092627878203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101389677817061456837170937 76042258362796092627878203)
  ·
    refine ⟨114063387544194138941817305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76042258362796092627878203 114063387544194138941817305)
    ·
      refine ⟨85547540658145604206362979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114063387544194138941817305 85547540658145604206362979)
      ·
        refine ⟨128321310987218406309544469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85547540658145604206362979 128321310987218406309544469)
        ·
          refine ⟨6015061452525862795759897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128321310987218406309544469 6015061452525862795759897)
          ·
            refine ⟨4511296089394397096819923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6015061452525862795759897 4511296089394397096819923)
            ·
              refine ⟨6766944134091595645229885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511296089394397096819923 6766944134091595645229885)
              ·
                refine ⟨2537604050284348366961207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6766944134091595645229885 2537604050284348366961207)
                ·
                  refine ⟨3806406075426522550441811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537604050284348366961207 3806406075426522550441811)
                  ·
                    refine ⟨5709609113139783825662717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806406075426522550441811 5709609113139783825662717)
                    ·
                      refine ⟨2141103417427418934623519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709609113139783825662717 2141103417427418934623519)
                      ·
                        rfl

theorem cell23_4169784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_4169784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169784 prefixEnd_4169784 := by exact prefixLift 4169784
  have htrace : WordTrace (prefixWord ++ tailWord_4169784) baseStart_4169784 baseEnd_4169784 := by
    simpa [prefixWord, tailWord_4169784, baseEnd_4169784] using wordTrace_append hprefix tailTrace_4169784
  have hstable : (prefixWord ++ tailWord_4169784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169784).length < 2 ^ (prefixWord ++ tailWord_4169784).sum := by decide
  have hdescent : baseEnd_4169784 < baseStart_4169784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169786 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_4169786 : Nat := 118140960795 + 4169786 * 2 ^ 59
def prefixEnd_4169786 : Nat := 4983230072969 + 3 ^ 40 * 4169786 * 2
def baseEnd_4169786 : Nat := 2141104444388727926798509

theorem tailTrace_4169786 : CollatzResearch.WordTrace tailWord_4169786 prefixEnd_4169786 2141104444388727926798509 := by
  unfold tailWord_4169786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38021147417896234899332303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101389726447723293064886141 38021147417896234899332303)
  ·
    refine ⟨57031721126844352348998455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38021147417896234899332303 57031721126844352348998455)
    ·
      refine ⟨85547581690266528523497683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57031721126844352348998455 85547581690266528523497683)
      ·
        refine ⟨128321372535399792785246525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85547581690266528523497683 128321372535399792785246525)
        ·
          refine ⟨48120514700774922294467447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128321372535399792785246525 48120514700774922294467447)
          ·
            refine ⟨72180772051162383441701171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48120514700774922294467447 72180772051162383441701171)
            ·
              refine ⟨108271158076743575162551757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72180772051162383441701171 108271158076743575162551757)
              ·
                refine ⟨40601684278778840685956909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108271158076743575162551757 40601684278778840685956909)
                ·
                  refine ⟨15225631604542065257233841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40601684278778840685956909 15225631604542065257233841)
                  ·
                    refine ⟨11419223703406548942925381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15225631604542065257233841 11419223703406548942925381)
                    ·
                      refine ⟨2141104444388727926798509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11419223703406548942925381 2141104444388727926798509)
                      ·
                        rfl

theorem cell23_4169786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_4169786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169786 prefixEnd_4169786 := by exact prefixLift 4169786
  have htrace : WordTrace (prefixWord ++ tailWord_4169786) baseStart_4169786 baseEnd_4169786 := by
    simpa [prefixWord, tailWord_4169786, baseEnd_4169786] using wordTrace_append hprefix tailTrace_4169786
  have hstable : (prefixWord ++ tailWord_4169786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169786).length < 2 ^ (prefixWord ++ tailWord_4169786).sum := by decide
  have hdescent : baseEnd_4169786 < baseStart_4169786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169793 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4169793 : Nat := 118140960795 + 4169793 * 2 ^ 59
def prefixEnd_4169793 : Nat := 4983230072969 + 3 ^ 40 * 4169793 * 2
def baseEnd_4169793 : Nat := 2141108038753309399410977

theorem tailTrace_4169793 : CollatzResearch.WordTrace tailWord_4169793 prefixEnd_4169793 2141108038753309399410977 := by
  unfold tailWord_4169793
  simp only [CollatzResearch.WordTrace]
  refine ⟨152084844982559579792834033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101389896655039719861889355 152084844982559579792834033)
  ·
    refine ⟨114063633736919684844625525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152084844982559579792834033 114063633736919684844625525)
    ·
      refine ⟨10693465662836220454183643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114063633736919684844625525 10693465662836220454183643)
      ·
        refine ⟨16040198494254330681275465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693465662836220454183643 16040198494254330681275465)
        ·
          refine ⟨12030148870690748010956599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040198494254330681275465 12030148870690748010956599)
          ·
            refine ⟨18045223306036122016434899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030148870690748010956599 18045223306036122016434899)
            ·
              refine ⟨27067834959054183024652349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045223306036122016434899 27067834959054183024652349)
              ·
                refine ⟨10150438109645318634244631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27067834959054183024652349 10150438109645318634244631)
                ·
                  refine ⟨15225657164467977951366947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10150438109645318634244631 15225657164467977951366947)
                  ·
                    refine ⟨22838485746701966927050421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15225657164467977951366947 22838485746701966927050421)
                    ·
                      refine ⟨2141108038753309399410977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22838485746701966927050421 2141108038753309399410977)
                      ·
                        rfl

theorem cell23_4169793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4169793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169793 prefixEnd_4169793 := by exact prefixLift 4169793
  have htrace : WordTrace (prefixWord ++ tailWord_4169793) baseStart_4169793 baseEnd_4169793 := by
    simpa [prefixWord, tailWord_4169793, baseEnd_4169793] using wordTrace_append hprefix tailTrace_4169793
  have hstable : (prefixWord ++ tailWord_4169793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169793).length < 2 ^ (prefixWord ++ tailWord_4169793).sum := by decide
  have hdescent : baseEnd_4169793 < baseStart_4169793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169823 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_4169823 : Nat := 118140960795 + 4169823 * 2 ^ 59
def prefixEnd_4169823 : Nat := 4983230072969 + 3 ^ 40 * 4169823 * 2
def baseEnd_4169823 : Nat := 2141123443172944282035839

theorem tailTrace_4169823 : CollatzResearch.WordTrace tailWord_4169823 prefixEnd_4169823 2141123443172944282035839 := by
  unfold tailWord_4169823
  simp only [CollatzResearch.WordTrace]
  refine ⟨152085939172450894916426123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101390626114967263277617415 152085939172450894916426123)
  ·
    refine ⟨228128908758676342374639185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152085939172450894916426123 228128908758676342374639185)
    ·
      refine ⟨171096681569007256780979389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228128908758676342374639185 171096681569007256780979389)
      ·
        refine ⟨64161255588377721292867271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171096681569007256780979389 64161255588377721292867271)
        ·
          refine ⟨96241883382566581939300907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64161255588377721292867271 96241883382566581939300907)
          ·
            refine ⟨144362825073849872908951361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96241883382566581939300907 144362825073849872908951361)
            ·
              refine ⟨108272118805387404681713521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144362825073849872908951361 108272118805387404681713521)
              ·
                refine ⟨81204089104040553511285141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108272118805387404681713521 81204089104040553511285141)
                ·
                  refine ⟨3806441676751900945841491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81204089104040553511285141 3806441676751900945841491)
                  ·
                    refine ⟨5709662515127851418762237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806441676751900945841491 5709662515127851418762237)
                    ·
                      refine ⟨2141123443172944282035839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709662515127851418762237 2141123443172944282035839)
                      ·
                        rfl

theorem cell23_4169823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_4169823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169823 prefixEnd_4169823 := by exact prefixLift 4169823
  have htrace : WordTrace (prefixWord ++ tailWord_4169823) baseStart_4169823 baseEnd_4169823 := by
    simpa [prefixWord, tailWord_4169823, baseEnd_4169823] using wordTrace_append hprefix tailTrace_4169823
  have hstable : (prefixWord ++ tailWord_4169823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169823).length < 2 ^ (prefixWord ++ tailWord_4169823).sum := by decide
  have hdescent : baseEnd_4169823 < baseStart_4169823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169856 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_4169856 : Nat := 118140960795 + 4169856 * 2 ^ 59
def prefixEnd_4169856 : Nat := 4983230072969 + 3 ^ 40 * 4169856 * 2
def baseEnd_4169856 : Nat := 713713462678180884307729

theorem tailTrace_4169856 : CollatzResearch.WordTrace tailWord_4169856 prefixEnd_4169856 713713462678180884307729 := by
  unfold tailWord_4169856
  simp only [CollatzResearch.WordTrace]
  refine ⟨76043571390665670776188711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101391428520887561034918281 76043571390665670776188711)
  ·
    refine ⟨114065357085998506164283067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76043571390665670776188711 114065357085998506164283067)
    ·
      refine ⟨171098035628997759246424601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114065357085998506164283067 171098035628997759246424601)
      ·
        refine ⟨128323526721748319434818451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171098035628997759246424601 128323526721748319434818451)
        ·
          refine ⟨192485290082622479152227677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128323526721748319434818451 192485290082622479152227677)
          ·
            refine ⟨72181983780983429682085379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192485290082622479152227677 72181983780983429682085379)
            ·
              refine ⟨108272975671475144523128069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72181983780983429682085379 108272975671475144523128069)
              ·
                refine ⟨20301182938401589598086513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108272975671475144523128069 20301182938401589598086513)
                ·
                  refine ⟨15225887203801192198564885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20301182938401589598086513 15225887203801192198564885)
                  ·
                    refine ⟨713713462678180884307729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15225887203801192198564885 713713462678180884307729)
                    ·
                      rfl

theorem cell23_4169856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_4169856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169856 prefixEnd_4169856 := by exact prefixLift 4169856
  have htrace : WordTrace (prefixWord ++ tailWord_4169856) baseStart_4169856 baseEnd_4169856 := by
    simpa [prefixWord, tailWord_4169856, baseEnd_4169856] using wordTrace_append hprefix tailTrace_4169856
  have hstable : (prefixWord ++ tailWord_4169856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169856).length < 2 ^ (prefixWord ++ tailWord_4169856).sum := by decide
  have hdescent : baseEnd_4169856 < baseStart_4169856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169901 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4169901 : Nat := 118140960795 + 4169901 * 2 ^ 59
def prefixEnd_4169901 : Nat := 4983230072969 + 3 ^ 40 * 4169901 * 2
def baseEnd_4169901 : Nat := 2141163494663994976860481

theorem tailTrace_4169901 : CollatzResearch.WordTrace tailWord_4169901 prefixEnd_4169901 2141163494663994976860481 := by
  unfold tailWord_4169901
  simp only [CollatzResearch.WordTrace]
  refine ⟨152088784066168314237765557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101392522710778876158510371 152088784066168314237765557)
  ·
    refine ⟨14258323506203279459790521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152088784066168314237765557 14258323506203279459790521)
    ·
      refine ⟨10693742629652459594842891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14258323506203279459790521 10693742629652459594842891)
      ·
        refine ⟨16040613944478689392264337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10693742629652459594842891 16040613944478689392264337)
        ·
          refine ⟨12030460458359017044198253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040613944478689392264337 12030460458359017044198253)
          ·
            refine ⟨4511422671884631391574345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12030460458359017044198253 4511422671884631391574345)
            ·
              refine ⟨3383567003913473543680759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4511422671884631391574345 3383567003913473543680759)
              ·
                refine ⟨5075350505870210315521139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383567003913473543680759 5075350505870210315521139)
                ·
                  refine ⟨7613025758805315473281709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075350505870210315521139 7613025758805315473281709)
                  ·
                    refine ⟨2854884659551993302480641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7613025758805315473281709 2854884659551993302480641)
                    ·
                      refine ⟨2141163494663994976860481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854884659551993302480641 2141163494663994976860481)
                      ·
                        rfl

theorem cell23_4169901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4169901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169901 prefixEnd_4169901 := by exact prefixLift 4169901
  have htrace : WordTrace (prefixWord ++ tailWord_4169901) baseStart_4169901 baseEnd_4169901 := by
    simpa [prefixWord, tailWord_4169901, baseEnd_4169901] using wordTrace_append hprefix tailTrace_4169901
  have hstable : (prefixWord ++ tailWord_4169901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169901).length < 2 ^ (prefixWord ++ tailWord_4169901).sum := by decide
  have hdescent : baseEnd_4169901 < baseStart_4169901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169913 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4169913 : Nat := 118140960795 + 4169913 * 2 ^ 59
def prefixEnd_4169913 : Nat := 4983230072969 + 3 ^ 40 * 4169913 * 2
def baseEnd_4169913 : Nat := 2141169656431848929910425

theorem tailTrace_4169913 : CollatzResearch.WordTrace tailWord_4169913 prefixEnd_4169913 2141169656431848929910425 := by
  unfold tailWord_4169913
  simp only [CollatzResearch.WordTrace]
  refine ⟨152089221742124840287202393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101392814494749893524801595 152089221742124840287202393)
  ·
    refine ⟨114066916306593630215401795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152089221742124840287202393 114066916306593630215401795)
    ·
      refine ⟨171100374459890445323102693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114066916306593630215401795 171100374459890445323102693)
      ·
        refine ⟨32081320211229458498081755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171100374459890445323102693 32081320211229458498081755)
        ·
          refine ⟨48121980316844187747122633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32081320211229458498081755 48121980316844187747122633)
          ·
            refine ⟨36091485237633140810341975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48121980316844187747122633 36091485237633140810341975)
            ·
              refine ⟨54137227856449711215512963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36091485237633140810341975 54137227856449711215512963)
              ·
                refine ⟨81205841784674566823269445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54137227856449711215512963 81205841784674566823269445)
                ·
                  refine ⟨15226095334626481279363021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81205841784674566823269445 15226095334626481279363021)
                  ·
                    refine ⟨5709785750484930479761133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15226095334626481279363021 5709785750484930479761133)
                    ·
                      refine ⟨2141169656431848929910425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709785750484930479761133 2141169656431848929910425)
                      ·
                        rfl

theorem cell23_4169913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4169913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169913 prefixEnd_4169913 := by exact prefixLift 4169913
  have htrace : WordTrace (prefixWord ++ tailWord_4169913) baseStart_4169913 baseEnd_4169913 := by
    simpa [prefixWord, tailWord_4169913, baseEnd_4169913] using wordTrace_append hprefix tailTrace_4169913
  have hstable : (prefixWord ++ tailWord_4169913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169913).length < 2 ^ (prefixWord ++ tailWord_4169913).sum := by decide
  have hdescent : baseEnd_4169913 < baseStart_4169913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169920 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 5]
def baseStart_4169920 : Nat := 118140960795 + 4169920 * 2 ^ 59
def prefixEnd_4169920 : Nat := 4983230072969 + 3 ^ 40 * 4169920 * 2
def baseEnd_4169920 : Nat := 237908138977381155835877

theorem tailTrace_4169920 : CollatzResearch.WordTrace tailWord_4169920 prefixEnd_4169920 237908138977381155835877 := by
  unfold tailWord_4169920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76044738526549740241353607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101392984702066320321804809 76044738526549740241353607)
  ·
    refine ⟨114067107789824610362030411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76044738526549740241353607 114067107789824610362030411)
    ·
      refine ⟨171100661684736915543045617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114067107789824610362030411 171100661684736915543045617)
      ·
        refine ⟨128325496263552686657284213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171100661684736915543045617 128325496263552686657284213)
        ·
          refine ⟨12030515274708064374120395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128325496263552686657284213 12030515274708064374120395)
          ·
            refine ⟨18045772912062096561180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030515274708064374120395 18045772912062096561180593)
            ·
              refine ⟨13534329684046572420885445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18045772912062096561180593 13534329684046572420885445)
              ·
                refine ⟨2537686815758732328916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13534329684046572420885445 2537686815758732328916021)
                ·
                  refine ⟨237908138977381155835877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537686815758732328916021 237908138977381155835877)
                  ·
                    rfl

theorem cell23_4169920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 5].length) (baseStart_4169920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169920 prefixEnd_4169920 := by exact prefixLift 4169920
  have htrace : WordTrace (prefixWord ++ tailWord_4169920) baseStart_4169920 baseEnd_4169920 := by
    simpa [prefixWord, tailWord_4169920, baseEnd_4169920] using wordTrace_append hprefix tailTrace_4169920
  have hstable : (prefixWord ++ tailWord_4169920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169920).length < 2 ^ (prefixWord ++ tailWord_4169920).sum := by decide
  have hdescent : baseEnd_4169920 < baseStart_4169920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169953 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4169953 : Nat := 118140960795 + 4169953 * 2 ^ 59
def prefixEnd_4169953 : Nat := 4983230072969 + 3 ^ 40 * 4169953 * 2
def baseEnd_4169953 : Nat := 2141190195658028773410241

theorem tailTrace_4169953 : CollatzResearch.WordTrace tailWord_4169953 prefixEnd_4169953 2141190195658028773410241 := by
  unfold tailWord_4169953
  simp only [CollatzResearch.WordTrace]
  refine ⟨152090680661979927118658513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101393787107986618079105675 152090680661979927118658513)
  ·
    refine ⟨114068010496484945338993885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152090680661979927118658513 114068010496484945338993885)
    ·
      refine ⟨42775503936181854502122707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114068010496484945338993885 42775503936181854502122707)
      ·
        refine ⟨64163255904272781753184061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42775503936181854502122707 64163255904272781753184061)
        ·
          refine ⟨24061220964102293157444023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64163255904272781753184061 24061220964102293157444023)
          ·
            refine ⟨36091831446153439736166035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061220964102293157444023 36091831446153439736166035)
            ·
              refine ⟨54137747169230159604249053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36091831446153439736166035 54137747169230159604249053)
              ·
                refine ⟨20301655188461309851593395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54137747169230159604249053 20301655188461309851593395)
                ·
                  refine ⟨30452482782691964777390093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20301655188461309851593395 30452482782691964777390093)
                  ·
                    refine ⟨11419681043509486791521285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30452482782691964777390093 11419681043509486791521285)
                    ·
                      refine ⟨2141190195658028773410241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11419681043509486791521285 2141190195658028773410241)
                      ·
                        rfl

theorem cell23_4169953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4169953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169953 prefixEnd_4169953 := by exact prefixLift 4169953
  have htrace : WordTrace (prefixWord ++ tailWord_4169953) baseStart_4169953 baseEnd_4169953 := by
    simpa [prefixWord, tailWord_4169953, baseEnd_4169953] using wordTrace_append hprefix tailTrace_4169953
  have hstable : (prefixWord ++ tailWord_4169953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169953).length < 2 ^ (prefixWord ++ tailWord_4169953).sum := by decide
  have hdescent : baseEnd_4169953 < baseStart_4169953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4169970 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4169970 : Nat := 118140960795 + 4169970 * 2 ^ 59
def prefixEnd_4169970 : Nat := 4983230072969 + 3 ^ 40 * 4169970 * 2
def baseEnd_4169970 : Nat := 2141198924829155206897663

theorem tailTrace_4169970 : CollatzResearch.WordTrace tailWord_4169970 prefixEnd_4169970 2141198924829155206897663 := by
  unfold tailWord_4169970
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022825175729584755506841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101394200468612226014684909 38022825175729584755506841)
  ·
    refine ⟨28517118881797188566630131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38022825175729584755506841 28517118881797188566630131)
    ·
      refine ⟨42775678322695782849945197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28517118881797188566630131 42775678322695782849945197)
      ·
        refine ⟨16040879371010918568729449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42775678322695782849945197 16040879371010918568729449)
        ·
          refine ⟨12030659528258188926547087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16040879371010918568729449 12030659528258188926547087)
          ·
            refine ⟨18045989292387283389820631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12030659528258188926547087 18045989292387283389820631)
            ·
              refine ⟨27068983938580925084730947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18045989292387283389820631 27068983938580925084730947)
              ·
                refine ⟨40603475907871387627096421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27068983938580925084730947 40603475907871387627096421)
                ·
                  refine ⟨7613151732725885180080579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40603475907871387627096421 7613151732725885180080579)
                  ·
                    refine ⟨11419727599088827770120869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613151732725885180080579 11419727599088827770120869)
                    ·
                      refine ⟨2141198924829155206897663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11419727599088827770120869 2141198924829155206897663)
                      ·
                        rfl

theorem cell23_4169970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4169970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4169970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4169970 prefixEnd_4169970 := by exact prefixLift 4169970
  have htrace : WordTrace (prefixWord ++ tailWord_4169970) baseStart_4169970 baseEnd_4169970 := by
    simpa [prefixWord, tailWord_4169970, baseEnd_4169970] using wordTrace_append hprefix tailTrace_4169970
  have hstable : (prefixWord ++ tailWord_4169970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4169970).length < 2 ^ (prefixWord ++ tailWord_4169970).sum := by decide
  have hdescent : baseEnd_4169970 < baseStart_4169970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4169970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170003 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3]
def baseStart_4170003 : Nat := 118140960795 + 4170003 * 2 ^ 59
def prefixEnd_4170003 : Nat := 4983230072969 + 3 ^ 40 * 4170003 * 2
def baseEnd_4170003 : Nat := 2141215869690753577785011

theorem tailTrace_4170003 : CollatzResearch.WordTrace tailWord_4170003 prefixEnd_4170003 2141215869690753577785011 := by
  unfold tailWord_4170003
  simp only [CollatzResearch.WordTrace]
  refine ⟨152092504311798785657978663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101395002874532523771985775 152092504311798785657978663)
  ·
    refine ⟨228138756467698178486967995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152092504311798785657978663 228138756467698178486967995)
    ·
      refine ⟨342208134701547267730451993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228138756467698178486967995 342208134701547267730451993)
      ·
        refine ⟨256656101026160450797838995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342208134701547267730451993 256656101026160450797838995)
        ·
          refine ⟨384984151539240676196758493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256656101026160450797838995 384984151539240676196758493)
          ·
            refine ⟨144369056827215253573784435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384984151539240676196758493 144369056827215253573784435)
            ·
              refine ⟨216553585240822880360676653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144369056827215253573784435 216553585240822880360676653)
              ·
                refine ⟨81207594465308580135253745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216553585240822880360676653 81207594465308580135253745)
                ·
                  refine ⟨60905695848981435101440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81207594465308580135253745 60905695848981435101440309)
                  ·
                    refine ⟨5709908985842009540760029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60905695848981435101440309 5709908985842009540760029)
                    ·
                      refine ⟨2141215869690753577785011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709908985842009540760029 2141215869690753577785011)
                      ·
                        rfl

theorem cell23_4170003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 3].length) (baseStart_4170003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170003 prefixEnd_4170003 := by exact prefixLift 4170003
  have htrace : WordTrace (prefixWord ++ tailWord_4170003) baseStart_4170003 baseEnd_4170003 := by
    simpa [prefixWord, tailWord_4170003, baseEnd_4170003] using wordTrace_append hprefix tailTrace_4170003
  have hstable : (prefixWord ++ tailWord_4170003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170003).length < 2 ^ (prefixWord ++ tailWord_4170003).sum := by decide
  have hdescent : baseEnd_4170003 < baseStart_4170003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170007 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4170007 : Nat := 118140960795 + 4170007 * 2 ^ 59
def prefixEnd_4170007 : Nat := 4983230072969 + 3 ^ 40 * 4170007 * 2
def baseEnd_4170007 : Nat := 2141217923613371562134993

theorem tailTrace_4170007 : CollatzResearch.WordTrace tailWord_4170007 prefixEnd_4170007 2141217923613371562134993 := by
  unfold tailWord_4170007
  simp only [CollatzResearch.WordTrace]
  refine ⟨152092650203784294341124275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101395100135856196227416183 152092650203784294341124275)
  ·
    refine ⟨228138975305676441511686413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152092650203784294341124275 228138975305676441511686413)
    ·
      refine ⟨85552115739628665566882405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228138975305676441511686413 85552115739628665566882405)
      ·
        refine ⟨16041021701180374793790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85552115739628665566882405 16041021701180374793790451)
        ·
          refine ⟨24061532551770562190685677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041021701180374793790451 24061532551770562190685677)
          ·
            refine ⟨9023074706913960821507129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24061532551770562190685677 9023074706913960821507129)
            ·
              refine ⟨6767306030185470616130347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023074706913960821507129 6767306030185470616130347)
              ·
                refine ⟨10150959045278205924195521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767306030185470616130347 10150959045278205924195521)
                ·
                  refine ⟨7613219283958654443146641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10150959045278205924195521 7613219283958654443146641)
                  ·
                    refine ⟨5709914462968990832359981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7613219283958654443146641 5709914462968990832359981)
                    ·
                      refine ⟨2141217923613371562134993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709914462968990832359981 2141217923613371562134993)
                      ·
                        rfl

theorem cell23_4170007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4170007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170007 prefixEnd_4170007 := by exact prefixLift 4170007
  have htrace : WordTrace (prefixWord ++ tailWord_4170007) baseStart_4170007 baseEnd_4170007 := by
    simpa [prefixWord, tailWord_4170007, baseEnd_4170007] using wordTrace_append hprefix tailTrace_4170007
  have hstable : (prefixWord ++ tailWord_4170007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170007).length < 2 ^ (prefixWord ++ tailWord_4170007).sum := by decide
  have hdescent : baseEnd_4170007 < baseStart_4170007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170037 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_4170037 : Nat := 118140960795 + 4170037 * 2 ^ 59
def prefixEnd_4170037 : Nat := 4983230072969 + 3 ^ 40 * 4170037 * 2
def baseEnd_4170037 : Nat := 2141233328033006444759855

theorem tailTrace_4170037 : CollatzResearch.WordTrace tailWord_4170037 prefixEnd_4170037 2141233328033006444759855 := by
  unfold tailWord_4170037
  simp only [CollatzResearch.WordTrace]
  refine ⟨152093744393675609464716365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101395829595783739643144243 152093744393675609464716365)
  ·
    refine ⟨57035154147628353549268637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152093744393675609464716365 57035154147628353549268637)
    ·
      refine ⟨21388182805360632580975739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57035154147628353549268637 21388182805360632580975739)
      ·
        refine ⟨32082274208040948871463609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21388182805360632580975739 32082274208040948871463609)
        ·
          refine ⟨24061705656030711653597707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32082274208040948871463609 24061705656030711653597707)
          ·
            refine ⟨36092558484046067480396561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061705656030711653597707 36092558484046067480396561)
            ·
              refine ⟨27069418863034550610297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36092558484046067480396561 27069418863034550610297421)
              ·
                refine ⟨10151032073637956478861533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27069418863034550610297421 10151032073637956478861533)
                ·
                  refine ⟨3806637027614233679573075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10151032073637956478861533 3806637027614233679573075)
                  ·
                    refine ⟨5709955541421350519359613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806637027614233679573075 5709955541421350519359613)
                    ·
                      refine ⟨2141233328033006444759855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5709955541421350519359613 2141233328033006444759855)
                      ·
                        rfl

theorem cell23_4170037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_4170037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170037 prefixEnd_4170037 := by exact prefixLift 4170037
  have htrace : WordTrace (prefixWord ++ tailWord_4170037) baseStart_4170037 baseEnd_4170037 := by
    simpa [prefixWord, tailWord_4170037, baseEnd_4170037] using wordTrace_append hprefix tailTrace_4170037
  have hstable : (prefixWord ++ tailWord_4170037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170037).length < 2 ^ (prefixWord ++ tailWord_4170037).sum := by decide
  have hdescent : baseEnd_4170037 < baseStart_4170037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170060 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4170060 : Nat := 118140960795 + 4170060 * 2 ^ 59
def prefixEnd_4170060 : Nat := 4983230072969 + 3 ^ 40 * 4170060 * 2
def baseEnd_4170060 : Nat := 2141245138088059854772249

theorem tailTrace_4170060 : CollatzResearch.WordTrace tailWord_4170060 prefixEnd_4170060 2141245138088059854772249 := by
  unfold tailWord_4170060
  simp only [CollatzResearch.WordTrace]
  refine ⟨76047291636296142196401817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101396388848394856261869089 76047291636296142196401817)
  ·
    refine ⟨57035468727222106647301363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76047291636296142196401817 57035468727222106647301363)
    ·
      refine ⟨85553203090833159970952045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57035468727222106647301363 85553203090833159970952045)
      ·
        refine ⟨32082451159062434989107017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85553203090833159970952045 32082451159062434989107017)
        ·
          refine ⟨24061838369296826241830263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32082451159062434989107017 24061838369296826241830263)
          ·
            refine ⟨36092757553945239362745395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061838369296826241830263 36092757553945239362745395)
            ·
              refine ⟨54139136330917859044118093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36092757553945239362745395 54139136330917859044118093)
              ·
                refine ⟨20302176124094197141544285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54139136330917859044118093 20302176124094197141544285)
                ·
                  refine ⟨7613316046535323928079107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20302176124094197141544285 7613316046535323928079107)
                  ·
                    refine ⟨11419974069802985892118661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613316046535323928079107 11419974069802985892118661)
                    ·
                      refine ⟨2141245138088059854772249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11419974069802985892118661 2141245138088059854772249)
                      ·
                        rfl

theorem cell23_4170060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4170060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170060 prefixEnd_4170060 := by exact prefixLift 4170060
  have htrace : WordTrace (prefixWord ++ tailWord_4170060) baseStart_4170060 baseEnd_4170060 := by
    simpa [prefixWord, tailWord_4170060, baseEnd_4170060] using wordTrace_append hprefix tailTrace_4170060
  have hstable : (prefixWord ++ tailWord_4170060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170060).length < 2 ^ (prefixWord ++ tailWord_4170060).sum := by decide
  have hdescent : baseEnd_4170060 < baseStart_4170060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_4170063 : Nat := 118140960795 + 4170063 * 2 ^ 59
def prefixEnd_4170063 : Nat := 4983230072969 + 3 ^ 40 * 4170063 * 2
def baseEnd_4170063 : Nat := 2141246678530023343034735

theorem tailTrace_4170063 : CollatzResearch.WordTrace tailWord_4170063 prefixEnd_4170063 2141246678530023343034735 := by
  unfold tailWord_4170063
  simp only [CollatzResearch.WordTrace]
  refine ⟨152094692691581415905162843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101396461794387610603441895 152094692691581415905162843)
  ·
    refine ⟨228142039037372123857744265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152094692691581415905162843 228142039037372123857744265)
    ·
      refine ⟨171106529278029092893308199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228142039037372123857744265 171106529278029092893308199)
      ·
        refine ⟨256659793917043639339962299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171106529278029092893308199 256659793917043639339962299)
        ·
          refine ⟨384989690875565459009943449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256659793917043639339962299 384989690875565459009943449)
          ·
            refine ⟨288742268156674094257457587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384989690875565459009943449 288742268156674094257457587)
            ·
              refine ⟨433113402235011141386186381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288742268156674094257457587 433113402235011141386186381)
              ·
                refine ⟨162417525838129178019819893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433113402235011141386186381 162417525838129178019819893)
                ·
                  refine ⟨15226643047324610439358115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162417525838129178019819893 15226643047324610439358115)
                  ·
                    refine ⟨22839964570986915659037173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15226643047324610439358115 22839964570986915659037173)
                    ·
                      refine ⟨2141246678530023343034735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22839964570986915659037173 2141246678530023343034735)
                      ·
                        rfl

theorem cell23_4170063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_4170063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170063 prefixEnd_4170063 := by exact prefixLift 4170063
  have htrace : WordTrace (prefixWord ++ tailWord_4170063) baseStart_4170063 baseEnd_4170063 := by
    simpa [prefixWord, tailWord_4170063, baseEnd_4170063] using wordTrace_append hprefix tailTrace_4170063
  have hstable : (prefixWord ++ tailWord_4170063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170063).length < 2 ^ (prefixWord ++ tailWord_4170063).sum := by decide
  have hdescent : baseEnd_4170063 < baseStart_4170063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170064 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2]
def baseStart_4170064 : Nat := 118140960795 + 4170064 * 2 ^ 59
def prefixEnd_4170064 : Nat := 4983230072969 + 3 ^ 40 * 4170064 * 2
def baseEnd_4170064 : Nat := 2141247192010677839122231

theorem tailTrace_4170064 : CollatzResearch.WordTrace tailWord_4170064 prefixEnd_4170064 2141247192010677839122231 := by
  unfold tailWord_4170064
  simp only [CollatzResearch.WordTrace]
  refine ⟨76047364582288896537974623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101396486109718528717299497 76047364582288896537974623)
  ·
    refine ⟨114071046873433344806961935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76047364582288896537974623 114071046873433344806961935)
    ·
      refine ⟨171106570310150017210442903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114071046873433344806961935 171106570310150017210442903)
      ·
        refine ⟨256659855465225025815664355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171106570310150017210442903 256659855465225025815664355)
        ·
          refine ⟨384989783197837538723496533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256659855465225025815664355 384989783197837538723496533)
          ·
            refine ⟨4511599021849658656915975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 384989783197837538723496533 4511599021849658656915975)
            ·
              refine ⟨6767398532774487985373963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511599021849658656915975 6767398532774487985373963)
              ·
                refine ⟨10151097799161731978060945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767398532774487985373963 10151097799161731978060945)
                ·
                  refine ⟨7613323349371298983545709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10151097799161731978060945 7613323349371298983545709)
                  ·
                    refine ⟨2854996256014237118829641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7613323349371298983545709 2854996256014237118829641)
                    ·
                      refine ⟨2141247192010677839122231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2854996256014237118829641 2141247192010677839122231)
                      ·
                        rfl

theorem cell23_4170064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 3, 2].length) (baseStart_4170064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170064 prefixEnd_4170064 := by exact prefixLift 4170064
  have htrace : WordTrace (prefixWord ++ tailWord_4170064) baseStart_4170064 baseEnd_4170064 := by
    simpa [prefixWord, tailWord_4170064, baseEnd_4170064] using wordTrace_append hprefix tailTrace_4170064
  have hstable : (prefixWord ++ tailWord_4170064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170064).length < 2 ^ (prefixWord ++ tailWord_4170064).sum := by decide
  have hdescent : baseEnd_4170064 < baseStart_4170064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170073 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_4170073 : Nat := 118140960795 + 4170073 * 2 ^ 59
def prefixEnd_4170073 : Nat := 4983230072969 + 3 ^ 40 * 4170073 * 2
def baseEnd_4170073 : Nat := 2141251813336568303909689

theorem tailTrace_4170073 : CollatzResearch.WordTrace tailWord_4170073 prefixEnd_4170073 2141251813336568303909689 := by
  unfold tailWord_4170073
  simp only [CollatzResearch.WordTrace]
  refine ⟨152095057421545187613026873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101396704947696791742017915 152095057421545187613026873)
  ·
    refine ⟨114071293066158890709770155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152095057421545187613026873 114071293066158890709770155)
    ·
      refine ⟨171106939599238336064655233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114071293066158890709770155 171106939599238336064655233)
      ·
        refine ⟨128330204699428752048491425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171106939599238336064655233 128330204699428752048491425)
        ·
          refine ⟨96247653524571564036368569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128330204699428752048491425 96247653524571564036368569)
          ·
            refine ⟨72185740143428673027276427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96247653524571564036368569 72185740143428673027276427)
            ·
              refine ⟨108278610215143009540914641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72185740143428673027276427 108278610215143009540914641)
              ·
                refine ⟨81208957661357257155685981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108278610215143009540914641 81208957661357257155685981)
                ·
                  refine ⟨30453359123008971433382243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81208957661357257155685981 30453359123008971433382243)
                  ·
                    refine ⟨45680038684513457150073365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30453359123008971433382243 45680038684513457150073365)
                    ·
                      refine ⟨2141251813336568303909689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45680038684513457150073365 2141251813336568303909689)
                      ·
                        rfl

theorem cell23_4170073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_4170073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170073 prefixEnd_4170073 := by exact prefixLift 4170073
  have htrace : WordTrace (prefixWord ++ tailWord_4170073) baseStart_4170073 baseEnd_4170073 := by
    simpa [prefixWord, tailWord_4170073, baseEnd_4170073] using wordTrace_append hprefix tailTrace_4170073
  have hstable : (prefixWord ++ tailWord_4170073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170073).length < 2 ^ (prefixWord ++ tailWord_4170073).sum := by decide
  have hdescent : baseEnd_4170073 < baseStart_4170073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170083 : List Nat := [1, 1, 1, 5, 2, 1, 12]
def baseStart_4170083 : Nat := 118140960795 + 4170083 * 2 ^ 59
def prefixEnd_4170083 : Nat := 4983230072969 + 3 ^ 40 * 4170083 * 2
def baseEnd_4170083 : Nat := 26435270964729793392403

theorem tailTrace_4170083 : CollatzResearch.WordTrace tailWord_4170083 prefixEnd_4170083 26435270964729793392403 := by
  unfold tailWord_4170083
  simp only [CollatzResearch.WordTrace]
  refine ⟨152095422151508959320890903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101396948101005972880593935 152095422151508959320890903)
  ·
    refine ⟨228143133227263438981336355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152095422151508959320890903 228143133227263438981336355)
    ·
      refine ⟨342214699840895158472004533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228143133227263438981336355 342214699840895158472004533)
      ·
        refine ⟨32082628110083921106750425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 342214699840895158472004533 32082628110083921106750425)
        ·
          refine ⟨24061971082562940830062819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32082628110083921106750425 24061971082562940830062819)
          ·
            refine ⟨36092956623844411245094229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24061971082562940830062819 36092956623844411245094229)
            ·
              refine ⟨26435270964729793392403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36092956623844411245094229 26435270964729793392403)
              ·
                rfl

theorem cell23_4170083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 12].length) (baseStart_4170083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170083 prefixEnd_4170083 := by exact prefixLift 4170083
  have htrace : WordTrace (prefixWord ++ tailWord_4170083) baseStart_4170083 baseEnd_4170083 := by
    simpa [prefixWord, tailWord_4170083, baseEnd_4170083] using wordTrace_append hprefix tailTrace_4170083
  have hstable : (prefixWord ++ tailWord_4170083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170083).length < 2 ^ (prefixWord ++ tailWord_4170083).sum := by decide
  have hdescent : baseEnd_4170083 < baseStart_4170083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170087 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 4, 4]
def baseStart_4170087 : Nat := 118140960795 + 4170087 * 2 ^ 59
def prefixEnd_4170087 : Nat := 4983230072969 + 3 ^ 40 * 4170087 * 2
def baseEnd_4170087 : Nat := 713753000688577083044875

theorem tailTrace_4170087 : CollatzResearch.WordTrace tailWord_4170087 prefixEnd_4170087 713753000688577083044875 := by
  unfold tailWord_4170087
  simp only [CollatzResearch.WordTrace]
  refine ⟨152095568043494468004036515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101397045362329645336024343 152095568043494468004036515)
  ·
    refine ⟨228143352065241702006054773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152095568043494468004036515 228143352065241702006054773)
    ·
      refine ⟨21388439256116409563067635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228143352065241702006054773 21388439256116409563067635)
      ·
        refine ⟨32082658884174614344601453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21388439256116409563067635 32082658884174614344601453)
        ·
          refine ⟨12030997081565480379225545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32082658884174614344601453 12030997081565480379225545)
          ·
            refine ⟨9023247811174110284419159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12030997081565480379225545 9023247811174110284419159)
            ·
              refine ⟨13534871716761165426628739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023247811174110284419159 13534871716761165426628739)
              ·
                refine ⟨20302307575141748139943109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13534871716761165426628739 20302307575141748139943109)
                ·
                  refine ⟨3806682670339077776239333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20302307575141748139943109 3806682670339077776239333)
                  ·
                    refine ⟨713753000688577083044875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3806682670339077776239333 713753000688577083044875)
                    ·
                      rfl

theorem cell23_4170087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_4170087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170087 prefixEnd_4170087 := by exact prefixLift 4170087
  have htrace : WordTrace (prefixWord ++ tailWord_4170087) baseStart_4170087 baseEnd_4170087 := by
    simpa [prefixWord, tailWord_4170087, baseEnd_4170087] using wordTrace_append hprefix tailTrace_4170087
  have hstable : (prefixWord ++ tailWord_4170087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170087).length < 2 ^ (prefixWord ++ tailWord_4170087).sum := by decide
  have hdescent : baseEnd_4170087 < baseStart_4170087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4170103 : Nat := 118140960795 + 4170103 * 2 ^ 59
def prefixEnd_4170103 : Nat := 4983230072969 + 3 ^ 40 * 4170103 * 2
def baseEnd_4170103 : Nat := 2141267217756203186534551

theorem tailTrace_4170103 : CollatzResearch.WordTrace tailWord_4170103 prefixEnd_4170103 2141267217756203186534551 := by
  unfold tailWord_4170103
  simp only [CollatzResearch.WordTrace]
  refine ⟨152096151611436502736618963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101397434407624335157745975 152096151611436502736618963)
  ·
    refine ⟨228144227417154754104928445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152096151611436502736618963 228144227417154754104928445)
    ·
      refine ⟨85554085281433032789348167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228144227417154754104928445 85554085281433032789348167)
      ·
        refine ⟨128331127922149549184022251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85554085281433032789348167 128331127922149549184022251)
        ·
          refine ⟨192496691883224323776033377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128331127922149549184022251 192496691883224323776033377)
          ·
            refine ⟨144372518912418242832025033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192496691883224323776033377 144372518912418242832025033)
            ·
              refine ⟨108279389184313682124018775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144372518912418242832025033 108279389184313682124018775)
              ·
                refine ⟨162419083776470523186028163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108279389184313682124018775 162419083776470523186028163)
                ·
                  refine ⟨243628625664705784779042245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162419083776470523186028163 243628625664705784779042245)
                  ·
                    refine ⟨45680367312132334646070421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243628625664705784779042245 45680367312132334646070421)
                    ·
                      refine ⟨2141267217756203186534551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45680367312132334646070421 2141267217756203186534551)
                      ·
                        rfl

theorem cell23_4170103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4170103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170103 prefixEnd_4170103 := by exact prefixLift 4170103
  have htrace : WordTrace (prefixWord ++ tailWord_4170103) baseStart_4170103 baseEnd_4170103 := by
    simpa [prefixWord, tailWord_4170103, baseEnd_4170103] using wordTrace_append hprefix tailTrace_4170103
  have hstable : (prefixWord ++ tailWord_4170103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170103).length < 2 ^ (prefixWord ++ tailWord_4170103).sum := by decide
  have hdescent : baseEnd_4170103 < baseStart_4170103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170107 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 4]
def baseStart_4170107 : Nat := 118140960795 + 4170107 * 2 ^ 59
def prefixEnd_4170107 : Nat := 4983230072969 + 3 ^ 40 * 4170107 * 2
def baseEnd_4170107 : Nat := 2141269271678821170884533

theorem tailTrace_4170107 : CollatzResearch.WordTrace tailWord_4170107 prefixEnd_4170107 2141269271678821170884533 := by
  unfold tailWord_4170107
  simp only [CollatzResearch.WordTrace]
  refine ⟨152096297503422011419764575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101397531668948007613176383 152096297503422011419764575)
  ·
    refine ⟨228144446255133017129646863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152096297503422011419764575 228144446255133017129646863)
    ·
      refine ⟨342216669382699525694470295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228144446255133017129646863 342216669382699525694470295)
      ·
        refine ⟨513325004074049288541705443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342216669382699525694470295 513325004074049288541705443)
        ·
          refine ⟨769987506111073932812558165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513325004074049288541705443 769987506111073932812558165)
          ·
            refine ⟨4511645543619573825073583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 769987506111073932812558165 4511645543619573825073583)
            ·
              refine ⟨6767468315429360737610375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511645543619573825073583 6767468315429360737610375)
              ·
                refine ⟨10151202473144041106415563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767468315429360737610375 10151202473144041106415563)
                ·
                  refine ⟨15226803709716061659623345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151202473144041106415563 15226803709716061659623345)
                  ·
                    refine ⟨11420102782287046244717509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15226803709716061659623345 11420102782287046244717509)
                    ·
                      refine ⟨2141269271678821170884533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11420102782287046244717509 2141269271678821170884533)
                      ·
                        rfl

theorem cell23_4170107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 4].length) (baseStart_4170107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170107 prefixEnd_4170107 := by exact prefixLift 4170107
  have htrace : WordTrace (prefixWord ++ tailWord_4170107) baseStart_4170107 baseEnd_4170107 := by
    simpa [prefixWord, tailWord_4170107, baseEnd_4170107] using wordTrace_append hprefix tailTrace_4170107
  have hstable : (prefixWord ++ tailWord_4170107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170107).length < 2 ^ (prefixWord ++ tailWord_4170107).sum := by decide
  have hdescent : baseEnd_4170107 < baseStart_4170107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170145 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4170145 : Nat := 118140960795 + 4170145 * 2 ^ 59
def prefixEnd_4170145 : Nat := 4983230072969 + 3 ^ 40 * 4170145 * 2
def baseEnd_4170145 : Nat := 2141288783943692022209359

theorem tailTrace_4170145 : CollatzResearch.WordTrace tailWord_4170145 prefixEnd_4170145 2141288783943692022209359 := by
  unfold tailWord_4170145
  simp only [CollatzResearch.WordTrace]
  refine ⟨152097683477284343909647889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101398455651522895939765259 152097683477284343909647889)
  ·
    refine ⟨114073262607963257932235917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152097683477284343909647889 114073262607963257932235917)
    ·
      refine ⟨42777473477986221724588469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114073262607963257932235917 42777473477986221724588469)
      ·
        refine ⟨4010388138561208286680169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42777473477986221724588469 4010388138561208286680169)
        ·
          refine ⟨3007791103920906215010127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010388138561208286680169 3007791103920906215010127)
          ·
            refine ⟨4511686655881359322515191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007791103920906215010127 4511686655881359322515191)
            ·
              refine ⟨6767529983822038983772787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511686655881359322515191 6767529983822038983772787)
              ·
                refine ⟨10151294975733058475659181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6767529983822038983772787 10151294975733058475659181)
                ·
                  refine ⟨3806735615899896928372193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10151294975733058475659181 3806735615899896928372193)
                  ·
                    refine ⟨2855051711924922696279145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3806735615899896928372193 2855051711924922696279145)
                    ·
                      refine ⟨2141288783943692022209359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855051711924922696279145 2141288783943692022209359)
                      ·
                        rfl

theorem cell23_4170145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4170145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170145 prefixEnd_4170145 := by exact prefixLift 4170145
  have htrace : WordTrace (prefixWord ++ tailWord_4170145) baseStart_4170145 baseEnd_4170145 := by
    simpa [prefixWord, tailWord_4170145, baseEnd_4170145] using wordTrace_append hprefix tailTrace_4170145
  have hstable : (prefixWord ++ tailWord_4170145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170145).length < 2 ^ (prefixWord ++ tailWord_4170145).sum := by decide
  have hdescent : baseEnd_4170145 < baseStart_4170145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170161 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4170161 : Nat := 118140960795 + 4170161 * 2 ^ 59
def prefixEnd_4170161 : Nat := 4983230072969 + 3 ^ 40 * 4170161 * 2
def baseEnd_4170161 : Nat := 2141296999634163959609285

theorem tailTrace_4170161 : CollatzResearch.WordTrace tailWord_4170161 prefixEnd_4170161 2141296999634163959609285 := by
  unfold tailWord_4170161
  simp only [CollatzResearch.WordTrace]
  refine ⟨152098267045226378642230337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101398844696817585761486891 152098267045226378642230337)
  ·
    refine ⟨114073700283919783981672753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152098267045226378642230337 114073700283919783981672753)
    ·
      refine ⟨85555275212939837986254565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114073700283919783981672753 85555275212939837986254565)
      ·
        refine ⟨16041614102426219622422731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85555275212939837986254565 16041614102426219622422731)
        ·
          refine ⟨24062421153639329433634097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16041614102426219622422731 24062421153639329433634097)
          ·
            refine ⟨18046815865229497075225573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24062421153639329433634097 18046815865229497075225573)
            ·
              refine ⟨3383777974730530701604795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18046815865229497075225573 3383777974730530701604795)
              ·
                refine ⟨5075666962095796052407193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383777974730530701604795 5075666962095796052407193)
                ·
                  refine ⟨3806750221571847039305395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075666962095796052407193 3806750221571847039305395)
                  ·
                    refine ⟨5710125332357770558958093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806750221571847039305395 5710125332357770558958093)
                    ·
                      refine ⟨2141296999634163959609285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710125332357770558958093 2141296999634163959609285)
                      ·
                        rfl

theorem cell23_4170161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4170161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170161 prefixEnd_4170161 := by exact prefixLift 4170161
  have htrace : WordTrace (prefixWord ++ tailWord_4170161) baseStart_4170161 baseEnd_4170161 := by
    simpa [prefixWord, tailWord_4170161, baseEnd_4170161] using wordTrace_append hprefix tailTrace_4170161
  have hstable : (prefixWord ++ tailWord_4170161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170161).length < 2 ^ (prefixWord ++ tailWord_4170161).sum := by decide
  have hdescent : baseEnd_4170161 < baseStart_4170161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170184 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_4170184 : Nat := 118140960795 + 4170184 * 2 ^ 59
def prefixEnd_4170184 : Nat := 4983230072969 + 3 ^ 40 * 4170184 * 2
def baseEnd_4170184 : Nat := 2141308809689217369621679

theorem tailTrace_4170184 : CollatzResearch.WordTrace tailWord_4170184 prefixEnd_4170184 2141308809689217369621679 := by
  unfold tailWord_4170184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76049552962071526785158803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101399403949428702380211737 76049552962071526785158803)
  ·
    refine ⟨114074329443107290177738205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76049552962071526785158803 114074329443107290177738205)
    ·
      refine ⟨42777873541165233816651827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114074329443107290177738205 42777873541165233816651827)
      ·
        refine ⟨64166810311747850724977741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42777873541165233816651827 64166810311747850724977741)
        ·
          refine ⟨24062553866905444021866653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64166810311747850724977741 24062553866905444021866653)
          ·
            refine ⟨9023457700089541508199995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24062553866905444021866653 9023457700089541508199995)
            ·
              refine ⟨13535186550134312262299993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023457700089541508199995 13535186550134312262299993)
              ·
                refine ⟨10151389912600734196724995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13535186550134312262299993 10151389912600734196724995)
                ·
                  refine ⟨15227084868901101295087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151389912600734196724995 15227084868901101295087493)
                  ·
                    refine ⟨2855078412918956492828905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15227084868901101295087493 2855078412918956492828905)
                    ·
                      refine ⟨2141308809689217369621679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855078412918956492828905 2141308809689217369621679)
                      ·
                        rfl

theorem cell23_4170184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_4170184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170184 prefixEnd_4170184 := by exact prefixLift 4170184
  have htrace : WordTrace (prefixWord ++ tailWord_4170184) baseStart_4170184 baseEnd_4170184 := by
    simpa [prefixWord, tailWord_4170184, baseEnd_4170184] using wordTrace_append hprefix tailTrace_4170184
  have hstable : (prefixWord ++ tailWord_4170184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170184).length < 2 ^ (prefixWord ++ tailWord_4170184).sum := by decide
  have hdescent : baseEnd_4170184 < baseStart_4170184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170188 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4170188 : Nat := 118140960795 + 4170188 * 2 ^ 59
def prefixEnd_4170188 : Nat := 4983230072969 + 3 ^ 40 * 4170188 * 2
def baseEnd_4170188 : Nat := 2141310863611835353971661

theorem tailTrace_4170188 : CollatzResearch.WordTrace tailWord_4170188 prefixEnd_4170188 2141310863611835353971661 := by
  unfold tailWord_4170188
  simp only [CollatzResearch.WordTrace]
  refine ⟨76049625908064281126731609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101399501210752374835642145 76049625908064281126731609)
  ·
    refine ⟨57037219431048210845048707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76049625908064281126731609 57037219431048210845048707)
    ·
      refine ⟨85555829146572316267573061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57037219431048210845048707 85555829146572316267573061)
      ·
        refine ⟨16041717964982309300169949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85555829146572316267573061 16041717964982309300169949)
        ·
          refine ⟨6015644236868365987563731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16041717964982309300169949 6015644236868365987563731)
          ·
            refine ⟨9023466355302548981345597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6015644236868365987563731 9023466355302548981345597)
            ·
              refine ⟨3383799883238455868004599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9023466355302548981345597 3383799883238455868004599)
              ·
                refine ⟨5075699824857683802006899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383799883238455868004599 5075699824857683802006899)
                ·
                  refine ⟨7613549737286525703010349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075699824857683802006899 7613549737286525703010349)
                  ·
                    refine ⟨2855081151482447138628881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7613549737286525703010349 2855081151482447138628881)
                    ·
                      refine ⟨2141310863611835353971661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855081151482447138628881 2141310863611835353971661)
                      ·
                        rfl

theorem cell23_4170188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4170188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170188 prefixEnd_4170188 := by exact prefixLift 4170188
  have htrace : WordTrace (prefixWord ++ tailWord_4170188) baseStart_4170188 baseEnd_4170188 := by
    simpa [prefixWord, tailWord_4170188, baseEnd_4170188] using wordTrace_append hprefix tailTrace_4170188
  have hstable : (prefixWord ++ tailWord_4170188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170188).length < 2 ^ (prefixWord ++ tailWord_4170188).sum := by decide
  have hdescent : baseEnd_4170188 < baseStart_4170188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170201 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 2, 2, 2]
def baseStart_4170201 : Nat := 118140960795 + 4170201 * 2 ^ 59
def prefixEnd_4170201 : Nat := 4983230072969 + 3 ^ 40 * 4170201 * 2
def baseEnd_4170201 : Nat := 2141317538860343803109101

theorem tailTrace_4170201 : CollatzResearch.WordTrace tailWord_4170201 prefixEnd_4170201 2141317538860343803109101 := by
  unfold tailWord_4170201
  simp only [CollatzResearch.WordTrace]
  refine ⟨152099725965081465473686457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101399817310054310315790971 152099725965081465473686457)
  ·
    refine ⟨114074794473811099105264843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152099725965081465473686457 114074794473811099105264843)
    ·
      refine ⟨171112191710716648657897265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114074794473811099105264843 171112191710716648657897265)
      ·
        refine ⟨128334143783037486493422949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171112191710716648657897265 128334143783037486493422949)
        ·
          refine ⟨24062651959319528717516803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128334143783037486493422949 24062651959319528717516803)
          ·
            refine ⟨36093977938979293076275205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24062651959319528717516803 36093977938979293076275205)
            ·
              refine ⟨6767620863558617451801601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36093977938979293076275205 6767620863558617451801601)
              ·
                refine ⟨5075715647668963088851201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6767620863558617451801601 5075715647668963088851201)
                ·
                  refine ⟨3806786735751722316638401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5075715647668963088851201 3806786735751722316638401)
                  ·
                    refine ⟨2855090051813791737478801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3806786735751722316638401 2855090051813791737478801)
                    ·
                      refine ⟨2141317538860343803109101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855090051813791737478801 2141317538860343803109101)
                      ·
                        rfl

theorem cell23_4170201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_4170201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170201 prefixEnd_4170201 := by exact prefixLift 4170201
  have htrace : WordTrace (prefixWord ++ tailWord_4170201) baseStart_4170201 baseEnd_4170201 := by
    simpa [prefixWord, tailWord_4170201, baseEnd_4170201] using wordTrace_append hprefix tailTrace_4170201
  have hstable : (prefixWord ++ tailWord_4170201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170201).length < 2 ^ (prefixWord ++ tailWord_4170201).sum := by decide
  have hdescent : baseEnd_4170201 < baseStart_4170201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170220 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_4170220 : Nat := 118140960795 + 4170220 * 2 ^ 59
def prefixEnd_4170220 : Nat := 4983230072969 + 3 ^ 40 * 4170220 * 2
def baseEnd_4170220 : Nat := 713775764997593076257171

theorem tailTrace_4170220 : CollatzResearch.WordTrace tailWord_4170220 prefixEnd_4170220 713775764997593076257171 := by
  unfold tailWord_4170220
  simp only [CollatzResearch.WordTrace]
  refine ⟨76050209476006315859314057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101400279301341754479085409 76050209476006315859314057)
  ·
    refine ⟨57037657107004736894485543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76050209476006315859314057 57037657107004736894485543)
    ·
      refine ⟨85556485660507105341728315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57037657107004736894485543 85556485660507105341728315)
      ·
        refine ⟨128334728490760658012592473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85556485660507105341728315 128334728490760658012592473)
        ·
          refine ⟨96251046368070493509444355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128334728490760658012592473 96251046368070493509444355)
          ·
            refine ⟨144376569552105740264166533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96251046368070493509444355 144376569552105740264166533)
            ·
              refine ⟨27070606791019826299531225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144376569552105740264166533 27070606791019826299531225)
              ·
                refine ⟨20302955093264869724648419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27070606791019826299531225 20302955093264869724648419)
                ·
                  refine ⟨30454432639897304586972629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20302955093264869724648419 30454432639897304586972629)
                  ·
                    refine ⟨713775764997593076257171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30454432639897304586972629 713775764997593076257171)
                    ·
                      rfl

theorem cell23_4170220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_4170220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170220 prefixEnd_4170220 := by exact prefixLift 4170220
  have htrace : WordTrace (prefixWord ++ tailWord_4170220) baseStart_4170220 baseEnd_4170220 := by
    simpa [prefixWord, tailWord_4170220, baseEnd_4170220] using wordTrace_append hprefix tailTrace_4170220
  have hstable : (prefixWord ++ tailWord_4170220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170220).length < 2 ^ (prefixWord ++ tailWord_4170220).sum := by decide
  have hdescent : baseEnd_4170220 < baseStart_4170220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170227 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 5, 2]
def baseStart_4170227 : Nat := 118140960795 + 4170227 * 2 ^ 59
def prefixEnd_4170227 : Nat := 4983230072969 + 3 ^ 40 * 4170227 * 2
def baseEnd_4170227 : Nat := 2141330889357360701383981

theorem tailTrace_4170227 : CollatzResearch.WordTrace tailWord_4170227 prefixEnd_4170227 2141330889357360701383981 := by
  unfold tailWord_4170227
  simp only [CollatzResearch.WordTrace]
  refine ⟨152100674262987271914132935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101400449508658181276088623 152100674262987271914132935)
  ·
    refine ⟨228151011394480907871199403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152100674262987271914132935 228151011394480907871199403)
    ·
      refine ⟨342226517091721361806799105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228151011394480907871199403 342226517091721361806799105)
      ·
        refine ⟨256669887818791021355099329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342226517091721361806799105 256669887818791021355099329)
        ·
          refine ⟨192502415864093266016324497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256669887818791021355099329 192502415864093266016324497)
          ·
            refine ⟨144376811898069949512243373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192502415864093266016324497 144376811898069949512243373)
            ·
              refine ⟨54141304461776231067091265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144376811898069949512243373 54141304461776231067091265)
              ·
                refine ⟨40605978346332173300318449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54141304461776231067091265 40605978346332173300318449)
                ·
                  refine ⟨30454483759749129975238837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40605978346332173300318449 30454483759749129975238837)
                  ·
                    refine ⟨2855107852476480935178641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30454483759749129975238837 2855107852476480935178641)
                    ·
                      refine ⟨2141330889357360701383981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855107852476480935178641 2141330889357360701383981)
                      ·
                        rfl

theorem cell23_4170227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5, 2].length) (baseStart_4170227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170227 prefixEnd_4170227 := by exact prefixLift 4170227
  have htrace : WordTrace (prefixWord ++ tailWord_4170227) baseStart_4170227 baseEnd_4170227 := by
    simpa [prefixWord, tailWord_4170227, baseEnd_4170227] using wordTrace_append hprefix tailTrace_4170227
  have hstable : (prefixWord ++ tailWord_4170227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170227).length < 2 ^ (prefixWord ++ tailWord_4170227).sum := by decide
  have hdescent : baseEnd_4170227 < baseStart_4170227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170277 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_4170277 : Nat := 118140960795 + 4170277 * 2 ^ 59
def prefixEnd_4170277 : Nat := 4983230072969 + 3 ^ 40 * 4170277 * 2
def baseEnd_4170277 : Nat := 2141356563390085505758751

theorem tailTrace_4170277 : CollatzResearch.WordTrace tailWord_4170277 prefixEnd_4170277 2141356563390085505758751 := by
  unfold tailWord_4170277
  simp only [CollatzResearch.WordTrace]
  refine ⟨152102497912806130453453085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101401665275204086968968723 152102497912806130453453085)
  ·
    refine ⟨57038436717302298920044907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152102497912806130453453085 57038436717302298920044907)
    ·
      refine ⟨85557655075953448380067361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57038436717302298920044907 85557655075953448380067361)
      ·
        refine ⟨64168241306965086285050521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85557655075953448380067361 64168241306965086285050521)
        ·
          refine ⟨48126180980223814713787891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64168241306965086285050521 48126180980223814713787891)
          ·
            refine ⟨72189271470335722070681837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48126180980223814713787891 72189271470335722070681837)
            ·
              refine ⟨27070976801375895776505689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72189271470335722070681837 27070976801375895776505689)
              ·
                refine ⟨20303232601031921832379267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27070976801375895776505689 20303232601031921832379267)
                ·
                  refine ⟨30454848901547882748568901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20303232601031921832379267 30454848901547882748568901)
                  ·
                    refine ⟨5710284169040228015356669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30454848901547882748568901 5710284169040228015356669)
                    ·
                      refine ⟨2141356563390085505758751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710284169040228015356669 2141356563390085505758751)
                      ·
                        rfl

theorem cell23_4170277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_4170277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170277 prefixEnd_4170277 := by exact prefixLift 4170277
  have htrace : WordTrace (prefixWord ++ tailWord_4170277) baseStart_4170277 baseEnd_4170277 := by
    simpa [prefixWord, tailWord_4170277, baseEnd_4170277] using wordTrace_append hprefix tailTrace_4170277
  have hstable : (prefixWord ++ tailWord_4170277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170277).length < 2 ^ (prefixWord ++ tailWord_4170277).sum := by decide
  have hdescent : baseEnd_4170277 < baseStart_4170277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170327 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 3, 5]
def baseStart_4170327 : Nat := 118140960795 + 4170327 * 2 ^ 59
def prefixEnd_4170327 : Nat := 4983230072969 + 3 ^ 40 * 4170327 * 2
def baseEnd_4170327 : Nat := 713794079140936770044507

theorem tailTrace_4170327 : CollatzResearch.WordTrace tailWord_4170327 prefixEnd_4170327 713794079140936770044507 := by
  unfold tailWord_4170327
  simp only [CollatzResearch.WordTrace]
  refine ⟨152104321562624988992773235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101402881041749992661848823 152104321562624988992773235)
  ·
    refine ⟨228156482343937483489159853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152104321562624988992773235 228156482343937483489159853)
    ·
      refine ⟨85558680878976556308434945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228156482343937483489159853 85558680878976556308434945)
      ·
        refine ⟨64169010659232417231326209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85558680878976556308434945 64169010659232417231326209)
        ·
          refine ⟨48126757994424312923494657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64169010659232417231326209 48126757994424312923494657)
          ·
            refine ⟨36095068495818234692620993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48126757994424312923494657 36095068495818234692620993)
            ·
              refine ⟨27071301371863676019465745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36095068495818234692620993 27071301371863676019465745)
              ·
                refine ⟨20303476028897757014599309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27071301371863676019465745 20303476028897757014599309)
                ·
                  refine ⟨7613803510836658880474741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20303476028897757014599309 7613803510836658880474741)
                  ·
                    refine ⟨713794079140936770044507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7613803510836658880474741 713794079140936770044507)
                    ·
                      rfl

theorem cell23_4170327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_4170327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170327 prefixEnd_4170327 := by exact prefixLift 4170327
  have htrace : WordTrace (prefixWord ++ tailWord_4170327) baseStart_4170327 baseEnd_4170327 := by
    simpa [prefixWord, tailWord_4170327, baseEnd_4170327] using wordTrace_append hprefix tailTrace_4170327
  have hstable : (prefixWord ++ tailWord_4170327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170327).length < 2 ^ (prefixWord ++ tailWord_4170327).sum := by decide
  have hdescent : baseEnd_4170327 < baseStart_4170327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170361 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_4170361 : Nat := 118140960795 + 4170361 * 2 ^ 59
def prefixEnd_4170361 : Nat := 4983230072969 + 3 ^ 40 * 4170361 * 2
def baseEnd_4170361 : Nat := 713799898588354392369455

theorem tailTrace_4170361 : CollatzResearch.WordTrace tailWord_4170361 prefixEnd_4170361 713799898588354392369455 := by
  unfold tailWord_4170361
  simp only [CollatzResearch.WordTrace]
  refine ⟨152105561644501812799510937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101403707763001208533007291 152105561644501812799510937)
  ·
    refine ⟨114079171233376359599633203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152105561644501812799510937 114079171233376359599633203)
    ·
      refine ⟨171118756850064539399449805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114079171233376359599633203 171118756850064539399449805)
      ·
        refine ⟨64169533818774202274793677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171118756850064539399449805 64169533818774202274793677)
        ·
          refine ⟨24063575182040325853047629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64169533818774202274793677 24063575182040325853047629)
          ·
            refine ⟨9023840693265122194892861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24063575182040325853047629 9023840693265122194892861)
            ·
              refine ⟨3383940259974420823084823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9023840693265122194892861 3383940259974420823084823)
              ·
                refine ⟨5075910389961631234627235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383940259974420823084823 5075910389961631234627235)
                ·
                  refine ⟨7613865584942446851940853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075910389961631234627235 7613865584942446851940853)
                  ·
                    refine ⟨713799898588354392369455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7613865584942446851940853 713799898588354392369455)
                    ·
                      rfl

theorem cell23_4170361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_4170361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170361 prefixEnd_4170361 := by exact prefixLift 4170361
  have htrace : WordTrace (prefixWord ++ tailWord_4170361) baseStart_4170361 baseEnd_4170361 := by
    simpa [prefixWord, tailWord_4170361, baseEnd_4170361] using wordTrace_append hprefix tailTrace_4170361
  have hstable : (prefixWord ++ tailWord_4170361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170361).length < 2 ^ (prefixWord ++ tailWord_4170361).sum := by decide
  have hdescent : baseEnd_4170361 < baseStart_4170361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170364 : List Nat := [2, 2, 2, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_4170364 : Nat := 118140960795 + 4170364 * 2 ^ 59
def prefixEnd_4170364 : Nat := 4983230072969 + 3 ^ 40 * 4170364 * 2
def baseEnd_4170364 : Nat := 2141401236207026665370851

theorem tailTrace_4170364 : CollatzResearch.WordTrace tailWord_4170364 prefixEnd_4170364 2141401236207026665370851 := by
  unfold tailWord_4170364
  simp only [CollatzResearch.WordTrace]
  refine ⟨76052835531745472155935073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101403780708993962874580097 76052835531745472155935073)
  ·
    refine ⟨57039626648809104116951305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76052835531745472155935073 57039626648809104116951305)
    ·
      refine ⟨42779719986606828087713479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57039626648809104116951305 42779719986606828087713479)
      ·
        refine ⟨64169579979910242131570219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42779719986606828087713479 64169579979910242131570219)
        ·
          refine ⟨96254369969865363197355329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64169579979910242131570219 96254369969865363197355329)
          ·
            refine ⟨72190777477399022398016497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96254369969865363197355329 72190777477399022398016497)
            ·
              refine ⟨54143083108049266798512373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72190777477399022398016497 54143083108049266798512373)
              ·
                refine ⟨5075914041379618762360535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54143083108049266798512373 5075914041379618762360535)
                ·
                  refine ⟨7613871062069428143540803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5075914041379618762360535 7613871062069428143540803)
                  ·
                    refine ⟨11420806593104142215311205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7613871062069428143540803 11420806593104142215311205)
                    ·
                      refine ⟨2141401236207026665370851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11420806593104142215311205 2141401236207026665370851)
                      ·
                        rfl

theorem cell23_4170364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_4170364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170364 prefixEnd_4170364 := by exact prefixLift 4170364
  have htrace : WordTrace (prefixWord ++ tailWord_4170364) baseStart_4170364 baseEnd_4170364 := by
    simpa [prefixWord, tailWord_4170364, baseEnd_4170364] using wordTrace_append hprefix tailTrace_4170364
  have hstable : (prefixWord ++ tailWord_4170364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170364).length < 2 ^ (prefixWord ++ tailWord_4170364).sum := by decide
  have hdescent : baseEnd_4170364 < baseStart_4170364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_4170367 : Nat := 118140960795 + 4170367 * 2 ^ 59
def prefixEnd_4170367 : Nat := 4983230072969 + 3 ^ 40 * 4170367 * 2
def baseEnd_4170367 : Nat := 2141402776648990153633337

theorem tailTrace_4170367 : CollatzResearch.WordTrace tailWord_4170367 prefixEnd_4170367 2141402776648990153633337 := by
  unfold tailWord_4170367
  simp only [CollatzResearch.WordTrace]
  refine ⟨152105780482480075824229355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101403853654986717216152903 152105780482480075824229355)
  ·
    refine ⟨228158670723720113736344033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152105780482480075824229355 228158670723720113736344033)
    ·
      refine ⟨171119003042790085302258025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228158670723720113736344033 171119003042790085302258025)
      ·
        refine ⟨128339252282092563976693519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171119003042790085302258025 128339252282092563976693519)
        ·
          refine ⟨192508878423138845965040279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128339252282092563976693519 192508878423138845965040279)
          ·
            refine ⟨288763317634708268947560419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192508878423138845965040279 288763317634708268947560419)
            ·
              refine ⟨433144976452062403421340629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288763317634708268947560419 433144976452062403421340629)
              ·
                refine ⟨10151835385595212580187671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 433144976452062403421340629 10151835385595212580187671)
                ·
                  refine ⟨15227753078392818870281507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10151835385595212580187671 15227753078392818870281507)
                  ·
                    refine ⟨22841629617589228305422261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15227753078392818870281507 22841629617589228305422261)
                    ·
                      refine ⟨2141402776648990153633337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22841629617589228305422261 2141402776648990153633337)
                      ·
                        rfl

theorem cell23_4170367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_4170367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170367 prefixEnd_4170367 := by exact prefixLift 4170367
  have htrace : WordTrace (prefixWord ++ tailWord_4170367) baseStart_4170367 baseEnd_4170367 := by
    simpa [prefixWord, tailWord_4170367, baseEnd_4170367] using wordTrace_append hprefix tailTrace_4170367
  have hstable : (prefixWord ++ tailWord_4170367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170367).length < 2 ^ (prefixWord ++ tailWord_4170367).sum := by decide
  have hdescent : baseEnd_4170367 < baseStart_4170367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170377 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_4170377 : Nat := 118140960795 + 4170377 * 2 ^ 59
def prefixEnd_4170377 : Nat := 4983230072969 + 3 ^ 40 * 4170377 * 2
def baseEnd_4170377 : Nat := 2141407911455535114508291

theorem tailTrace_4170377 : CollatzResearch.WordTrace tailWord_4170377 prefixEnd_4170377 2141407911455535114508291 := by
  unfold tailWord_4170377
  simp only [CollatzResearch.WordTrace]
  refine ⟨152106145212443847532093385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101404096808295898354728923 152106145212443847532093385)
  ·
    refine ⟨114079608909332885649070039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152106145212443847532093385 114079608909332885649070039)
    ·
      refine ⟨171119413363999328473605059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114079608909332885649070039 171119413363999328473605059)
      ·
        refine ⟨256679120045998992710407589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171119413363999328473605059 256679120045998992710407589)
        ·
          refine ⟨48127335008624811133201423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256679120045998992710407589 48127335008624811133201423)
          ·
            refine ⟨72191002512937216699802135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48127335008624811133201423 72191002512937216699802135)
            ·
              refine ⟨108286503769405825049703203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72191002512937216699802135 108286503769405825049703203)
              ·
                refine ⟨162429755654108737574554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108286503769405825049703203 162429755654108737574554805)
                ·
                  refine ⟨15227789592572694147614513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162429755654108737574554805 15227789592572694147614513)
                  ·
                    refine ⟨11420842194429520610710885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15227789592572694147614513 11420842194429520610710885)
                    ·
                      refine ⟨2141407911455535114508291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11420842194429520610710885 2141407911455535114508291)
                      ·
                        rfl

theorem cell23_4170377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_4170377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170377 prefixEnd_4170377 := by exact prefixLift 4170377
  have htrace : WordTrace (prefixWord ++ tailWord_4170377) baseStart_4170377 baseEnd_4170377 := by
    simpa [prefixWord, tailWord_4170377, baseEnd_4170377] using wordTrace_append hprefix tailTrace_4170377
  have hstable : (prefixWord ++ tailWord_4170377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170377).length < 2 ^ (prefixWord ++ tailWord_4170377).sum := by decide
  have hdescent : baseEnd_4170377 < baseStart_4170377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170404 : List Nat := [2, 3, 1, 2, 2, 1, 5, 7]
def baseStart_4170404 : Nat := 118140960795 + 4170404 * 2 ^ 59
def prefixEnd_4170404 : Nat := 4983230072969 + 3 ^ 40 * 4170404 * 2
def baseEnd_4170404 : Nat := 79311917608637278106321

theorem tailTrace_4170404 : CollatzResearch.WordTrace tailWord_4170404 prefixEnd_4170404 79311917608637278106321 := by
  unfold tailWord_4170404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76053564991673015571663133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101404753322230687428884177 76053564991673015571663133)
  ·
    refine ⟨28520086871877380839373675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76053564991673015571663133 28520086871877380839373675)
    ·
      refine ⟨42780130307816071259060513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28520086871877380839373675 42780130307816071259060513)
      ·
        refine ⟨32085097730862053444295385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42780130307816071259060513 32085097730862053444295385)
        ·
          refine ⟨24063823298146540083221539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32085097730862053444295385 24063823298146540083221539)
          ·
            refine ⟨36095734947219810124832309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24063823298146540083221539 36095734947219810124832309)
            ·
              refine ⟨3383975151301857199203029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36095734947219810124832309 3383975151301857199203029)
              ·
                refine ⟨79311917608637278106321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383975151301857199203029 79311917608637278106321)
                ·
                  rfl

theorem cell23_4170404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 7].length) (baseStart_4170404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170404 prefixEnd_4170404 := by exact prefixLift 4170404
  have htrace : WordTrace (prefixWord ++ tailWord_4170404) baseStart_4170404 baseEnd_4170404 := by
    simpa [prefixWord, tailWord_4170404, baseEnd_4170404] using wordTrace_append hprefix tailTrace_4170404
  have hstable : (prefixWord ++ tailWord_4170404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170404).length < 2 ^ (prefixWord ++ tailWord_4170404).sum := by decide
  have hdescent : baseEnd_4170404 < baseStart_4170404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170415 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 1, 2, 2]
def baseStart_4170415 : Nat := 118140960795 + 4170415 * 2 ^ 59
def prefixEnd_4170415 : Nat := 4983230072969 + 3 ^ 40 * 4170415 * 2
def baseEnd_4170415 : Nat := 2141427423720405965833117

theorem tailTrace_4170415 : CollatzResearch.WordTrace tailWord_4170415 prefixEnd_4170415 2141427423720405965833117 := by
  unfold tailWord_4170415
  simp only [CollatzResearch.WordTrace]
  refine ⟨152107531186306180021976699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101405020790870786681317799 152107531186306180021976699)
  ·
    refine ⟨228161296779459270032965049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152107531186306180021976699 228161296779459270032965049)
    ·
      refine ⟨171120972584594452524723787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228161296779459270032965049 171120972584594452524723787)
      ·
        refine ⟨256681458876891678787085681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171120972584594452524723787 256681458876891678787085681)
        ·
          refine ⟨192511094157668759090314261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256681458876891678787085681 192511094157668759090314261)
          ·
            refine ⟨9023957538640723082358481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192511094157668759090314261 9023957538640723082358481)
            ·
              refine ⟨6767968153980542311768861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9023957538640723082358481 6767968153980542311768861)
              ·
                refine ⟨2537988057742703366913323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6767968153980542311768861 2537988057742703366913323)
                ·
                  refine ⟨3806982086614055050369985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2537988057742703366913323 3806982086614055050369985)
                  ·
                    refine ⟨2855236564960541287777489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3806982086614055050369985 2855236564960541287777489)
                    ·
                      refine ⟨2141427423720405965833117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855236564960541287777489 2141427423720405965833117)
                      ·
                        rfl

theorem cell23_4170415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 2, 2].length) (baseStart_4170415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170415 prefixEnd_4170415 := by exact prefixLift 4170415
  have htrace : WordTrace (prefixWord ++ tailWord_4170415) baseStart_4170415 baseEnd_4170415 := by
    simpa [prefixWord, tailWord_4170415, baseEnd_4170415] using wordTrace_append hprefix tailTrace_4170415
  have hstable : (prefixWord ++ tailWord_4170415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170415).length < 2 ^ (prefixWord ++ tailWord_4170415).sum := by decide
  have hdescent : baseEnd_4170415 < baseStart_4170415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170431 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_4170431 : Nat := 118140960795 + 4170431 * 2 ^ 59
def prefixEnd_4170431 : Nat := 4983230072969 + 3 ^ 40 * 4170431 * 2
def baseEnd_4170431 : Nat := 2141435639410877903233043

theorem tailTrace_4170431 : CollatzResearch.WordTrace tailWord_4170431 prefixEnd_4170431 2141435639410877903233043 := by
  unfold tailWord_4170431
  simp only [CollatzResearch.WordTrace]
  refine ⟨152108114754248214754559147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101405409836165476503039431 152108114754248214754559147)
  ·
    refine ⟨228162172131372322131838721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152108114754248214754559147 228162172131372322131838721)
    ·
      refine ⟨171121629098529241598879041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228162172131372322131838721 171121629098529241598879041)
      ·
        refine ⟨128341221823896931199159281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171121629098529241598879041 128341221823896931199159281)
        ·
          refine ⟨96255916367922698399369461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128341221823896931199159281 96255916367922698399369461)
          ·
            refine ⟨9023992159492752974940887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96255916367922698399369461 9023992159492752974940887)
            ·
              refine ⟨13535988239239129462411331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9023992159492752974940887 13535988239239129462411331)
              ·
                refine ⟨20303982358858694193616997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13535988239239129462411331 20303982358858694193616997)
                ·
                  refine ⟨3806996692286005161303187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20303982358858694193616997 3806996692286005161303187)
                  ·
                    refine ⟨5710495038429007741954781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3806996692286005161303187 5710495038429007741954781)
                    ·
                      refine ⟨2141435639410877903233043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710495038429007741954781 2141435639410877903233043)
                      ·
                        rfl

theorem cell23_4170431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_4170431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170431 prefixEnd_4170431 := by exact prefixLift 4170431
  have htrace : WordTrace (prefixWord ++ tailWord_4170431) baseStart_4170431 baseEnd_4170431 := by
    simpa [prefixWord, tailWord_4170431, baseEnd_4170431] using wordTrace_append hprefix tailTrace_4170431
  have hstable : (prefixWord ++ tailWord_4170431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170431).length < 2 ^ (prefixWord ++ tailWord_4170431).sum := by decide
  have hdescent : baseEnd_4170431 < baseStart_4170431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170445 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4170445 : Nat := 118140960795 + 4170445 * 2 ^ 59
def prefixEnd_4170445 : Nat := 4983230072969 + 3 ^ 40 * 4170445 * 2
def baseEnd_4170445 : Nat := 2141442828140040848457979

theorem tailTrace_4170445 : CollatzResearch.WordTrace tailWord_4170445 prefixEnd_4170445 2141442828140040848457979 := by
  unfold tailWord_4170445
  simp only [CollatzResearch.WordTrace]
  refine ⟨152108625376197495145568789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101405750250798330097045859 152108625376197495145568789)
  ·
    refine ⟨7130091814509257584948537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152108625376197495145568789 7130091814509257584948537)
    ·
      refine ⟨5347568860881943188711403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7130091814509257584948537 5347568860881943188711403)
      ·
        refine ⟨8021353291322914783067105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347568860881943188711403 8021353291322914783067105)
        ·
          refine ⟨6016014968492186087300329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8021353291322914783067105 6016014968492186087300329)
          ·
            refine ⟨4512011226369139565475247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016014968492186087300329 4512011226369139565475247)
            ·
              refine ⟨6768016839553709348212871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512011226369139565475247 6768016839553709348212871)
              ·
                refine ⟨10152025259330564022319307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768016839553709348212871 10152025259330564022319307)
                ·
                  refine ⟨15228037888995846033478961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10152025259330564022319307 15228037888995846033478961)
                  ·
                    refine ⟨11421028416746884525109221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15228037888995846033478961 11421028416746884525109221)
                    ·
                      refine ⟨2141442828140040848457979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11421028416746884525109221 2141442828140040848457979)
                      ·
                        rfl

theorem cell23_4170445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4170445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170445 prefixEnd_4170445 := by exact prefixLift 4170445
  have htrace : WordTrace (prefixWord ++ tailWord_4170445) baseStart_4170445 baseEnd_4170445 := by
    simpa [prefixWord, tailWord_4170445, baseEnd_4170445] using wordTrace_append hprefix tailTrace_4170445
  have hstable : (prefixWord ++ tailWord_4170445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170445).length < 2 ^ (prefixWord ++ tailWord_4170445).sum := by decide
  have hdescent : baseEnd_4170445 < baseStart_4170445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170458 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_4170458 : Nat := 118140960795 + 4170458 * 2 ^ 59
def prefixEnd_4170458 : Nat := 4983230072969 + 3 ^ 40 * 4170458 * 2
def baseEnd_4170458 : Nat := 2141449503388549297595419

theorem tailTrace_4170458 : CollatzResearch.WordTrace tailWord_4170458 prefixEnd_4170458 2141449503388549297595419 := by
  unfold tailWord_4170458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38027274881287599591448007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101406066350100265577194685 38027274881287599591448007)
  ·
    refine ⟨57040912321931399387172011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38027274881287599591448007 57040912321931399387172011)
    ·
      refine ⟨85561368482897099080758017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57040912321931399387172011 85561368482897099080758017)
      ·
        refine ⟨64171026362172824310568513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85561368482897099080758017 64171026362172824310568513)
        ·
          refine ⟨48128269771629618232926385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64171026362172824310568513 48128269771629618232926385)
          ·
            refine ⟨36096202328722213674694789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48128269771629618232926385 36096202328722213674694789)
            ·
              refine ⟨6768037936635415064005273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36096202328722213674694789 6768037936635415064005273)
              ·
                refine ⟨5076028452476561298003955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6768037936635415064005273 5076028452476561298003955)
                ·
                  refine ⟨7614042678714841947005933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076028452476561298003955 7614042678714841947005933)
                  ·
                    refine ⟨2855266004518065730127225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7614042678714841947005933 2855266004518065730127225)
                    ·
                      refine ⟨2141449503388549297595419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855266004518065730127225 2141449503388549297595419)
                      ·
                        rfl

theorem cell23_4170458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_4170458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170458 prefixEnd_4170458 := by exact prefixLift 4170458
  have htrace : WordTrace (prefixWord ++ tailWord_4170458) baseStart_4170458 baseEnd_4170458 := by
    simpa [prefixWord, tailWord_4170458, baseEnd_4170458] using wordTrace_append hprefix tailTrace_4170458
  have hstable : (prefixWord ++ tailWord_4170458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170458).length < 2 ^ (prefixWord ++ tailWord_4170458).sum := by decide
  have hdescent : baseEnd_4170458 < baseStart_4170458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170474 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_4170474 : Nat := 118140960795 + 4170474 * 2 ^ 59
def prefixEnd_4170474 : Nat := 4983230072969 + 3 ^ 40 * 4170474 * 2
def baseEnd_4170474 : Nat := 2141457719079021234995345

theorem tailTrace_4170474 : CollatzResearch.WordTrace tailWord_4170474 prefixEnd_4170474 2141457719079021234995345 := by
  unfold tailWord_4170474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38027420773273108274593619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101406455395394955398916317 38027420773273108274593619)
  ·
    refine ⟨57041131159909662411890429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38027420773273108274593619 57041131159909662411890429)
    ·
      refine ⟨21390424184966123404458911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57041131159909662411890429 21390424184966123404458911)
      ·
        refine ⟨32085636277449185106688367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21390424184966123404458911 32085636277449185106688367)
        ·
          refine ⟨48128454416173777660032551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32085636277449185106688367 48128454416173777660032551)
          ·
            refine ⟨72192681624260666490048827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48128454416173777660032551 72192681624260666490048827)
            ·
              refine ⟨108289022436390999735073241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72192681624260666490048827 108289022436390999735073241)
              ·
                refine ⟨81216766827293249801304931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108289022436390999735073241 81216766827293249801304931)
                ·
                  refine ⟨121825150240939874701957397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81216766827293249801304931 121825150240939874701957397)
                  ·
                    refine ⟨5710553917544056626654253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121825150240939874701957397 5710553917544056626654253)
                    ·
                      refine ⟨2141457719079021234995345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710553917544056626654253 2141457719079021234995345)
                      ·
                        rfl

theorem cell23_4170474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_4170474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170474 prefixEnd_4170474 := by exact prefixLift 4170474
  have htrace : WordTrace (prefixWord ++ tailWord_4170474) baseStart_4170474 baseEnd_4170474 := by
    simpa [prefixWord, tailWord_4170474, baseEnd_4170474] using wordTrace_append hprefix tailTrace_4170474
  have hstable : (prefixWord ++ tailWord_4170474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170474).length < 2 ^ (prefixWord ++ tailWord_4170474).sum := by decide
  have hdescent : baseEnd_4170474 < baseStart_4170474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170487 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4170487 : Nat := 118140960795 + 4170487 * 2 ^ 59
def prefixEnd_4170487 : Nat := 4983230072969 + 3 ^ 40 * 4170487 * 2
def baseEnd_4170487 : Nat := 2141464394327529684132785

theorem tailTrace_4170487 : CollatzResearch.WordTrace tailWord_4170487 prefixEnd_4170487 2141464394327529684132785 := by
  unfold tailWord_4170487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152110157242045336318597715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101406771494696890879065143 152110157242045336318597715)
  ·
    refine ⟨228165235863068004477896573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152110157242045336318597715 228165235863068004477896573)
    ·
      refine ⟨85561963448650501679211215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228165235863068004477896573 85561963448650501679211215)
      ·
        refine ⟨128342945172975752518816823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85561963448650501679211215 128342945172975752518816823)
        ·
          refine ⟨192514417759463628778225235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128342945172975752518816823 192514417759463628778225235)
          ·
            refine ⟨288771626639195443167337853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192514417759463628778225235 288771626639195443167337853)
            ·
              refine ⟨108289359989698291187751695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288771626639195443167337853 108289359989698291187751695)
              ·
                refine ⟨162434039984547436781627543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108289359989698291187751695 162434039984547436781627543)
                ·
                  refine ⟨243651059976821155172441315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162434039984547436781627543 243651059976821155172441315)
                  ·
                    refine ⟨365476589965231732758661973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243651059976821155172441315 365476589965231732758661973)
                    ·
                      refine ⟨2141464394327529684132785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 365476589965231732758661973 2141464394327529684132785)
                      ·
                        rfl

theorem cell23_4170487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4170487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170487 prefixEnd_4170487 := by exact prefixLift 4170487
  have htrace : WordTrace (prefixWord ++ tailWord_4170487) baseStart_4170487 baseEnd_4170487 := by
    simpa [prefixWord, tailWord_4170487, baseEnd_4170487] using wordTrace_append hprefix tailTrace_4170487
  have hstable : (prefixWord ++ tailWord_4170487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170487).length < 2 ^ (prefixWord ++ tailWord_4170487).sum := by decide
  have hdescent : baseEnd_4170487 < baseStart_4170487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170488 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_4170488 : Nat := 118140960795 + 4170488 * 2 ^ 59
def prefixEnd_4170488 : Nat := 4983230072969 + 3 ^ 40 * 4170488 * 2
def baseEnd_4170488 : Nat := 2141464907808184180220281

theorem tailTrace_4170488 : CollatzResearch.WordTrace tailWord_4170488 prefixEnd_4170488 2141464907808184180220281 := by
  unfold tailWord_4170488
  simp only [CollatzResearch.WordTrace]
  refine ⟨76055096857520856744692059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101406795810027808992922745 76055096857520856744692059)
  ·
    refine ⟨114082645286281285117038089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76055096857520856744692059 114082645286281285117038089)
    ·
      refine ⟨85561983964710963837778567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114082645286281285117038089 85561983964710963837778567)
      ·
        refine ⟨128342975947066445756667851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85561983964710963837778567 128342975947066445756667851)
        ·
          refine ⟨192514463920599668635001777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128342975947066445756667851 192514463920599668635001777)
          ·
            refine ⟨144385847940449751476251333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192514463920599668635001777 144385847940449751476251333)
            ·
              refine ⟨27072346488834328401797125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144385847940449751476251333 27072346488834328401797125)
              ·
                refine ⟨5076064966656436575336961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27072346488834328401797125 5076064966656436575336961)
                ·
                  refine ⟨3807048724992327431502721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076064966656436575336961 3807048724992327431502721)
                  ·
                    refine ⟨2855286543744245573627041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807048724992327431502721 2855286543744245573627041)
                    ·
                      refine ⟨2141464907808184180220281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855286543744245573627041 2141464907808184180220281)
                      ·
                        rfl

theorem cell23_4170488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_4170488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170488 prefixEnd_4170488 := by exact prefixLift 4170488
  have htrace : WordTrace (prefixWord ++ tailWord_4170488) baseStart_4170488 baseEnd_4170488 := by
    simpa [prefixWord, tailWord_4170488, baseEnd_4170488] using wordTrace_append hprefix tailTrace_4170488
  have hstable : (prefixWord ++ tailWord_4170488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170488).length < 2 ^ (prefixWord ++ tailWord_4170488).sum := by decide
  have hdescent : baseEnd_4170488 < baseStart_4170488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170505 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 2, 2, 2]
def baseStart_4170505 : Nat := 118140960795 + 4170505 * 2 ^ 59
def prefixEnd_4170505 : Nat := 4983230072969 + 3 ^ 40 * 4170505 * 2
def baseEnd_4170505 : Nat := 2141473636979310613707703

theorem tailTrace_4170505 : CollatzResearch.WordTrace tailWord_4170505 prefixEnd_4170505 2141473636979310613707703 := by
  unfold tailWord_4170505
  simp only [CollatzResearch.WordTrace]
  refine ⟨152110813755980125392752969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101407209170653416928501979 152110813755980125392752969)
  ·
    refine ⟨114083110316985094044564727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152110813755980125392752969 114083110316985094044564727)
    ·
      refine ⟨171124665475477641066847091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114083110316985094044564727 171124665475477641066847091)
      ·
        refine ⟨256686998213216461600270637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171124665475477641066847091 256686998213216461600270637)
        ·
          refine ⟨96257624329956173100101489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256686998213216461600270637 96257624329956173100101489)
          ·
            refine ⟨72193218247467129825076117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96257624329956173100101489 72193218247467129825076117)
            ·
              refine ⟨3384057105350021710550443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72193218247467129825076117 3384057105350021710550443)
              ·
                refine ⟨5076085658025032565825665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384057105350021710550443 5076085658025032565825665)
                ·
                  refine ⟨3807064243518774424369249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076085658025032565825665 3807064243518774424369249)
                  ·
                    refine ⟨2855298182639080818276937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807064243518774424369249 2855298182639080818276937)
                    ·
                      refine ⟨2141473636979310613707703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855298182639080818276937 2141473636979310613707703)
                      ·
                        rfl

theorem cell23_4170505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 2, 2].length) (baseStart_4170505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170505 prefixEnd_4170505 := by exact prefixLift 4170505
  have htrace : WordTrace (prefixWord ++ tailWord_4170505) baseStart_4170505 baseEnd_4170505 := by
    simpa [prefixWord, tailWord_4170505, baseEnd_4170505] using wordTrace_append hprefix tailTrace_4170505
  have hstable : (prefixWord ++ tailWord_4170505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170505).length < 2 ^ (prefixWord ++ tailWord_4170505).sum := by decide
  have hdescent : baseEnd_4170505 < baseStart_4170505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170574 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4170574 : Nat := 118140960795 + 4170574 * 2 ^ 59
def prefixEnd_4170574 : Nat := 4983230072969 + 3 ^ 40 * 4170574 * 2
def baseEnd_4170574 : Nat := 2141509067144470843744885

theorem tailTrace_4170574 : CollatzResearch.WordTrace tailWord_4170574 prefixEnd_4170574 2141509067144470843744885 := by
  unfold tailWord_4170574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014166299091268772126847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101408886928486766784676517 19014166299091268772126847)
  ·
    refine ⟨28521249448636903158190271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014166299091268772126847 28521249448636903158190271)
    ·
      refine ⟨42781874172955354737285407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28521249448636903158190271 42781874172955354737285407)
      ·
        refine ⟨64172811259433032105928111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42781874172955354737285407 64172811259433032105928111)
        ·
          refine ⟨96259216889149548158892167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64172811259433032105928111 96259216889149548158892167)
          ·
            refine ⟨144388825333724322238338251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96259216889149548158892167 144388825333724322238338251)
            ·
              refine ⟨216583238000586483357507377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144388825333724322238338251 216583238000586483357507377)
              ·
                refine ⟨162437428500439862518130533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216583238000586483357507377 162437428500439862518130533)
                ·
                  refine ⟨30457017843832474222149475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162437428500439862518130533 30457017843832474222149475)
                  ·
                    refine ⟨45685526765748711333224213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30457017843832474222149475 45685526765748711333224213)
                    ·
                      refine ⟨2141509067144470843744885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45685526765748711333224213 2141509067144470843744885)
                      ·
                        rfl

theorem cell23_4170574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4170574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170574 prefixEnd_4170574 := by exact prefixLift 4170574
  have htrace : WordTrace (prefixWord ++ tailWord_4170574) baseStart_4170574 baseEnd_4170574 := by
    simpa [prefixWord, tailWord_4170574, baseEnd_4170574] using wordTrace_append hprefix tailTrace_4170574
  have hstable : (prefixWord ++ tailWord_4170574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170574).length < 2 ^ (prefixWord ++ tailWord_4170574).sum := by decide
  have hdescent : baseEnd_4170574 < baseStart_4170574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170581 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4170581 : Nat := 118140960795 + 4170581 * 2 ^ 59
def prefixEnd_4170581 : Nat := 4983230072969 + 3 ^ 40 * 4170581 * 2
def baseEnd_4170581 : Nat := 2141512661509052316357353

theorem tailTrace_4170581 : CollatzResearch.WordTrace tailWord_4170581 prefixEnd_4170581 2141512661509052316357353 := by
  unfold tailWord_4170581
  simp only [CollatzResearch.WordTrace]
  refine ⟨152113585703704790372519597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101409057135803193581679731 152113585703704790372519597)
  ·
    refine ⟨57042594638889296389694849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152113585703704790372519597 57042594638889296389694849)
    ·
      refine ⟨42781945979166972292271137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57042594638889296389694849 42781945979166972292271137)
      ·
        refine ⟨32086459484375229219203353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781945979166972292271137 32086459484375229219203353)
        ·
          refine ⟨24064844613281421914402515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32086459484375229219203353 24064844613281421914402515)
          ·
            refine ⟨36097266919922132871603773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24064844613281421914402515 36097266919922132871603773)
            ·
              refine ⟨13536475094970799826851415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36097266919922132871603773 13536475094970799826851415)
              ·
                refine ⟨20304712642456199740277123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13536475094970799826851415 20304712642456199740277123)
                ·
                  refine ⟨30457068963684299610415685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20304712642456199740277123 30457068963684299610415685)
                  ·
                    refine ⟨5710700430690806176952941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30457068963684299610415685 5710700430690806176952941)
                    ·
                      refine ⟨2141512661509052316357353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710700430690806176952941 2141512661509052316357353)
                      ·
                        rfl

theorem cell23_4170581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4170581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170581 prefixEnd_4170581 := by exact prefixLift 4170581
  have htrace : WordTrace (prefixWord ++ tailWord_4170581) baseStart_4170581 baseEnd_4170581 := by
    simpa [prefixWord, tailWord_4170581, baseEnd_4170581] using wordTrace_append hprefix tailTrace_4170581
  have hstable : (prefixWord ++ tailWord_4170581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170581).length < 2 ^ (prefixWord ++ tailWord_4170581).sum := by decide
  have hdescent : baseEnd_4170581 < baseStart_4170581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170604 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_4170604 : Nat := 118140960795 + 4170604 * 2 ^ 59
def prefixEnd_4170604 : Nat := 4983230072969 + 3 ^ 40 * 4170604 * 2
def baseEnd_4170604 : Nat := 2141524471564105726369747

theorem tailTrace_4170604 : CollatzResearch.WordTrace tailWord_4170604 prefixEnd_4170604 2141524471564105726369747 := by
  unfold tailWord_4170604
  simp only [CollatzResearch.WordTrace]
  refine ⟨76057212291310732650303433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101409616388414310200404577 76057212291310732650303433)
  ·
    refine ⟨57042909218483049487727575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76057212291310732650303433 57042909218483049487727575)
    ·
      refine ⟨85564363827724574231591363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57042909218483049487727575 85564363827724574231591363)
      ·
        refine ⟨128346545741586861347387045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85564363827724574231591363 128346545741586861347387045)
        ·
          refine ⟨24064977326547536502635071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128346545741586861347387045 24064977326547536502635071)
          ·
            refine ⟨36097465989821304753952607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24064977326547536502635071 36097465989821304753952607)
            ·
              refine ⟨54146198984731957130928911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36097465989821304753952607 54146198984731957130928911)
              ·
                refine ⟨81219298477097935696393367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54146198984731957130928911 81219298477097935696393367)
                ·
                  refine ⟨121828947715646903544590051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81219298477097935696393367 121828947715646903544590051)
                  ·
                    refine ⟨182743421573470355316885077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121828947715646903544590051 182743421573470355316885077)
                    ·
                      refine ⟨2141524471564105726369747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 182743421573470355316885077 2141524471564105726369747)
                      ·
                        rfl

theorem cell23_4170604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_4170604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170604 prefixEnd_4170604 := by exact prefixLift 4170604
  have htrace : WordTrace (prefixWord ++ tailWord_4170604) baseStart_4170604 baseEnd_4170604 := by
    simpa [prefixWord, tailWord_4170604, baseEnd_4170604] using wordTrace_append hprefix tailTrace_4170604
  have hstable : (prefixWord ++ tailWord_4170604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170604).length < 2 ^ (prefixWord ++ tailWord_4170604).sum := by decide
  have hdescent : baseEnd_4170604 < baseStart_4170604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170655 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4170655 : Nat := 118140960795 + 4170655 * 2 ^ 59
def prefixEnd_4170655 : Nat := 4983230072969 + 3 ^ 40 * 4170655 * 2
def baseEnd_4170655 : Nat := 2141550659077485026832013

theorem tailTrace_4170655 : CollatzResearch.WordTrace tailWord_4170655 prefixEnd_4170655 2141550659077485026832013 := by
  unfold tailWord_4170655
  simp only [CollatzResearch.WordTrace]
  refine ⟨152116284705436701010713419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101410856470291134007142279 152116284705436701010713419)
  ·
    refine ⟨228174427058155051516070129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152116284705436701010713419 228174427058155051516070129)
    ·
      refine ⟨171130820293616288637052597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228174427058155051516070129 171130820293616288637052597)
      ·
        refine ⟨16043514402526527059723681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171130820293616288637052597 16043514402526527059723681)
        ·
          refine ⟨12032635801894895294792761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043514402526527059723681 12032635801894895294792761)
          ·
            refine ⟨9024476851421171471094571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032635801894895294792761 9024476851421171471094571)
            ·
              refine ⟨13536715277131757206641857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024476851421171471094571 13536715277131757206641857)
              ·
                refine ⟨10152536457848817904981393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13536715277131757206641857 10152536457848817904981393)
                ·
                  refine ⟨7614402343386613428736045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10152536457848817904981393 7614402343386613428736045)
                  ·
                    refine ⟨2855400878769980035776017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7614402343386613428736045 2855400878769980035776017)
                    ·
                      refine ⟨2141550659077485026832013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855400878769980035776017 2141550659077485026832013)
                      ·
                        rfl

theorem cell23_4170655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4170655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170655 prefixEnd_4170655 := by exact prefixLift 4170655
  have htrace : WordTrace (prefixWord ++ tailWord_4170655) baseStart_4170655 baseEnd_4170655 := by
    simpa [prefixWord, tailWord_4170655, baseEnd_4170655] using wordTrace_append hprefix tailTrace_4170655
  have hstable : (prefixWord ++ tailWord_4170655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170655).length < 2 ^ (prefixWord ++ tailWord_4170655).sum := by decide
  have hdescent : baseEnd_4170655 < baseStart_4170655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170669 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 6]
def baseStart_4170669 : Nat := 118140960795 + 4170669 * 2 ^ 59
def prefixEnd_4170669 : Nat := 4983230072969 + 3 ^ 40 * 4170669 * 2
def baseEnd_4170669 : Nat := 237950871978516441339661

theorem tailTrace_4170669 : CollatzResearch.WordTrace tailWord_4170669 prefixEnd_4170669 237950871978516441339661 := by
  unfold tailWord_4170669
  simp only [CollatzResearch.WordTrace]
  refine ⟨152116795327385981401723061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101411196884923987601148707 152116795327385981401723061)
  ·
    refine ⟨14260949561942435756411537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152116795327385981401723061 14260949561942435756411537)
    ·
      refine ⟨10695712171456826817308653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14260949561942435756411537 10695712171456826817308653)
      ·
        refine ⟨4010892064296310056490745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10695712171456826817308653 4010892064296310056490745)
        ·
          refine ⟨3008169048222232542368059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010892064296310056490745 3008169048222232542368059)
          ·
            refine ⟨4512253572333348813552089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008169048222232542368059 4512253572333348813552089)
            ·
              refine ⟨3384190179250011610164067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4512253572333348813552089 3384190179250011610164067)
              ·
                refine ⟨5076285268875017415246101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384190179250011610164067 5076285268875017415246101)
                ·
                  refine ⟨237950871978516441339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5076285268875017415246101 237950871978516441339661)
                  ·
                    rfl

theorem cell23_4170669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_4170669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170669 prefixEnd_4170669 := by exact prefixLift 4170669
  have htrace : WordTrace (prefixWord ++ tailWord_4170669) baseStart_4170669 baseEnd_4170669 := by
    simpa [prefixWord, tailWord_4170669, baseEnd_4170669] using wordTrace_append hprefix tailTrace_4170669
  have hstable : (prefixWord ++ tailWord_4170669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170669).length < 2 ^ (prefixWord ++ tailWord_4170669).sum := by decide
  have hdescent : baseEnd_4170669 < baseStart_4170669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170681 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4170681 : Nat := 118140960795 + 4170681 * 2 ^ 59
def prefixEnd_4170681 : Nat := 4983230072969 + 3 ^ 40 * 4170681 * 2
def baseEnd_4170681 : Nat := 2141564009574501925106893

theorem tailTrace_4170681 : CollatzResearch.WordTrace tailWord_4170681 prefixEnd_4170681 2141564009574501925106893 := by
  unfold tailWord_4170681
  simp only [CollatzResearch.WordTrace]
  refine ⟨152117233003342507451159897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101411488668895004967439931 152117233003342507451159897)
  ·
    refine ⟨114087924752506880588369923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152117233003342507451159897 114087924752506880588369923)
    ·
      refine ⟨171131887128760320882554885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114087924752506880588369923 171131887128760320882554885)
      ·
        refine ⟨32087228836642560165479041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171131887128760320882554885 32087228836642560165479041)
        ·
          refine ⟨24065421627481920124109281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32087228836642560165479041 24065421627481920124109281)
          ·
            refine ⟨18049066220611440093081961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24065421627481920124109281 18049066220611440093081961)
            ·
              refine ⟨13536799665458580069811471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18049066220611440093081961 13536799665458580069811471)
              ·
                refine ⟨20305199498187870104717207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13536799665458580069811471 20305199498187870104717207)
                ·
                  refine ⟨30457799247281805157075811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20305199498187870104717207 30457799247281805157075811)
                  ·
                    refine ⟨45686698870922707735613717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30457799247281805157075811 45686698870922707735613717)
                    ·
                      refine ⟨2141564009574501925106893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45686698870922707735613717 2141564009574501925106893)
                      ·
                        rfl

theorem cell23_4170681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4170681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170681 prefixEnd_4170681 := by exact prefixLift 4170681
  have htrace : WordTrace (prefixWord ++ tailWord_4170681) baseStart_4170681 baseEnd_4170681 := by
    simpa [prefixWord, tailWord_4170681, baseEnd_4170681] using wordTrace_append hprefix tailTrace_4170681
  have hstable : (prefixWord ++ tailWord_4170681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170681).length < 2 ^ (prefixWord ++ tailWord_4170681).sum := by decide
  have hdescent : baseEnd_4170681 < baseStart_4170681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170688 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_4170688 : Nat := 118140960795 + 4170688 * 2 ^ 59
def prefixEnd_4170688 : Nat := 4983230072969 + 3 ^ 40 * 4170688 * 2
def baseEnd_4170688 : Nat := 2141567603939083397719361

theorem tailTrace_4170688 : CollatzResearch.WordTrace tailWord_4170688 prefixEnd_4170688 2141567603939083397719361 := by
  unfold tailWord_4170688
  simp only [CollatzResearch.WordTrace]
  refine ⟨76058744157158573823332359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101411658876211431764443145 76058744157158573823332359)
  ·
    refine ⟨114088116235737860734998539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76058744157158573823332359 114088116235737860734998539)
    ·
      refine ⟨171132174353606791102497809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114088116235737860734998539 171132174353606791102497809)
      ·
        refine ⟨128349130765205093326873357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171132174353606791102497809 128349130765205093326873357)
        ·
          refine ⟨48130924036951909997577509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128349130765205093326873357 48130924036951909997577509)
          ·
            refine ⟨9024548256928483124545783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48130924036951909997577509 9024548256928483124545783)
            ·
              refine ⟨13536822385392724686818675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024548256928483124545783 13536822385392724686818675)
              ·
                refine ⟨20305233578089087030228013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13536822385392724686818675 20305233578089087030228013)
                ·
                  refine ⟨7614462591783407636335505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20305233578089087030228013 7614462591783407636335505)
                  ·
                    refine ⟨5710846943837555727251629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614462591783407636335505 5710846943837555727251629)
                    ·
                      refine ⟨2141567603939083397719361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710846943837555727251629 2141567603939083397719361)
                      ·
                        rfl

theorem cell23_4170688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_4170688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170688 prefixEnd_4170688 := by exact prefixLift 4170688
  have htrace : WordTrace (prefixWord ++ tailWord_4170688) baseStart_4170688 baseEnd_4170688 := by
    simpa [prefixWord, tailWord_4170688, baseEnd_4170688] using wordTrace_append hprefix tailTrace_4170688
  have hstable : (prefixWord ++ tailWord_4170688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170688).length < 2 ^ (prefixWord ++ tailWord_4170688).sum := by decide
  have hdescent : baseEnd_4170688 < baseStart_4170688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170705 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_4170705 : Nat := 118140960795 + 4170705 * 2 ^ 59
def prefixEnd_4170705 : Nat := 4983230072969 + 3 ^ 40 * 4170705 * 2
def baseEnd_4170705 : Nat := 2141576333110209831206783

theorem tailTrace_4170705 : CollatzResearch.WordTrace tailWord_4170705 prefixEnd_4170705 2141576333110209831206783 := by
  unfold tailWord_4170705
  simp only [CollatzResearch.WordTrace]
  refine ⟨152118108355255559550033569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101412072236837039700022379 152118108355255559550033569)
  ·
    refine ⟨114088581266441669662525177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152118108355255559550033569 114088581266441669662525177)
    ·
      refine ⟨85566435949831252246893883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114088581266441669662525177 85566435949831252246893883)
      ·
        refine ⟨128349653924746878370340825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85566435949831252246893883 128349653924746878370340825)
        ·
          refine ⟨96262240443560158777755619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128349653924746878370340825 96262240443560158777755619)
          ·
            refine ⟨144393360665340238166633429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96262240443560158777755619 144393360665340238166633429)
            ·
              refine ⟨3384219390593911832030471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 144393360665340238166633429 3384219390593911832030471)
              ·
                refine ⟨5076329085890867748045707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384219390593911832030471 5076329085890867748045707)
                ·
                  refine ⟨7614493628836301622068561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076329085890867748045707 7614493628836301622068561)
                  ·
                    refine ⟨5710870221627226216551421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614493628836301622068561 5710870221627226216551421)
                    ·
                      refine ⟨2141576333110209831206783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710870221627226216551421 2141576333110209831206783)
                      ·
                        rfl

theorem cell23_4170705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_4170705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170705 prefixEnd_4170705 := by exact prefixLift 4170705
  have htrace : WordTrace (prefixWord ++ tailWord_4170705) baseStart_4170705 baseEnd_4170705 := by
    simpa [prefixWord, tailWord_4170705, baseEnd_4170705] using wordTrace_append hprefix tailTrace_4170705
  have hstable : (prefixWord ++ tailWord_4170705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170705).length < 2 ^ (prefixWord ++ tailWord_4170705).sum := by decide
  have hdescent : baseEnd_4170705 < baseStart_4170705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170719 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 1, 2, 2]
def baseStart_4170719 : Nat := 118140960795 + 4170719 * 2 ^ 59
def prefixEnd_4170719 : Nat := 4983230072969 + 3 ^ 40 * 4170719 * 2
def baseEnd_4170719 : Nat := 2141583521839372776431719

theorem tailTrace_4170719 : CollatzResearch.WordTrace tailWord_4170719 prefixEnd_4170719 2141583521839372776431719 := by
  unfold tailWord_4170719
  simp only [CollatzResearch.WordTrace]
  refine ⟨152118618977204839941043211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101412412651469893294028807 152118618977204839941043211)
  ·
    refine ⟨228177928465807259911564817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152118618977204839941043211 228177928465807259911564817)
    ·
      refine ⟨171133446349355444933673613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228177928465807259911564817 171133446349355444933673613)
      ·
        refine ⟨64175042381008291850127605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171133446349355444933673613 64175042381008291850127605)
        ·
          refine ⟨6016410223219527360949463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64175042381008291850127605 6016410223219527360949463)
          ·
            refine ⟨9024615334829291041424195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016410223219527360949463 9024615334829291041424195)
            ·
              refine ⟨13536923002243936562136293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024615334829291041424195 13536923002243936562136293)
              ·
                refine ⟨2538173062920738105400555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13536923002243936562136293 2538173062920738105400555)
                ·
                  refine ⟨3807259594381107158100833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538173062920738105400555 3807259594381107158100833)
                  ·
                    refine ⟨2855444695785830368575625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807259594381107158100833 2855444695785830368575625)
                    ·
                      refine ⟨2141583521839372776431719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855444695785830368575625 2141583521839372776431719)
                      ·
                        rfl

theorem cell23_4170719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_4170719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170719 prefixEnd_4170719 := by exact prefixLift 4170719
  have htrace : WordTrace (prefixWord ++ tailWord_4170719) baseStart_4170719 baseEnd_4170719 := by
    simpa [prefixWord, tailWord_4170719, baseEnd_4170719] using wordTrace_append hprefix tailTrace_4170719
  have hstable : (prefixWord ++ tailWord_4170719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170719).length < 2 ^ (prefixWord ++ tailWord_4170719).sum := by decide
  have hdescent : baseEnd_4170719 < baseStart_4170719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170725 : List Nat := [1, 3, 1, 6, 1, 2, 1, 8]
def baseStart_4170725 : Nat := 118140960795 + 4170725 * 2 ^ 59
def prefixEnd_4170725 : Nat := 4983230072969 + 3 ^ 40 * 4170725 * 2
def baseEnd_4170725 : Nat := 79318022323085176035433

theorem tailTrace_4170725 : CollatzResearch.WordTrace tailWord_4170725 prefixEnd_4170725 79318022323085176035433 := by
  unfold tailWord_4170725
  simp only [CollatzResearch.WordTrace]
  refine ⟨152118837815183102965761629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101412558543455401977174419 152118837815183102965761629)
  ·
    refine ⟨57044564180693663612160611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152118837815183102965761629 57044564180693663612160611)
    ·
      refine ⟨85566846271040495418240917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57044564180693663612160611 85566846271040495418240917)
      ·
        refine ⟨4010945918955023222730043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85566846271040495418240917 4010945918955023222730043)
        ·
          refine ⟨6016418878432534834095065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010945918955023222730043 6016418878432534834095065)
          ·
            refine ⟨4512314158824401125571299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016418878432534834095065 4512314158824401125571299)
            ·
              refine ⟨6768471238236601688356949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512314158824401125571299 6768471238236601688356949)
              ·
                refine ⟨79318022323085176035433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6768471238236601688356949 79318022323085176035433)
                ·
                  rfl

theorem cell23_4170725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 8].length) (baseStart_4170725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170725 prefixEnd_4170725 := by exact prefixLift 4170725
  have htrace : WordTrace (prefixWord ++ tailWord_4170725) baseStart_4170725 baseEnd_4170725 := by
    simpa [prefixWord, tailWord_4170725, baseEnd_4170725] using wordTrace_append hprefix tailTrace_4170725
  have hstable : (prefixWord ++ tailWord_4170725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170725).length < 2 ^ (prefixWord ++ tailWord_4170725).sum := by decide
  have hdescent : baseEnd_4170725 < baseStart_4170725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170735 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_4170735 : Nat := 118140960795 + 4170735 * 2 ^ 59
def prefixEnd_4170735 : Nat := 4983230072969 + 3 ^ 40 * 4170735 * 2
def baseEnd_4170735 : Nat := 2141591737529844713831645

theorem tailTrace_4170735 : CollatzResearch.WordTrace tailWord_4170735 prefixEnd_4170735 2141591737529844713831645 := by
  unfold tailWord_4170735
  simp only [CollatzResearch.WordTrace]
  refine ⟨152119202545146874673625659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101412801696764583115750439 152119202545146874673625659)
  ·
    refine ⟨228178803817720312010438489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152119202545146874673625659 228178803817720312010438489)
    ·
      refine ⟨171134102863290234007828867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228178803817720312010438489 171134102863290234007828867)
      ·
        refine ⟨256701154294935351011743301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171134102863290234007828867 256701154294935351011743301)
        ·
          refine ⟨48131466430300378314701869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256701154294935351011743301 48131466430300378314701869)
          ·
            refine ⟨18049299911362641868013201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48131466430300378314701869 18049299911362641868013201)
            ·
              refine ⟨13536974933521981401009901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18049299911362641868013201 13536974933521981401009901)
              ·
                refine ⟨5076365600070743025378713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13536974933521981401009901 5076365600070743025378713)
                ·
                  refine ⟨3807274200053057269034035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076365600070743025378713 3807274200053057269034035)
                  ·
                    refine ⟨5710911300079585903551053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807274200053057269034035 5710911300079585903551053)
                    ·
                      refine ⟨2141591737529844713831645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5710911300079585903551053 2141591737529844713831645)
                      ·
                        rfl

theorem cell23_4170735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_4170735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170735 prefixEnd_4170735 := by exact prefixLift 4170735
  have htrace : WordTrace (prefixWord ++ tailWord_4170735) baseStart_4170735 baseEnd_4170735 := by
    simpa [prefixWord, tailWord_4170735, baseEnd_4170735] using wordTrace_append hprefix tailTrace_4170735
  have hstable : (prefixWord ++ tailWord_4170735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170735).length < 2 ^ (prefixWord ++ tailWord_4170735).sum := by decide
  have hdescent : baseEnd_4170735 < baseStart_4170735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170740 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4170740 : Nat := 118140960795 + 4170740 * 2 ^ 59
def prefixEnd_4170740 : Nat := 4983230072969 + 3 ^ 40 * 4170740 * 2
def baseEnd_4170740 : Nat := 2141594304933117194269123

theorem tailTrace_4170740 : CollatzResearch.WordTrace tailWord_4170740 prefixEnd_4170740 2141594304933117194269123 := by
  unfold tailWord_4170740
  simp only [CollatzResearch.WordTrace]
  refine ⟨76059692455064380263778837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101412923273419173685038449 76059692455064380263778837)
  ·
    refine ⟨3565298083831142824864633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76059692455064380263778837 3565298083831142824864633)
    ·
      refine ⟨2673973562873357118648475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3565298083831142824864633 2673973562873357118648475)
      ·
        refine ⟨4010960344310035677972713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673973562873357118648475 4010960344310035677972713)
        ·
          refine ⟨3008220258232526758479535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010960344310035677972713 3008220258232526758479535)
          ·
            refine ⟨4512330387348790137719303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008220258232526758479535 4512330387348790137719303)
            ·
              refine ⟨6768495581023185206578955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512330387348790137719303 6768495581023185206578955)
              ·
                refine ⟨10152743371534777809868433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768495581023185206578955 10152743371534777809868433)
                ·
                  refine ⟨7614557528651083357401325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10152743371534777809868433 7614557528651083357401325)
                  ·
                    refine ⟨2855459073244156259025497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7614557528651083357401325 2855459073244156259025497)
                    ·
                      refine ⟨2141594304933117194269123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855459073244156259025497 2141594304933117194269123)
                      ·
                        rfl

theorem cell23_4170740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4170740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170740 prefixEnd_4170740 := by exact prefixLift 4170740
  have htrace : WordTrace (prefixWord ++ tailWord_4170740) baseStart_4170740 baseEnd_4170740 := by
    simpa [prefixWord, tailWord_4170740, baseEnd_4170740] using wordTrace_append hprefix tailTrace_4170740
  have hstable : (prefixWord ++ tailWord_4170740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170740).length < 2 ^ (prefixWord ++ tailWord_4170740).sum := by decide
  have hdescent : baseEnd_4170740 < baseStart_4170740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170745 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 1, 3, 2]
def baseStart_4170745 : Nat := 118140960795 + 4170745 * 2 ^ 59
def prefixEnd_4170745 : Nat := 4983230072969 + 3 ^ 40 * 4170745 * 2
def baseEnd_4170745 : Nat := 2141596872336389674706599

theorem tailTrace_4170745 : CollatzResearch.WordTrace tailWord_4170745 prefixEnd_4170745 2141596872336389674706599 := by
  unfold tailWord_4170745
  simp only [CollatzResearch.WordTrace]
  refine ⟨152119567275110646381489689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101413044850073764254326459 152119567275110646381489689)
  ·
    refine ⟨114089675456332984786117267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152119567275110646381489689 114089675456332984786117267)
    ·
      refine ⟨171134513184499477179175901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114089675456332984786117267 171134513184499477179175901)
      ·
        refine ⟨64175442444187303942190963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171134513184499477179175901 64175442444187303942190963)
        ·
          refine ⟨96263163666280955913286445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64175442444187303942190963 96263163666280955913286445)
          ·
            refine ⟨36098686374855358467482417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96263163666280955913286445 36098686374855358467482417)
            ·
              refine ⟨27074014781141518850611813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36098686374855358467482417 27074014781141518850611813)
              ·
                refine ⟨5076377771464034784489715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27074014781141518850611813 5076377771464034784489715)
                ·
                  refine ⟨7614566657196052176734573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076377771464034784489715 7614566657196052176734573)
                  ·
                    refine ⟨2855462496448519566275465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7614566657196052176734573 2855462496448519566275465)
                    ·
                      refine ⟨2141596872336389674706599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855462496448519566275465 2141596872336389674706599)
                      ·
                        rfl

theorem cell23_4170745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_4170745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170745 prefixEnd_4170745 := by exact prefixLift 4170745
  have htrace : WordTrace (prefixWord ++ tailWord_4170745) baseStart_4170745 baseEnd_4170745 := by
    simpa [prefixWord, tailWord_4170745, baseEnd_4170745] using wordTrace_append hprefix tailTrace_4170745
  have hstable : (prefixWord ++ tailWord_4170745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170745).length < 2 ^ (prefixWord ++ tailWord_4170745).sum := by decide
  have hdescent : baseEnd_4170745 < baseStart_4170745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170761 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_4170761 : Nat := 118140960795 + 4170761 * 2 ^ 59
def prefixEnd_4170761 : Nat := 4983230072969 + 3 ^ 40 * 4170761 * 2
def baseEnd_4170761 : Nat := 2141605088026861612106525

theorem tailTrace_4170761 : CollatzResearch.WordTrace tailWord_4170761 prefixEnd_4170761 2141605088026861612106525 := by
  unfold tailWord_4170761
  simp only [CollatzResearch.WordTrace]
  refine ⟨152120150843052681114072137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101413433895368454076048091 152120150843052681114072137)
  ·
    refine ⟨114090113132289510835554103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152120150843052681114072137 114090113132289510835554103)
    ·
      refine ⟨171135169698434266253331155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114090113132289510835554103 171135169698434266253331155)
      ·
        refine ⟨256702754547651399379996733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171135169698434266253331155 256702754547651399379996733)
        ·
          refine ⟨96263532955369274767498775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256702754547651399379996733 96263532955369274767498775)
          ·
            refine ⟨144395299433053912151248163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96263532955369274767498775 144395299433053912151248163)
            ·
              refine ⟨216592949149580868226872245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144395299433053912151248163 216592949149580868226872245)
              ·
                refine ⟨20305588982773206396269273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216592949149580868226872245 20305588982773206396269273)
                ·
                  refine ⟨15229191737079904797201955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20305588982773206396269273 15229191737079904797201955)
                  ·
                    refine ⟨22843787605619857195802933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15229191737079904797201955 22843787605619857195802933)
                    ·
                      refine ⟨2141605088026861612106525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22843787605619857195802933 2141605088026861612106525)
                      ·
                        rfl

theorem cell23_4170761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_4170761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170761 prefixEnd_4170761 := by exact prefixLift 4170761
  have htrace : WordTrace (prefixWord ++ tailWord_4170761) baseStart_4170761 baseEnd_4170761 := by
    simpa [prefixWord, tailWord_4170761, baseEnd_4170761] using wordTrace_append hprefix tailTrace_4170761
  have hstable : (prefixWord ++ tailWord_4170761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170761).length < 2 ^ (prefixWord ++ tailWord_4170761).sum := by decide
  have hdescent : baseEnd_4170761 < baseStart_4170761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170762 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_4170762 : Nat := 118140960795 + 4170762 * 2 ^ 59
def prefixEnd_4170762 : Nat := 4983230072969 + 3 ^ 40 * 4170762 * 2
def baseEnd_4170762 : Nat := 2141605601507516108194021

theorem tailTrace_4170762 : CollatzResearch.WordTrace tailWord_4170762 prefixEnd_4170762 2141605601507516108194021 := by
  unfold tailWord_4170762
  simp only [CollatzResearch.WordTrace]
  refine ⟨38030046829012264571214635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101413458210699372189905693 38030046829012264571214635)
  ·
    refine ⟨57045070243518396856821953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38030046829012264571214635 57045070243518396856821953)
    ·
      refine ⟨42783802682638797642616465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57045070243518396856821953 42783802682638797642616465)
      ·
        refine ⟨32087852011979098231962349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42783802682638797642616465 32087852011979098231962349)
        ·
          refine ⟨12032944504492161836985881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32087852011979098231962349 12032944504492161836985881)
          ·
            refine ⟨9024708378369121377739411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032944504492161836985881 9024708378369121377739411)
            ·
              refine ⟨13537062567553682066609117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9024708378369121377739411 13537062567553682066609117)
              ·
                refine ⟨5076398462832630774978419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13537062567553682066609117 5076398462832630774978419)
                ·
                  refine ⟨7614597694248946162467629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076398462832630774978419 7614597694248946162467629)
                  ·
                    refine ⟨2855474135343354810925361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7614597694248946162467629 2855474135343354810925361)
                    ·
                      refine ⟨2141605601507516108194021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855474135343354810925361 2141605601507516108194021)
                      ·
                        rfl

theorem cell23_4170762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_4170762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170762 prefixEnd_4170762 := by exact prefixLift 4170762
  have htrace : WordTrace (prefixWord ++ tailWord_4170762) baseStart_4170762 baseEnd_4170762 := by
    simpa [prefixWord, tailWord_4170762, baseEnd_4170762] using wordTrace_append hprefix tailTrace_4170762
  have hstable : (prefixWord ++ tailWord_4170762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170762).length < 2 ^ (prefixWord ++ tailWord_4170762).sum := by decide
  have hdescent : baseEnd_4170762 < baseStart_4170762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170798 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_4170798 : Nat := 118140960795 + 4170798 * 2 ^ 59
def prefixEnd_4170798 : Nat := 4983230072969 + 3 ^ 40 * 4170798 * 2
def baseEnd_4170798 : Nat := 237958231867897551927095

theorem tailTrace_4170798 : CollatzResearch.WordTrace tailWord_4170798 prefixEnd_4170798 237958231867897551927095 := by
  unfold tailWord_4170798
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015187542989829554146131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101414333562612424288779365 19015187542989829554146131)
  ·
    refine ⟨28522781314484744331219197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19015187542989829554146131 28522781314484744331219197)
    ·
      refine ⟨10696042992931779124207199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28522781314484744331219197 10696042992931779124207199)
      ·
        refine ⟨16044064489397668686310799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696042992931779124207199 16044064489397668686310799)
        ·
          refine ⟨24066096734096503029466199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044064489397668686310799 24066096734096503029466199)
          ·
            refine ⟨36099145101144754544199299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24066096734096503029466199 36099145101144754544199299)
            ·
              refine ⟨54148717651717131816298949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36099145101144754544199299 54148717651717131816298949)
              ·
                refine ⟨10152884559696962215556053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54148717651717131816298949 10152884559696962215556053)
                ·
                  refine ⟨237958231867897551927095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10152884559696962215556053 237958231867897551927095)
                  ·
                    rfl

theorem cell23_4170798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_4170798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170798 prefixEnd_4170798 := by exact prefixLift 4170798
  have htrace : WordTrace (prefixWord ++ tailWord_4170798) baseStart_4170798 baseEnd_4170798 := by
    simpa [prefixWord, tailWord_4170798, baseEnd_4170798] using wordTrace_append hprefix tailTrace_4170798
  have hstable : (prefixWord ++ tailWord_4170798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170798).length < 2 ^ (prefixWord ++ tailWord_4170798).sum := by decide
  have hdescent : baseEnd_4170798 < baseStart_4170798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170841 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_4170841 : Nat := 118140960795 + 4170841 * 2 ^ 59
def prefixEnd_4170841 : Nat := 4983230072969 + 3 ^ 40 * 4170841 * 2
def baseEnd_4170841 : Nat := 713882055493073766368719

theorem tailTrace_4170841 : CollatzResearch.WordTrace tailWord_4170841 prefixEnd_4170841 713882055493073766368719 := by
  unfold tailWord_4170841
  simp only [CollatzResearch.WordTrace]
  refine ⟨152123068682762854776984377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101415379121841903184656251 152123068682762854776984377)
  ·
    refine ⟨114092301512072141082738283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152123068682762854776984377 114092301512072141082738283)
    ·
      refine ⟨171138452268108211624107425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114092301512072141082738283 171138452268108211624107425)
      ·
        refine ⟨128353839201081158718080569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171138452268108211624107425 128353839201081158718080569)
        ·
          refine ⟨96265379400810869038560427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128353839201081158718080569 96265379400810869038560427)
          ·
            refine ⟨144398069101216303557840641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96265379400810869038560427 144398069101216303557840641)
            ·
              refine ⟨108298551825912227668380481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144398069101216303557840641 108298551825912227668380481)
              ·
                refine ⟨81223913869434170751285361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108298551825912227668380481 81223913869434170751285361)
                ·
                  refine ⟨60917935402075628063464021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81223913869434170751285361 60917935402075628063464021)
                  ·
                    refine ⟨713882055493073766368719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60917935402075628063464021 713882055493073766368719)
                    ·
                      rfl

theorem cell23_4170841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_4170841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170841 prefixEnd_4170841 := by exact prefixLift 4170841
  have htrace : WordTrace (prefixWord ++ tailWord_4170841) baseStart_4170841 baseEnd_4170841 := by
    simpa [prefixWord, tailWord_4170841, baseEnd_4170841] using wordTrace_append hprefix tailTrace_4170841
  have hstable : (prefixWord ++ tailWord_4170841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170841).length < 2 ^ (prefixWord ++ tailWord_4170841).sum := by decide
  have hdescent : baseEnd_4170841 < baseStart_4170841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170848 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_4170848 : Nat := 118140960795 + 4170848 * 2 ^ 59
def prefixEnd_4170848 : Nat := 4983230072969 + 3 ^ 40 * 4170848 * 2
def baseEnd_4170848 : Nat := 2141649760843802771718625

theorem tailTrace_4170848 : CollatzResearch.WordTrace tailWord_4170848 prefixEnd_4170848 2141649760843802771718625 := by
  unfold tailWord_4170848
  simp only [CollatzResearch.WordTrace]
  refine ⟨76061661996868747486244599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101415549329158329981659465 76061661996868747486244599)
  ·
    refine ⟨114092492995303121229366899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76061661996868747486244599 114092492995303121229366899)
    ·
      refine ⟨171138739492954681844050349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114092492995303121229366899 171138739492954681844050349)
      ·
        refine ⟨64177027309858005691518881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171138739492954681844050349 64177027309858005691518881)
        ·
          refine ⟨48132770482393504268639161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64177027309858005691518881 48132770482393504268639161)
          ·
            refine ⟨36099577861795128201479371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48132770482393504268639161 36099577861795128201479371)
            ·
              refine ⟨54149366792692692302219057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36099577861795128201479371 54149366792692692302219057)
              ·
                refine ⟨40612025094519519226664293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54149366792692692302219057 40612025094519519226664293)
                ·
                  refine ⟨7614754705222409854999555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40612025094519519226664293 7614754705222409854999555)
                  ·
                    refine ⟨11422132057833614782499333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7614754705222409854999555 11422132057833614782499333)
                    ·
                      refine ⟨2141649760843802771718625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11422132057833614782499333 2141649760843802771718625)
                      ·
                        rfl

theorem cell23_4170848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_4170848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170848 prefixEnd_4170848 := by exact prefixLift 4170848
  have htrace : WordTrace (prefixWord ++ tailWord_4170848) baseStart_4170848 baseEnd_4170848 := by
    simpa [prefixWord, tailWord_4170848, baseEnd_4170848] using wordTrace_append hprefix tailTrace_4170848
  have hstable : (prefixWord ++ tailWord_4170848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170848).length < 2 ^ (prefixWord ++ tailWord_4170848).sum := by decide
  have hdescent : baseEnd_4170848 < baseStart_4170848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170919 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4170919 : Nat := 118140960795 + 4170919 * 2 ^ 59
def prefixEnd_4170919 : Nat := 4983230072969 + 3 ^ 40 * 4170919 * 2
def baseEnd_4170919 : Nat := 2141686217970271993930799

theorem tailTrace_4170919 : CollatzResearch.WordTrace tailWord_4170919 prefixEnd_4170919 2141686217970271993930799 := by
  unfold tailWord_4170919
  simp only [CollatzResearch.WordTrace]
  refine ⟨152125913576480274098323811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101417275717653516065549207 152125913576480274098323811)
  ·
    refine ⟨228188870364720411147485717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152125913576480274098323811 228188870364720411147485717)
    ·
      refine ⟨10696353298346269272538393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228188870364720411147485717 10696353298346269272538393)
      ·
        refine ⟨8022264973759701954403795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10696353298346269272538393 8022264973759701954403795)
        ·
          refine ⟨12033397460639552931605693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022264973759701954403795 12033397460639552931605693)
          ·
            refine ⟨4512524047739832349352135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12033397460639552931605693 4512524047739832349352135)
            ·
              refine ⟨6768786071609748524028203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512524047739832349352135 6768786071609748524028203)
              ·
                refine ⟨10153179107414622786042305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768786071609748524028203 10153179107414622786042305)
                ·
                  refine ⟨7614884330560967089531729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10153179107414622786042305 7614884330560967089531729)
                  ·
                    refine ⟨5711163247920725317148797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614884330560967089531729 5711163247920725317148797)
                    ·
                      refine ⟨2141686217970271993930799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711163247920725317148797 2141686217970271993930799)
                      ·
                        rfl

theorem cell23_4170919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4170919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170919 prefixEnd_4170919 := by exact prefixLift 4170919
  have htrace : WordTrace (prefixWord ++ tailWord_4170919) baseStart_4170919 baseEnd_4170919 := by
    simpa [prefixWord, tailWord_4170919, baseEnd_4170919] using wordTrace_append hprefix tailTrace_4170919
  have hstable : (prefixWord ++ tailWord_4170919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170919).length < 2 ^ (prefixWord ++ tailWord_4170919).sum := by decide
  have hdescent : baseEnd_4170919 < baseStart_4170919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170935 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 1, 5]
def baseStart_4170935 : Nat := 118140960795 + 4170935 * 2 ^ 59
def prefixEnd_4170935 : Nat := 4983230072969 + 3 ^ 40 * 4170935 * 2
def baseEnd_4170935 : Nat := 713898144553581310443575

theorem tailTrace_4170935 : CollatzResearch.WordTrace tailWord_4170935 prefixEnd_4170935 713898144553581310443575 := by
  unfold tailWord_4170935
  simp only [CollatzResearch.WordTrace]
  refine ⟨152126497144422308830906259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101417664762948205887270839 152126497144422308830906259)
  ·
    refine ⟨228189745716633463246359389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152126497144422308830906259 228189745716633463246359389)
    ·
      refine ⟨85571154643737548717384771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228189745716633463246359389 85571154643737548717384771)
      ·
        refine ⟨128356731965606323076077157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85571154643737548717384771 128356731965606323076077157)
        ·
          refine ⟨24066887243551185576764467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128356731965606323076077157 24066887243551185576764467)
          ·
            refine ⟨36100330865326778365146701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24066887243551185576764467 36100330865326778365146701)
            ·
              refine ⟨13537624074497541886930013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36100330865326778365146701 13537624074497541886930013)
              ·
                refine ⟨5076609027936578207598755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13537624074497541886930013 5076609027936578207598755)
                ·
                  refine ⟨7614913541904867311398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076609027936578207598755 7614913541904867311398133)
                  ·
                    refine ⟨713898144553581310443575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7614913541904867311398133 713898144553581310443575)
                    ·
                      rfl

theorem cell23_4170935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_4170935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170935 prefixEnd_4170935 := by exact prefixLift 4170935
  have htrace : WordTrace (prefixWord ++ tailWord_4170935) baseStart_4170935 baseEnd_4170935 := by
    simpa [prefixWord, tailWord_4170935, baseEnd_4170935] using wordTrace_append hprefix tailTrace_4170935
  have hstable : (prefixWord ++ tailWord_4170935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170935).length < 2 ^ (prefixWord ++ tailWord_4170935).sum := by decide
  have hdescent : baseEnd_4170935 < baseStart_4170935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170975 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_4170975 : Nat := 118140960795 + 4170975 * 2 ^ 59
def prefixEnd_4170975 : Nat := 4983230072969 + 3 ^ 40 * 4170975 * 2
def baseEnd_4170975 : Nat := 2141714972886923774830541

theorem tailTrace_4170975 : CollatzResearch.WordTrace tailWord_4170975 prefixEnd_4170975 2141714972886923774830541 := by
  unfold tailWord_4170975
  simp only [CollatzResearch.WordTrace]
  refine ⟨152127956064277395662362379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101418637376184930441574919 152127956064277395662362379)
  ·
    refine ⟨228191934096416093493543569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152127956064277395662362379 228191934096416093493543569)
    ·
      refine ⟨171143950572312070120157677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228191934096416093493543569 171143950572312070120157677)
      ·
        refine ⟨64178981464617026295059129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171143950572312070120157677 64178981464617026295059129)
        ·
          refine ⟨48134236098462769721294347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64178981464617026295059129 48134236098462769721294347)
          ·
            refine ⟨72201354147694154581941521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48134236098462769721294347 72201354147694154581941521)
            ·
              refine ⟨54151015610770615936456141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72201354147694154581941521 54151015610770615936456141)
              ·
                refine ⟨20306630854038980976171053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54151015610770615936456141 20306630854038980976171053)
                ·
                  refine ⟨7614986570264617866064145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20306630854038980976171053 7614986570264617866064145)
                  ·
                    refine ⟨5711239927698463399548109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7614986570264617866064145 5711239927698463399548109)
                    ·
                      refine ⟨2141714972886923774830541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711239927698463399548109 2141714972886923774830541)
                      ·
                        rfl

theorem cell23_4170975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_4170975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170975 prefixEnd_4170975 := by exact prefixLift 4170975
  have htrace : WordTrace (prefixWord ++ tailWord_4170975) baseStart_4170975 baseEnd_4170975 := by
    simpa [prefixWord, tailWord_4170975, baseEnd_4170975] using wordTrace_append hprefix tailTrace_4170975
  have hstable : (prefixWord ++ tailWord_4170975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170975).length < 2 ^ (prefixWord ++ tailWord_4170975).sum := by decide
  have hdescent : baseEnd_4170975 < baseStart_4170975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4170983 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4170983 : Nat := 118140960795 + 4170983 * 2 ^ 59
def prefixEnd_4170983 : Nat := 4983230072969 + 3 ^ 40 * 4170983 * 2
def baseEnd_4170983 : Nat := 2141719080732159743530505

theorem tailTrace_4170983 : CollatzResearch.WordTrace tailWord_4170983 prefixEnd_4170983 2141719080732159743530505 := by
  unfold tailWord_4170983
  simp only [CollatzResearch.WordTrace]
  refine ⟨152128247848248413028653603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101418831898832275352435735 152128247848248413028653603)
  ·
    refine ⟨228192371772372619542980405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152128247848248413028653603 228192371772372619542980405)
    ·
      refine ⟨21393034853659933082154413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228192371772372619542980405 21393034853659933082154413)
      ·
        refine ⟨8022388070122474905807905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21393034853659933082154413 8022388070122474905807905)
        ·
          refine ⟨6016791052591856179355929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8022388070122474905807905 6016791052591856179355929)
          ·
            refine ⟨4512593289443892134516947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016791052591856179355929 4512593289443892134516947)
            ·
              refine ⟨6768889934165838201775421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512593289443892134516947 6768889934165838201775421)
              ·
                refine ⟨2538333725312189325665783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6768889934165838201775421 2538333725312189325665783)
                ·
                  refine ⟨3807500587968283988498675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538333725312189325665783 3807500587968283988498675)
                  ·
                    refine ⟨5711250881952425982748013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807500587968283988498675 5711250881952425982748013)
                    ·
                      refine ⟨2141719080732159743530505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711250881952425982748013 2141719080732159743530505)
                      ·
                        rfl

theorem cell23_4170983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4170983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4170983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4170983 prefixEnd_4170983 := by exact prefixLift 4170983
  have htrace : WordTrace (prefixWord ++ tailWord_4170983) baseStart_4170983 baseEnd_4170983 := by
    simpa [prefixWord, tailWord_4170983, baseEnd_4170983] using wordTrace_append hprefix tailTrace_4170983
  have hstable : (prefixWord ++ tailWord_4170983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4170983).length < 2 ^ (prefixWord ++ tailWord_4170983).sum := by decide
  have hdescent : baseEnd_4170983 < baseStart_4170983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4170983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171006 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_4171006 : Nat := 118140960795 + 4171006 * 2 ^ 59
def prefixEnd_4171006 : Nat := 4983230072969 + 3 ^ 40 * 4171006 * 2
def baseEnd_4171006 : Nat := 2141730890787213153542899

theorem tailTrace_4171006 : CollatzResearch.WordTrace tailWord_4171006 prefixEnd_4171006 2141730890787213153542899 := by
  unfold tailWord_4171006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016135840895635994592609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101419391151443391971160581 19016135840895635994592609)
  ·
    refine ⟨14262101880671726995944457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19016135840895635994592609 14262101880671726995944457)
    ·
      refine ⟨10696576410503795246958343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14262101880671726995944457 10696576410503795246958343)
      ·
        refine ⟨16044864615755692870437515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10696576410503795246958343 16044864615755692870437515)
        ·
          refine ⟨24067296923633539305656273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16044864615755692870437515 24067296923633539305656273)
          ·
            refine ⟨18050472692725154479242205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24067296923633539305656273 18050472692725154479242205)
            ·
              refine ⟨6768927259771932929715827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18050472692725154479242205 6768927259771932929715827)
              ·
                refine ⟨10153390889657899394573741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768927259771932929715827 10153390889657899394573741)
                ·
                  refine ⟨3807521583621712272965153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10153390889657899394573741 3807521583621712272965153)
                  ·
                    refine ⟨2855641187716284204723865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807521583621712272965153 2855641187716284204723865)
                    ·
                      refine ⟨2141730890787213153542899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855641187716284204723865 2141730890787213153542899)
                      ·
                        rfl

theorem cell23_4171006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_4171006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171006 prefixEnd_4171006 := by exact prefixLift 4171006
  have htrace : WordTrace (prefixWord ++ tailWord_4171006) baseStart_4171006 baseEnd_4171006 := by
    simpa [prefixWord, tailWord_4171006, baseEnd_4171006] using wordTrace_append hprefix tailTrace_4171006
  have hstable : (prefixWord ++ tailWord_4171006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171006).length < 2 ^ (prefixWord ++ tailWord_4171006).sum := by decide
  have hdescent : baseEnd_4171006 < baseStart_4171006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171008 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_4171008 : Nat := 118140960795 + 4171008 * 2 ^ 59
def prefixEnd_4171008 : Nat := 4983230072969 + 3 ^ 40 * 4171008 * 2
def baseEnd_4171008 : Nat := 713910639249507381905963

theorem tailTrace_4171008 : CollatzResearch.WordTrace tailWord_4171008 prefixEnd_4171008 713910639249507381905963 := by
  unfold tailWord_4171008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76064579836578921149156839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101419439782105228198875785 76064579836578921149156839)
  ·
    refine ⟨114096869754868381723735259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76064579836578921149156839 114096869754868381723735259)
    ·
      refine ⟨171145304632302572585602889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114096869754868381723735259 171145304632302572585602889)
      ·
        refine ⟨128358978474226929439202167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171145304632302572585602889 128358978474226929439202167)
        ·
          refine ⟨192538467711340394158803251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128358978474226929439202167 192538467711340394158803251)
          ·
            refine ⟨288807701567010591238204877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192538467711340394158803251 288807701567010591238204877)
            ·
              refine ⟨108302888087628971714326829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288807701567010591238204877 108302888087628971714326829)
              ·
                refine ⟨40613583032860864392872561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108302888087628971714326829 40613583032860864392872561)
                ·
                  refine ⟨30460187274645648294654421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40613583032860864392872561 30460187274645648294654421)
                  ·
                    refine ⟨713910639249507381905963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30460187274645648294654421 713910639249507381905963)
                    ·
                      rfl

theorem cell23_4171008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_4171008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171008 prefixEnd_4171008 := by exact prefixLift 4171008
  have htrace : WordTrace (prefixWord ++ tailWord_4171008) baseStart_4171008 baseEnd_4171008 := by
    simpa [prefixWord, tailWord_4171008, baseEnd_4171008] using wordTrace_append hprefix tailTrace_4171008
  have hstable : (prefixWord ++ tailWord_4171008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171008).length < 2 ^ (prefixWord ++ tailWord_4171008).sum := by decide
  have hdescent : baseEnd_4171008 < baseStart_4171008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171016 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 2, 4]
def baseStart_4171016 : Nat := 118140960795 + 4171016 * 2 ^ 59
def prefixEnd_4171016 : Nat := 4983230072969 + 3 ^ 40 * 4171016 * 2
def baseEnd_4171016 : Nat := 713912008531252704805951

theorem tailTrace_4171016 : CollatzResearch.WordTrace tailWord_4171016 prefixEnd_4171016 713912008531252704805951 := by
  unfold tailWord_4171016
  simp only [CollatzResearch.WordTrace]
  refine ⟨76064725728564429832302451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101419634304752573109736601 76064725728564429832302451)
  ·
    refine ⟨114097088592846644748453677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76064725728564429832302451 114097088592846644748453677)
    ·
      refine ⟨42786408222317491780670129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114097088592846644748453677 42786408222317491780670129)
      ·
        refine ⟨32089806166738118835502597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42786408222317491780670129 32089806166738118835502597)
        ·
          refine ⟨6016838656263397281656737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32089806166738118835502597 6016838656263397281656737)
          ·
            refine ⟨4512628992197547961242553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6016838656263397281656737 4512628992197547961242553)
            ·
              refine ⟨3384471744148160970931915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4512628992197547961242553 3384471744148160970931915)
              ·
                refine ⟨5076707616222241456397873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384471744148160970931915 5076707616222241456397873)
                ·
                  refine ⟨3807530712166681092298405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5076707616222241456397873 3807530712166681092298405)
                  ·
                    refine ⟨713912008531252704805951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3807530712166681092298405 713912008531252704805951)
                    ·
                      rfl

theorem cell23_4171016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_4171016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171016 prefixEnd_4171016 := by exact prefixLift 4171016
  have htrace : WordTrace (prefixWord ++ tailWord_4171016) baseStart_4171016 baseEnd_4171016 := by
    simpa [prefixWord, tailWord_4171016, baseEnd_4171016] using wordTrace_append hprefix tailTrace_4171016
  have hstable : (prefixWord ++ tailWord_4171016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171016).length < 2 ^ (prefixWord ++ tailWord_4171016).sum := by decide
  have hdescent : baseEnd_4171016 < baseStart_4171016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171026 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4171026 : Nat := 118140960795 + 4171026 * 2 ^ 59
def prefixEnd_4171026 : Nat := 4983230072969 + 3 ^ 40 * 4171026 * 2
def baseEnd_4171026 : Nat := 2141741160400303075292807

theorem tailTrace_4171026 : CollatzResearch.WordTrace tailWord_4171026 prefixEnd_4171026 2141741160400303075292807 := by
  unfold tailWord_4171026
  simp only [CollatzResearch.WordTrace]
  refine ⟨38032454046773157843117233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101419877458061754248312621 38032454046773157843117233)
  ·
    refine ⟨28524340535079868382337925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38032454046773157843117233 28524340535079868382337925)
    ·
      refine ⟨5348313850327475321688361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28524340535079868382337925 5348313850327475321688361)
      ·
        refine ⟨4011235387745606491266271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5348313850327475321688361 4011235387745606491266271)
        ·
          refine ⟨6016853081618409736899407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4011235387745606491266271 6016853081618409736899407)
          ·
            refine ⟨9025279622427614605349111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6016853081618409736899407 9025279622427614605349111)
            ·
              refine ⟨13537919433641421908023667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025279622427614605349111 13537919433641421908023667)
              ·
                refine ⟨20306879150462132862035501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13537919433641421908023667 20306879150462132862035501)
                ·
                  refine ⟨7615079681423299823263313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20306879150462132862035501 7615079681423299823263313)
                  ·
                    refine ⟨5711309761067474867447485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615079681423299823263313 5711309761067474867447485)
                    ·
                      refine ⟨2141741160400303075292807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711309761067474867447485 2141741160400303075292807)
                      ·
                        rfl

theorem cell23_4171026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4171026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171026 prefixEnd_4171026 := by exact prefixLift 4171026
  have htrace : WordTrace (prefixWord ++ tailWord_4171026) baseStart_4171026 baseEnd_4171026 := by
    simpa [prefixWord, tailWord_4171026, baseEnd_4171026] using wordTrace_append hprefix tailTrace_4171026
  have hstable : (prefixWord ++ tailWord_4171026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171026).length < 2 ^ (prefixWord ++ tailWord_4171026).sum := by decide
  have hdescent : baseEnd_4171026 < baseStart_4171026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171079 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_4171079 : Nat := 118140960795 + 4171079 * 2 ^ 59
def prefixEnd_4171079 : Nat := 4983230072969 + 3 ^ 40 * 4171079 * 2
def baseEnd_4171079 : Nat := 2141768374874991367930063

theorem tailTrace_4171079 : CollatzResearch.WordTrace tailWord_4171079 prefixEnd_4171079 2141768374874991367930063 := by
  unfold tailWord_4171079
  simp only [CollatzResearch.WordTrace]
  refine ⟨152131749255900621424148291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101421166170600414282765527 152131749255900621424148291)
  ·
    refine ⟨228197623883850932136222437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152131749255900621424148291 228197623883850932136222437)
    ·
      refine ⟨42787054478222049775541707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228197623883850932136222437 42787054478222049775541707)
      ·
        refine ⟨64180581717333074663312561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42787054478222049775541707 64180581717333074663312561)
        ·
          refine ⟨48135436287999805997484421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64180581717333074663312561 48135436287999805997484421)
          ·
            refine ⟨9025394303999963624528329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48135436287999805997484421 9025394303999963624528329)
            ·
              refine ⟨6769045727999972718396247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9025394303999963624528329 6769045727999972718396247)
              ·
                refine ⟨10153568591999959077594371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769045727999972718396247 10153568591999959077594371)
                ·
                  refine ⟨15230352887999938616391557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10153568591999959077594371 15230352887999938616391557)
                  ·
                    refine ⟨2855691166499988490573417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15230352887999938616391557 2855691166499988490573417)
                    ·
                      refine ⟨2141768374874991367930063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855691166499988490573417 2141768374874991367930063)
                      ·
                        rfl

theorem cell23_4171079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_4171079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171079 prefixEnd_4171079 := by exact prefixLift 4171079
  have htrace : WordTrace (prefixWord ++ tailWord_4171079) baseStart_4171079 baseEnd_4171079 := by
    simpa [prefixWord, tailWord_4171079, baseEnd_4171079] using wordTrace_append hprefix tailTrace_4171079
  have hstable : (prefixWord ++ tailWord_4171079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171079).length < 2 ^ (prefixWord ++ tailWord_4171079).sum := by decide
  have hdescent : baseEnd_4171079 < baseStart_4171079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171094 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4171094 : Nat := 118140960795 + 4171094 * 2 ^ 59
def prefixEnd_4171094 : Nat := 4983230072969 + 3 ^ 40 * 4171094 * 2
def baseEnd_4171094 : Nat := 2141776077084808809242495

theorem tailTrace_4171094 : CollatzResearch.WordTrace tailWord_4171094 prefixEnd_4171094 2141776077084808809242495 := by
  unfold tailWord_4171094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9508268521927892436621521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101421530900564185990629557 9508268521927892436621521)
  ·
    refine ⟨7131201391445919327466141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9508268521927892436621521 7131201391445919327466141)
    ·
      refine ⟨2674200521792219747799803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7131201391445919327466141 2674200521792219747799803)
      ·
        refine ⟨4011300782688329621699705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674200521792219747799803 4011300782688329621699705)
        ·
          refine ⟨3008475587016247216274779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011300782688329621699705 3008475587016247216274779)
          ·
            refine ⟨4512713380524370824412169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008475587016247216274779 4512713380524370824412169)
            ·
              refine ⟨3384535035393278118309127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4512713380524370824412169 3384535035393278118309127)
              ·
                refine ⟨5076802553089917177463691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384535035393278118309127 5076802553089917177463691)
                ·
                  refine ⟨7615203829634875766195537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5076802553089917177463691 7615203829634875766195537)
                  ·
                    refine ⟨5711402872226156824646653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7615203829634875766195537 5711402872226156824646653)
                    ·
                      refine ⟨2141776077084808809242495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711402872226156824646653 2141776077084808809242495)
                      ·
                        rfl

theorem cell23_4171094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4171094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171094 prefixEnd_4171094 := by exact prefixLift 4171094
  have htrace : WordTrace (prefixWord ++ tailWord_4171094) baseStart_4171094 baseEnd_4171094 := by
    simpa [prefixWord, tailWord_4171094, baseEnd_4171094] using wordTrace_append hprefix tailTrace_4171094
  have hstable : (prefixWord ++ tailWord_4171094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171094).length < 2 ^ (prefixWord ++ tailWord_4171094).sum := by decide
  have hdescent : baseEnd_4171094 < baseStart_4171094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171166 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_4171166 : Nat := 118140960795 + 4171166 * 2 ^ 59
def prefixEnd_4171166 : Nat := 4983230072969 + 3 ^ 40 * 4171166 * 2
def baseEnd_4171166 : Nat := 713937682563977509180721

theorem tailTrace_4171166 : CollatzResearch.WordTrace tailWord_4171166 prefixEnd_4171166 713937682563977509180721 := by
  unfold tailWord_4171166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19016865300823179410320669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101423281604390290188376901 19016865300823179410320669)
  ·
    refine ⟨7131324487808692278870251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19016865300823179410320669 7131324487808692278870251)
    ·
      refine ⟨10696986731713038418305377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131324487808692278870251 10696986731713038418305377)
      ·
        refine ⟨8022740048784778813729033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10696986731713038418305377 8022740048784778813729033)
        ·
          refine ⟨6017055036588584110296775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8022740048784778813729033 6017055036588584110296775)
          ·
            refine ⟨9025582554882876165445163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017055036588584110296775 9025582554882876165445163)
            ·
              refine ⟨13538373832324314248167745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025582554882876165445163 13538373832324314248167745)
              ·
                refine ⟨10153780374243235686125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13538373832324314248167745 10153780374243235686125809)
                ·
                  refine ⟨7615335280682426764594357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10153780374243235686125809 7615335280682426764594357)
                  ·
                    refine ⟨713937682563977509180721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7615335280682426764594357 713937682563977509180721)
                    ·
                      rfl

theorem cell23_4171166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_4171166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171166 prefixEnd_4171166 := by exact prefixLift 4171166
  have htrace : WordTrace (prefixWord ++ tailWord_4171166) baseStart_4171166 baseEnd_4171166 := by
    simpa [prefixWord, tailWord_4171166, baseEnd_4171166] using wordTrace_append hprefix tailTrace_4171166
  have hstable : (prefixWord ++ tailWord_4171166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171166).length < 2 ^ (prefixWord ++ tailWord_4171166).sum := by decide
  have hdescent : baseEnd_4171166 < baseStart_4171166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171253 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4171253 : Nat := 118140960795 + 4171253 * 2 ^ 59
def prefixEnd_4171253 : Nat := 4983230072969 + 3 ^ 40 * 4171253 * 2
def baseEnd_4171253 : Nat := 2141857720508873687154263

theorem tailTrace_4171253 : CollatzResearch.WordTrace tailWord_4171253 prefixEnd_4171253 2141857720508873687154263 := by
  unfold tailWord_4171253
  simp only [CollatzResearch.WordTrace]
  refine ⟨152138095557270249140982413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101425397038180166093988275 152138095557270249140982413)
  ·
    refine ⟨57051785833976343427868405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152138095557270249140982413 57051785833976343427868405)
    ·
      refine ⟨5348604921935282196362663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57051785833976343427868405 5348604921935282196362663)
      ·
        refine ⟨8022907382902923294543995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348604921935282196362663 8022907382902923294543995)
        ·
          refine ⟨12034361074354384941815993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8022907382902923294543995 12034361074354384941815993)
          ·
            refine ⟨9025770805765788706361995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12034361074354384941815993 9025770805765788706361995)
            ·
              refine ⟨13538656208648683059542993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025770805765788706361995 13538656208648683059542993)
              ·
                refine ⟨10153992156486512294657245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13538656208648683059542993 10153992156486512294657245)
                ·
                  refine ⟨3807747058682442110496467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10153992156486512294657245 3807747058682442110496467)
                  ·
                    refine ⟨5711620588023663165744701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807747058682442110496467 5711620588023663165744701)
                    ·
                      refine ⟨2141857720508873687154263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711620588023663165744701 2141857720508873687154263)
                      ·
                        rfl

theorem cell23_4171253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4171253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171253 prefixEnd_4171253 := by exact prefixLift 4171253
  have htrace : WordTrace (prefixWord ++ tailWord_4171253) baseStart_4171253 baseEnd_4171253 := by
    simpa [prefixWord, tailWord_4171253, baseEnd_4171253] using wordTrace_append hprefix tailTrace_4171253
  have hstable : (prefixWord ++ tailWord_4171253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171253).length < 2 ^ (prefixWord ++ tailWord_4171253).sum := by decide
  have hdescent : baseEnd_4171253 < baseStart_4171253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171276 : List Nat := [2, 2, 1, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_4171276 : Nat := 118140960795 + 4171276 * 2 ^ 59
def prefixEnd_4171276 : Nat := 4983230072969 + 3 ^ 40 * 4171276 * 2
def baseEnd_4171276 : Nat := 2141869530563927097166657

theorem tailTrace_4171276 : CollatzResearch.WordTrace tailWord_4171276 prefixEnd_4171276 2141869530563927097166657 := by
  unfold tailWord_4171276
  simp only [CollatzResearch.WordTrace]
  refine ⟨76069467218093462034534841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101425956290791282712713121 76069467218093462034534841)
  ·
    refine ⟨57052100413570096525901131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76069467218093462034534841 57052100413570096525901131)
    ·
      refine ⟨85578150620355144788851697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57052100413570096525901131 85578150620355144788851697)
      ·
        refine ⟨64183612965266358591638773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85578150620355144788851697 64183612965266358591638773)
        ·
          refine ⟨6017213715493721117966135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64183612965266358591638773 6017213715493721117966135)
          ·
            refine ⟨9025820573240581676949203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017213715493721117966135 9025820573240581676949203)
            ·
              refine ⟨13538730859860872515423805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9025820573240581676949203 13538730859860872515423805)
              ·
                refine ⟨5077024072447827193283927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13538730859860872515423805 5077024072447827193283927)
                ·
                  refine ⟨7615536108671740789925891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077024072447827193283927 7615536108671740789925891)
                  ·
                    refine ⟨11423304163007611184888837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7615536108671740789925891 11423304163007611184888837)
                    ·
                      refine ⟨2141869530563927097166657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11423304163007611184888837 2141869530563927097166657)
                      ·
                        rfl

theorem cell23_4171276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_4171276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171276 prefixEnd_4171276 := by exact prefixLift 4171276
  have htrace : WordTrace (prefixWord ++ tailWord_4171276) baseStart_4171276 baseEnd_4171276 := by
    simpa [prefixWord, tailWord_4171276, baseEnd_4171276] using wordTrace_append hprefix tailTrace_4171276
  have hstable : (prefixWord ++ tailWord_4171276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171276).length < 2 ^ (prefixWord ++ tailWord_4171276).sum := by decide
  have hdescent : baseEnd_4171276 < baseStart_4171276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171293 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4171293 : Nat := 118140960795 + 4171293 * 2 ^ 59
def prefixEnd_4171293 : Nat := 4983230072969 + 3 ^ 40 * 4171293 * 2
def baseEnd_4171293 : Nat := 2141878259735053530654079

theorem tailTrace_4171293 : CollatzResearch.WordTrace tailWord_4171293 prefixEnd_4171293 2141878259735053530654079 := by
  unfold tailWord_4171293
  simp only [CollatzResearch.WordTrace]
  refine ⟨152139554477125335972438533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101426369651416890648292355 152139554477125335972438533)
  ·
    refine ⟨28526166464461000494832225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152139554477125335972438533 28526166464461000494832225)
    ·
      refine ⟨21394624848345750371124169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28526166464461000494832225 21394624848345750371124169)
      ·
        refine ⟨16045968636259312778343127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21394624848345750371124169 16045968636259312778343127)
        ·
          refine ⟨24068952954388969167514691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16045968636259312778343127 24068952954388969167514691)
          ·
            refine ⟨36103429431583453751272037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24068952954388969167514691 36103429431583453751272037)
            ·
              refine ⟨6769393018421897578363507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36103429431583453751272037 6769393018421897578363507)
              ·
                refine ⟨10154089527632846367545261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769393018421897578363507 10154089527632846367545261)
                ·
                  refine ⟨3807783572862317387829473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10154089527632846367545261 3807783572862317387829473)
                  ·
                    refine ⟨2855837679646738040872105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3807783572862317387829473 2855837679646738040872105)
                    ·
                      refine ⟨2141878259735053530654079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855837679646738040872105 2141878259735053530654079)
                      ·
                        rfl

theorem cell23_4171293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4171293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171293 prefixEnd_4171293 := by exact prefixLift 4171293
  have htrace : WordTrace (prefixWord ++ tailWord_4171293) baseStart_4171293 baseEnd_4171293 := by
    simpa [prefixWord, tailWord_4171293, baseEnd_4171293] using wordTrace_append hprefix tailTrace_4171293
  have hstable : (prefixWord ++ tailWord_4171293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171293).length < 2 ^ (prefixWord ++ tailWord_4171293).sum := by decide
  have hdescent : baseEnd_4171293 < baseStart_4171293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171322 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_4171322 : Nat := 118140960795 + 4171322 * 2 ^ 59
def prefixEnd_4171322 : Nat := 4983230072969 + 3 ^ 40 * 4171322 * 2
def baseEnd_4171322 : Nat := 2141893150674033917191445

theorem tailTrace_4171322 : CollatzResearch.WordTrace tailWord_4171322 prefixEnd_4171322 2141893150674033917191445 := by
  unfold tailWord_4171322
  simp only [CollatzResearch.WordTrace]
  refine ⟨38035153048505068481311055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101427074796013515950162813 38035153048505068481311055)
  ·
    refine ⟨57052729572757602721966583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38035153048505068481311055 57052729572757602721966583)
    ·
      refine ⟨85579094359136404082949875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57052729572757602721966583 85579094359136404082949875)
      ·
        refine ⟨128368641538704606124424813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85579094359136404082949875 128368641538704606124424813)
        ·
          refine ⟨48138240577014227296659305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128368641538704606124424813 48138240577014227296659305)
          ·
            refine ⟨36103680432760670472494479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48138240577014227296659305 36103680432760670472494479)
            ·
              refine ⟨54155520649141005708741719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36103680432760670472494479 54155520649141005708741719)
              ·
                refine ⟨81233280973711508563112579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54155520649141005708741719 81233280973711508563112579)
                ·
                  refine ⟨121849921460567262844668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81233280973711508563112579 121849921460567262844668869)
                  ·
                    refine ⟨22846860273856361783375413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121849921460567262844668869 22846860273856361783375413)
                    ·
                      refine ⟨2141893150674033917191445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22846860273856361783375413 2141893150674033917191445)
                      ·
                        rfl

theorem cell23_4171322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_4171322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171322 prefixEnd_4171322 := by exact prefixLift 4171322
  have htrace : WordTrace (prefixWord ++ tailWord_4171322) baseStart_4171322 baseEnd_4171322 := by
    simpa [prefixWord, tailWord_4171322, baseEnd_4171322] using wordTrace_append hprefix tailTrace_4171322
  have hstable : (prefixWord ++ tailWord_4171322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171322).length < 2 ^ (prefixWord ++ tailWord_4171322).sum := by decide
  have hdescent : baseEnd_4171322 < baseStart_4171322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171352 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4171352 : Nat := 118140960795 + 4171352 * 2 ^ 59
def prefixEnd_4171352 : Nat := 4983230072969 + 3 ^ 40 * 4171352 * 2
def baseEnd_4171352 : Nat := 2141908555093668799816307

theorem tailTrace_4171352 : CollatzResearch.WordTrace tailWord_4171352 prefixEnd_4171352 2141908555093668799816307 := by
  unfold tailWord_4171352
  simp only [CollatzResearch.WordTrace]
  refine ⟨76070853191955794524418155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101427804255941059365890873 76070853191955794524418155)
  ·
    refine ⟨114106279787933691786627233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76070853191955794524418155 114106279787933691786627233)
    ·
      refine ⟨85579709840950268839970425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114106279787933691786627233 85579709840950268839970425)
      ·
        refine ⟨64184782380712701629977819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85579709840950268839970425 64184782380712701629977819)
        ·
          refine ⟨96277173571069052444966729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64184782380712701629977819 96277173571069052444966729)
          ·
            refine ⟨72207880178301789333725047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96277173571069052444966729 72207880178301789333725047)
            ·
              refine ⟨108311820267452684000587571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72207880178301789333725047 108311820267452684000587571)
              ·
                refine ⟨162467730401179026000881357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108311820267452684000587571 162467730401179026000881357)
                ·
                  refine ⟨60925398900442134750330509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162467730401179026000881357 60925398900442134750330509)
                  ·
                    refine ⟨22847024587665800531373941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60925398900442134750330509 22847024587665800531373941)
                    ·
                      refine ⟨2141908555093668799816307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22847024587665800531373941 2141908555093668799816307)
                      ·
                        rfl

theorem cell23_4171352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4171352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171352 prefixEnd_4171352 := by exact prefixLift 4171352
  have htrace : WordTrace (prefixWord ++ tailWord_4171352) baseStart_4171352 baseEnd_4171352 := by
    simpa [prefixWord, tailWord_4171352, baseEnd_4171352] using wordTrace_append hprefix tailTrace_4171352
  have hstable : (prefixWord ++ tailWord_4171352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171352).length < 2 ^ (prefixWord ++ tailWord_4171352).sum := by decide
  have hdescent : baseEnd_4171352 < baseStart_4171352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171370 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4171370 : Nat := 118140960795 + 4171370 * 2 ^ 59
def prefixEnd_4171370 : Nat := 4983230072969 + 3 ^ 40 * 4171370 * 2
def baseEnd_4171370 : Nat := 2141917797745449729391225

theorem tailTrace_4171370 : CollatzResearch.WordTrace tailWord_4171370 prefixEnd_4171370 2141917797745449729391225 := by
  unfold tailWord_4171370
  simp only [CollatzResearch.WordTrace]
  refine ⟨38035590724461594530747891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101428241931897585415327709 38035590724461594530747891)
  ·
    refine ⟨57053386086692391796121837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38035590724461594530747891 57053386086692391796121837)
    ·
      refine ⟨21395019782509646923545689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57053386086692391796121837 21395019782509646923545689)
      ·
        refine ⟨16046264836882235192659267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21395019782509646923545689 16046264836882235192659267)
        ·
          refine ⟨24069397255323352788988901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046264836882235192659267 24069397255323352788988901)
          ·
            refine ⟨4513011985373128647935419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24069397255323352788988901 4513011985373128647935419)
            ·
              refine ⟨6769517978059692971903129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513011985373128647935419 6769517978059692971903129)
              ·
                refine ⟨5077138483544769728927347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769517978059692971903129 5077138483544769728927347)
                ·
                  refine ⟨7615707725317154593391021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077138483544769728927347 7615707725317154593391021)
                  ·
                    refine ⟨2855890396993932972521633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7615707725317154593391021 2855890396993932972521633)
                    ·
                      refine ⟨2141917797745449729391225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855890396993932972521633 2141917797745449729391225)
                      ·
                        rfl

theorem cell23_4171370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4171370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171370 prefixEnd_4171370 := by exact prefixLift 4171370
  have htrace : WordTrace (prefixWord ++ tailWord_4171370) baseStart_4171370 baseEnd_4171370 := by
    simpa [prefixWord, tailWord_4171370, baseEnd_4171370] using wordTrace_append hprefix tailTrace_4171370
  have hstable : (prefixWord ++ tailWord_4171370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171370).length < 2 ^ (prefixWord ++ tailWord_4171370).sum := by decide
  have hdescent : baseEnd_4171370 < baseStart_4171370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171372 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 9]
def baseStart_4171372 : Nat := 118140960795 + 4171372 * 2 ^ 59
def prefixEnd_4171372 : Nat := 4983230072969 + 3 ^ 40 * 4171372 * 2
def baseEnd_4171372 : Nat := 237990980522973191285135

theorem tailTrace_4171372 : CollatzResearch.WordTrace tailWord_4171372 prefixEnd_4171372 237990980522973191285135 := by
  unfold tailWord_4171372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76071217921919566232282185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101428290562559421643042913 76071217921919566232282185)
  ·
    refine ⟨57053413441439674674211639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76071217921919566232282185 57053413441439674674211639)
    ·
      refine ⟨85580120162159512011317459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57053413441439674674211639 85580120162159512011317459)
      ·
        refine ⟨128370180243239268016976189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85580120162159512011317459 128370180243239268016976189)
        ·
          refine ⟨48138817591214725506366071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128370180243239268016976189 48138817591214725506366071)
          ·
            refine ⟨72208226386822088259549107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48138817591214725506366071 72208226386822088259549107)
            ·
              refine ⟨108312339580233132389323661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72208226386822088259549107 108312339580233132389323661)
              ·
                refine ⟨40617127342587424645996373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108312339580233132389323661 40617127342587424645996373)
                ·
                  refine ⟨237990980522973191285135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40617127342587424645996373 237990980522973191285135)
                  ·
                    rfl

theorem cell23_4171372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_4171372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171372 prefixEnd_4171372 := by exact prefixLift 4171372
  have htrace : WordTrace (prefixWord ++ tailWord_4171372) baseStart_4171372 baseEnd_4171372 := by
    simpa [prefixWord, tailWord_4171372, baseEnd_4171372] using wordTrace_append hprefix tailTrace_4171372
  have hstable : (prefixWord ++ tailWord_4171372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171372).length < 2 ^ (prefixWord ++ tailWord_4171372).sum := by decide
  have hdescent : baseEnd_4171372 < baseStart_4171372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171416 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4171416 : Nat := 118140960795 + 4171416 * 2 ^ 59
def prefixEnd_4171416 : Nat := 4983230072969 + 3 ^ 40 * 4171416 * 2
def baseEnd_4171416 : Nat := 2141941417855556549416013

theorem tailTrace_4171416 : CollatzResearch.WordTrace tailWord_4171416 prefixEnd_4171416 2141941417855556549416013 := by
  unfold tailWord_4171416
  simp only [CollatzResearch.WordTrace]
  refine ⟨76072020327839863989583051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101429360437119818652777401 76072020327839863989583051)
  ·
    refine ⟨114108030491759795984374577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76072020327839863989583051 114108030491759795984374577)
    ·
      refine ⟨85581022868819846988280933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114108030491759795984374577 85581022868819846988280933)
      ·
        refine ⟨16046441787903721310302675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85581022868819846988280933 16046441787903721310302675)
        ·
          refine ⟨24069662681855581965454013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046441787903721310302675 24069662681855581965454013)
          ·
            refine ⟨9026123505695843237045255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24069662681855581965454013 9026123505695843237045255)
            ·
              refine ⟨13539185258543764855567883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026123505695843237045255 13539185258543764855567883)
              ·
                refine ⟨20308777887815647283351825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539185258543764855567883 20308777887815647283351825)
                ·
                  refine ⟨15231583415861735462513869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20308777887815647283351825 15231583415861735462513869)
                  ·
                    refine ⟨5711843780948150798442701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15231583415861735462513869 5711843780948150798442701)
                    ·
                      refine ⟨2141941417855556549416013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711843780948150798442701 2141941417855556549416013)
                      ·
                        rfl

theorem cell23_4171416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4171416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171416 prefixEnd_4171416 := by exact prefixLift 4171416
  have htrace : WordTrace (prefixWord ++ tailWord_4171416) baseStart_4171416 baseEnd_4171416 := by
    simpa [prefixWord, tailWord_4171416, baseEnd_4171416] using wordTrace_append hprefix tailTrace_4171416
  have hstable : (prefixWord ++ tailWord_4171416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171416).length < 2 ^ (prefixWord ++ tailWord_4171416).sum := by decide
  have hdescent : baseEnd_4171416 < baseStart_4171416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171439 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_4171439 : Nat := 118140960795 + 4171439 * 2 ^ 59
def prefixEnd_4171439 : Nat := 4983230072969 + 3 ^ 40 * 4171439 * 2
def baseEnd_4171439 : Nat := 2141953227910609959428407

theorem tailTrace_4171439 : CollatzResearch.WordTrace tailWord_4171439 prefixEnd_4171439 2141953227910609959428407 := by
  unfold tailWord_4171439
  simp only [CollatzResearch.WordTrace]
  refine ⟨152144879534596402907253371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101429919689730935271502247 152144879534596402907253371)
  ·
    refine ⟨228217319301894604360880057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152144879534596402907253371 228217319301894604360880057)
    ·
      refine ⟨171162989476420953270660043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228217319301894604360880057 171162989476420953270660043)
      ·
        refine ⟨256744484214631429905990065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171162989476420953270660043 256744484214631429905990065)
        ·
          refine ⟨192558363160973572429492549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256744484214631429905990065 192558363160973572429492549)
          ·
            refine ⟨36104693092682544830529853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192558363160973572429492549 36104693092682544830529853)
            ·
              refine ⟨13539259909755954311448695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36104693092682544830529853 13539259909755954311448695)
              ·
                refine ⟨20308889864633931467173043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539259909755954311448695 20308889864633931467173043)
                ·
                  refine ⟨30463334796950897200759565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20308889864633931467173043 30463334796950897200759565)
                  ·
                    refine ⟨11423750548856586450284837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30463334796950897200759565 11423750548856586450284837)
                    ·
                      refine ⟨2141953227910609959428407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11423750548856586450284837 2141953227910609959428407)
                      ·
                        rfl

theorem cell23_4171439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_4171439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171439 prefixEnd_4171439 := by exact prefixLift 4171439
  have htrace : WordTrace (prefixWord ++ tailWord_4171439) baseStart_4171439 baseEnd_4171439 := by
    simpa [prefixWord, tailWord_4171439, baseEnd_4171439] using wordTrace_append hprefix tailTrace_4171439
  have hstable : (prefixWord ++ tailWord_4171439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171439).length < 2 ^ (prefixWord ++ tailWord_4171439).sum := by decide
  have hdescent : baseEnd_4171439 < baseStart_4171439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171456 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2]
def baseStart_4171456 : Nat := 118140960795 + 4171456 * 2 ^ 59
def prefixEnd_4171456 : Nat := 4983230072969 + 3 ^ 40 * 4171456 * 2
def baseEnd_4171456 : Nat := 2141961957081736392915829

theorem tailTrace_4171456 : CollatzResearch.WordTrace tailWord_4171456 prefixEnd_4171456 2141961957081736392915829 := by
  unfold tailWord_4171456
  simp only [CollatzResearch.WordTrace]
  refine ⟨76072749787767407405311111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101430333050356543207081481 76072749787767407405311111)
  ·
    refine ⟨114109124681651111107966667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76072749787767407405311111 114109124681651111107966667)
    ·
      refine ⟨171163687022476666661950001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114109124681651111107966667 171163687022476666661950001)
      ·
        refine ⟨128372765266857499996462501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171163687022476666661950001 128372765266857499996462501)
        ·
          refine ⟨24069893487535781249336719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128372765266857499996462501 24069893487535781249336719)
          ·
            refine ⟨36104840231303671874005079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24069893487535781249336719 36104840231303671874005079)
            ·
              refine ⟨54157260346955507811007619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36104840231303671874005079 54157260346955507811007619)
              ·
                refine ⟨81235890520433261716511429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54157260346955507811007619 81235890520433261716511429)
                ·
                  refine ⟨15231729472581236571845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81235890520433261716511429 15231729472581236571845893)
                  ·
                    refine ⟨2855949276108981857221105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15231729472581236571845893 2855949276108981857221105)
                    ·
                      refine ⟨2141961957081736392915829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2855949276108981857221105 2141961957081736392915829)
                      ·
                        rfl

theorem cell23_4171456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_4171456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171456 prefixEnd_4171456 := by exact prefixLift 4171456
  have htrace : WordTrace (prefixWord ++ tailWord_4171456) baseStart_4171456 baseEnd_4171456 := by
    simpa [prefixWord, tailWord_4171456, baseEnd_4171456] using wordTrace_append hprefix tailTrace_4171456
  have hstable : (prefixWord ++ tailWord_4171456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171456).length < 2 ^ (prefixWord ++ tailWord_4171456).sum := by decide
  have hdescent : baseEnd_4171456 < baseStart_4171456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171523 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 3]
def baseStart_4171523 : Nat := 118140960795 + 4171523 * 2 ^ 59
def prefixEnd_4171523 : Nat := 4983230072969 + 3 ^ 40 * 4171523 * 2
def baseEnd_4171523 : Nat := 2141996360285587630778021

theorem tailTrace_4171523 : CollatzResearch.WordTrace tailWord_4171523 prefixEnd_4171523 2141996360285587630778021 := by
  unfold tailWord_4171523
  simp only [CollatzResearch.WordTrace]
  refine ⟨152147943266292085253311223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101431962177528056835540815 152147943266292085253311223)
  ·
    refine ⟨228221914899438127879966835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152147943266292085253311223 228221914899438127879966835)
    ·
      refine ⟨342332872349157191819950253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228221914899438127879966835 342332872349157191819950253)
      ·
        refine ⟨128374827130933946932481345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342332872349157191819950253 128374827130933946932481345)
        ·
          refine ⟨96281120348200460199361009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128374827130933946932481345 96281120348200460199361009)
          ·
            refine ⟨72210840261150345149520757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96281120348200460199361009 72210840261150345149520757)
            ·
              refine ⟨6769766274482844857767571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72210840261150345149520757 6769766274482844857767571)
              ·
                refine ⟨10154649411724267286651357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6769766274482844857767571 10154649411724267286651357)
                ·
                  refine ⟨3807993529396600232494259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10154649411724267286651357 3807993529396600232494259)
                  ·
                    refine ⟨5711990294094900348741389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3807993529396600232494259 5711990294094900348741389)
                    ·
                      refine ⟨2141996360285587630778021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5711990294094900348741389 2141996360285587630778021)
                      ·
                        rfl

theorem cell23_4171523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_4171523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171523 prefixEnd_4171523 := by exact prefixLift 4171523
  have htrace : WordTrace (prefixWord ++ tailWord_4171523) baseStart_4171523 baseEnd_4171523 := by
    simpa [prefixWord, tailWord_4171523, baseEnd_4171523] using wordTrace_append hprefix tailTrace_4171523
  have hstable : (prefixWord ++ tailWord_4171523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171523).length < 2 ^ (prefixWord ++ tailWord_4171523).sum := by decide
  have hdescent : baseEnd_4171523 < baseStart_4171523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171529 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_4171529 : Nat := 118140960795 + 4171529 * 2 ^ 59
def prefixEnd_4171529 : Nat := 4983230072969 + 3 ^ 40 * 4171529 * 2
def baseEnd_4171529 : Nat := 2141999441169514607302993

theorem tailTrace_4171529 : CollatzResearch.WordTrace tailWord_4171529 prefixEnd_4171529 2141999441169514607302993 := by
  unfold tailWord_4171529
  simp only [CollatzResearch.WordTrace]
  refine ⟨152148162104270348278029641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101432108069513565518686427 152148162104270348278029641)
  ·
    refine ⟨114111121578202761208522231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152148162104270348278029641 114111121578202761208522231)
    ·
      refine ⟨171166682367304141812783347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114111121578202761208522231 171166682367304141812783347)
      ·
        refine ⟨256750023550956212719175021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171166682367304141812783347 256750023550956212719175021)
        ·
          refine ⟨96281258831608579769690633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256750023550956212719175021 96281258831608579769690633)
          ·
            refine ⟨72210944123706434827267975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96281258831608579769690633 72210944123706434827267975)
            ·
              refine ⟨108316416185559652240901963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72210944123706434827267975 108316416185559652240901963)
              ·
                refine ⟨162474624278339478361352945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108316416185559652240901963 162474624278339478361352945)
                ·
                  refine ⟨121855968208754608771014709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162474624278339478361352945 121855968208754608771014709)
                  ·
                    refine ⟨11423997019570744572282629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121855968208754608771014709 11423997019570744572282629)
                    ·
                      refine ⟨2141999441169514607302993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11423997019570744572282629 2141999441169514607302993)
                      ·
                        rfl

theorem cell23_4171529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_4171529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171529 prefixEnd_4171529 := by exact prefixLift 4171529
  have htrace : WordTrace (prefixWord ++ tailWord_4171529) baseStart_4171529 baseEnd_4171529 := by
    simpa [prefixWord, tailWord_4171529, baseEnd_4171529] using wordTrace_append hprefix tailTrace_4171529
  have hstable : (prefixWord ++ tailWord_4171529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171529).length < 2 ^ (prefixWord ++ tailWord_4171529).sum := by decide
  have hdescent : baseEnd_4171529 < baseStart_4171529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171543 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 1, 5]
def baseStart_4171543 : Nat := 118140960795 + 4171543 * 2 ^ 59
def prefixEnd_4171543 : Nat := 4983230072969 + 3 ^ 40 * 4171543 * 2
def baseEnd_4171543 : Nat := 714002209966225850842643

theorem tailTrace_4171543 : CollatzResearch.WordTrace tailWord_4171543 prefixEnd_4171543 714002209966225850842643 := by
  unfold tailWord_4171543
  simp only [CollatzResearch.WordTrace]
  refine ⟨152148672726219628669039283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101432448484146419112692855 152148672726219628669039283)
  ·
    refine ⟨228223009089329443003558925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152148672726219628669039283 228223009089329443003558925)
    ·
      refine ⟨85583628408498541126334597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228223009089329443003558925 85583628408498541126334597)
      ·
        refine ⟨16046930326593476461187737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85583628408498541126334597 16046930326593476461187737)
        ·
          refine ⟨12035197744945107345890803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16046930326593476461187737 12035197744945107345890803)
          ·
            refine ⟨18052796617417661018836205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035197744945107345890803 18052796617417661018836205)
            ·
              refine ⟨6769798731531622882063577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18052796617417661018836205 6769798731531622882063577)
              ·
                refine ⟨5077349048648717161547683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6769798731531622882063577 5077349048648717161547683)
                ·
                  refine ⟨7616023572973075742321525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077349048648717161547683 7616023572973075742321525)
                  ·
                    refine ⟨714002209966225850842643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7616023572973075742321525 714002209966225850842643)
                    ·
                      rfl

theorem cell23_4171543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_4171543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171543 prefixEnd_4171543 := by exact prefixLift 4171543
  have htrace : WordTrace (prefixWord ++ tailWord_4171543) baseStart_4171543 baseEnd_4171543 := by
    simpa [prefixWord, tailWord_4171543, baseEnd_4171543] using wordTrace_append hprefix tailTrace_4171543
  have hstable : (prefixWord ++ tailWord_4171543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171543).length < 2 ^ (prefixWord ++ tailWord_4171543).sum := by decide
  have hdescent : baseEnd_4171543 < baseStart_4171543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171556 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_4171556 : Nat := 118140960795 + 4171556 * 2 ^ 59
def prefixEnd_4171556 : Nat := 4983230072969 + 3 ^ 40 * 4171556 * 2
def baseEnd_4171556 : Nat := 714004435049062000555123

theorem tailTrace_4171556 : CollatzResearch.WordTrace tailWord_4171556 prefixEnd_4171556 714004435049062000555123 := by
  unfold tailWord_4171556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074573437586265944631261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101432764583448354592841681 76074573437586265944631261)
  ·
    refine ⟨28527965039094849729236723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76074573437586265944631261 28527965039094849729236723)
    ·
      refine ⟨42791947558642274593855085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28527965039094849729236723 42791947558642274593855085)
      ·
        refine ⟨16046980334490852972695657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42791947558642274593855085 16046980334490852972695657)
        ·
          refine ⟨12035235250868139729521743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16046980334490852972695657 12035235250868139729521743)
          ·
            refine ⟨18052852876302209594282615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035235250868139729521743 18052852876302209594282615)
            ·
              refine ⟨27079279314453314391423923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18052852876302209594282615 27079279314453314391423923)
              ·
                refine ⟨40618918971679971587135885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27079279314453314391423923 40618918971679971587135885)
                ·
                  refine ⟨15232094614379989345175957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40618918971679971587135885 15232094614379989345175957)
                  ·
                    refine ⟨714004435049062000555123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15232094614379989345175957 714004435049062000555123)
                    ·
                      rfl

theorem cell23_4171556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_4171556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171556 prefixEnd_4171556 := by exact prefixLift 4171556
  have htrace : WordTrace (prefixWord ++ tailWord_4171556) baseStart_4171556 baseEnd_4171556 := by
    simpa [prefixWord, tailWord_4171556, baseEnd_4171556] using wordTrace_append hprefix tailTrace_4171556
  have hstable : (prefixWord ++ tailWord_4171556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171556).length < 2 ^ (prefixWord ++ tailWord_4171556).sum := by decide
  have hdescent : baseEnd_4171556 < baseStart_4171556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171560 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4171560 : Nat := 118140960795 + 4171560 * 2 ^ 59
def prefixEnd_4171560 : Nat := 4983230072969 + 3 ^ 40 * 4171560 * 2
def baseEnd_4171560 : Nat := 714005119689934662005117

theorem tailTrace_4171560 : CollatzResearch.WordTrace tailWord_4171560 prefixEnd_4171560 714005119689934662005117 := by
  unfold tailWord_4171560
  simp only [CollatzResearch.WordTrace]
  refine ⟨76074646383579020286204067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101432861844772027048272089 76074646383579020286204067)
  ·
    refine ⟨114111969575368530429306101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76074646383579020286204067 114111969575368530429306101)
    ·
      refine ⟨10697997147690799727747447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114111969575368530429306101 10697997147690799727747447)
      ·
        refine ⟨16046995721536199591621171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10697997147690799727747447 16046995721536199591621171)
        ·
          refine ⟨24070493582304299387431757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046995721536199591621171 24070493582304299387431757)
          ·
            refine ⟨9026435093364112270286909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24070493582304299387431757 9026435093364112270286909)
            ·
              refine ⟨3384913160011542101357591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9026435093364112270286909 3384913160011542101357591)
              ·
                refine ⟨5077369740017313152036387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3384913160011542101357591 5077369740017313152036387)
                ·
                  refine ⟨7616054610025969728054581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077369740017313152036387 7616054610025969728054581)
                  ·
                    refine ⟨714005119689934662005117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7616054610025969728054581 714005119689934662005117)
                    ·
                      rfl

theorem cell23_4171560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4171560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171560 prefixEnd_4171560 := by exact prefixLift 4171560
  have htrace : WordTrace (prefixWord ++ tailWord_4171560) baseStart_4171560 baseEnd_4171560 := by
    simpa [prefixWord, tailWord_4171560, baseEnd_4171560] using wordTrace_append hprefix tailTrace_4171560
  have hstable : (prefixWord ++ tailWord_4171560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171560).length < 2 ^ (prefixWord ++ tailWord_4171560).sum := by decide
  have hdescent : baseEnd_4171560 < baseStart_4171560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171569 : List Nat := [1, 2, 2, 3, 2, 13]
def baseStart_4171569 : Nat := 118140960795 + 4171569 * 2 ^ 59
def prefixEnd_4171569 : Nat := 4983230072969 + 3 ^ 40 * 4171569 * 2
def baseEnd_4171569 : Nat := 8814897038665409262563

theorem tailTrace_4171569 : CollatzResearch.WordTrace tailWord_4171569 prefixEnd_4171569 8814897038665409262563 := by
  unfold tailWord_4171569
  simp only [CollatzResearch.WordTrace]
  refine ⟨152149621024125435109485761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101433080682750290072990507 152149621024125435109485761)
  ·
    refine ⟨114112215768094076332114321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152149621024125435109485761 114112215768094076332114321)
    ·
      refine ⟨85584161826070557249085741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114112215768094076332114321 85584161826070557249085741)
      ·
        refine ⟨32094060684776458968407153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85584161826070557249085741 32094060684776458968407153)
        ·
          refine ⟨24070545513582344226305365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32094060684776458968407153 24070545513582344226305365)
          ·
            refine ⟨8814897038665409262563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 24070545513582344226305365 8814897038665409262563)
            ·
              rfl

theorem cell23_4171569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 13].length) (baseStart_4171569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171569 prefixEnd_4171569 := by exact prefixLift 4171569
  have htrace : WordTrace (prefixWord ++ tailWord_4171569) baseStart_4171569 baseEnd_4171569 := by
    simpa [prefixWord, tailWord_4171569, baseEnd_4171569] using wordTrace_append hprefix tailTrace_4171569
  have hstable : (prefixWord ++ tailWord_4171569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171569).length < 2 ^ (prefixWord ++ tailWord_4171569).sum := by decide
  have hdescent : baseEnd_4171569 < baseStart_4171569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171574 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4171574 : Nat := 118140960795 + 4171574 * 2 ^ 59
def prefixEnd_4171574 : Nat := 4983230072969 + 3 ^ 40 * 4171574 * 2
def baseEnd_4171574 : Nat := 2142022547798966931240287

theorem tailTrace_4171574 : CollatzResearch.WordTrace tailWord_4171574 prefixEnd_4171574 2142022547798966931240287 := by
  unfold tailWord_4171574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509362711819207560213611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101433202259404880642278517 9509362711819207560213611)
  ·
    refine ⟨14264044067728811340320417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9509362711819207560213611 14264044067728811340320417)
    ·
      refine ⟨10698033050796608505240313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14264044067728811340320417 10698033050796608505240313)
      ·
        refine ⟨8023524788097456378930235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10698033050796608505240313 8023524788097456378930235)
        ·
          refine ⟨12035287182146184568395353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023524788097456378930235 12035287182146184568395353)
          ·
            refine ⟨9026465386609638426296515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12035287182146184568395353 9026465386609638426296515)
            ·
              refine ⟨13539698079914457639444773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9026465386609638426296515 13539698079914457639444773)
              ·
                refine ⟨2538693389983960807395895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13539698079914457639444773 2538693389983960807395895)
                ·
                  refine ⟨3808040084975941211093843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538693389983960807395895 3808040084975941211093843)
                  ·
                    refine ⟨5712060127463911816640765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808040084975941211093843 5712060127463911816640765)
                    ·
                      refine ⟨2142022547798966931240287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712060127463911816640765 2142022547798966931240287)
                      ·
                        rfl

theorem cell23_4171574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4171574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171574 prefixEnd_4171574 := by exact prefixLift 4171574
  have htrace : WordTrace (prefixWord ++ tailWord_4171574) baseStart_4171574 baseEnd_4171574 := by
    simpa [prefixWord, tailWord_4171574, baseEnd_4171574] using wordTrace_append hprefix tailTrace_4171574
  have hstable : (prefixWord ++ tailWord_4171574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171574).length < 2 ^ (prefixWord ++ tailWord_4171574).sum := by decide
  have hdescent : baseEnd_4171574 < baseStart_4171574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171590 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4171590 : Nat := 118140960795 + 4171590 * 2 ^ 59
def prefixEnd_4171590 : Nat := 4983230072969 + 3 ^ 40 * 4171590 * 2
def baseEnd_4171590 : Nat := 714010254496479622880071

theorem tailTrace_4171590 : CollatzResearch.WordTrace tailWord_4171590 prefixEnd_4171590 714010254496479622880071 := by
  unfold tailWord_4171590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754699592407792365500007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101433591304699570464000149 4754699592407792365500007)
  ·
    refine ⟨7132049388611688548250011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4754699592407792365500007 7132049388611688548250011)
    ·
      refine ⟨10698074082917532822375017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132049388611688548250011 10698074082917532822375017)
      ·
        refine ⟨8023555562188149616781263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10698074082917532822375017 8023555562188149616781263)
        ·
          refine ⟨12035333343282224425171895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023555562188149616781263 12035333343282224425171895)
          ·
            refine ⟨18053000014923336637757843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035333343282224425171895 18053000014923336637757843)
            ·
              refine ⟨27079500022385004956636765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18053000014923336637757843 27079500022385004956636765)
              ·
                refine ⟨10154812508394376858738787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27079500022385004956636765 10154812508394376858738787)
                ·
                  refine ⟨15232218762591565288108181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10154812508394376858738787 15232218762591565288108181)
                  ·
                    refine ⟨714010254496479622880071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15232218762591565288108181 714010254496479622880071)
                    ·
                      rfl

theorem cell23_4171590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4171590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171590 prefixEnd_4171590 := by exact prefixLift 4171590
  have htrace : WordTrace (prefixWord ++ tailWord_4171590) baseStart_4171590 baseEnd_4171590 := by
    simpa [prefixWord, tailWord_4171590, baseEnd_4171590] using wordTrace_append hprefix tailTrace_4171590
  have hstable : (prefixWord ++ tailWord_4171590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171590).length < 2 ^ (prefixWord ++ tailWord_4171590).sum := by decide
  have hdescent : baseEnd_4171590 < baseStart_4171590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171597 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4171597 : Nat := 118140960795 + 4171597 * 2 ^ 59
def prefixEnd_4171597 : Nat := 4983230072969 + 3 ^ 40 * 4171597 * 2
def baseEnd_4171597 : Nat := 2142034357854020341252681

theorem tailTrace_4171597 : CollatzResearch.WordTrace tailWord_4171597 prefixEnd_4171597 2142034357854020341252681 := by
  unfold tailWord_4171597
  simp only [CollatzResearch.WordTrace]
  refine ⟨152150642268023995891505045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101433761512015997261003363 152150642268023995891505045)
  ·
    refine ⟨7132061356313624807414299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152150642268023995891505045 7132061356313624807414299)
    ·
      refine ⟨10698092034470437211121449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7132061356313624807414299 10698092034470437211121449)
      ·
        refine ⟨8023569025852827908341087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10698092034470437211121449 8023569025852827908341087)
        ·
          refine ⟨12035353538779241862511631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023569025852827908341087 12035353538779241862511631)
          ·
            refine ⟨18053030308168862793767447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035353538779241862511631 18053030308168862793767447)
            ·
              refine ⟨27079545462253294190651171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18053030308168862793767447 27079545462253294190651171)
              ·
                refine ⟨40619318193379941285976757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27079545462253294190651171 40619318193379941285976757)
                ·
                  refine ⟨3808061080629369495560321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40619318193379941285976757 3808061080629369495560321)
                  ·
                    refine ⟨2856045810472027121670241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808061080629369495560321 2856045810472027121670241)
                    ·
                      refine ⟨2142034357854020341252681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856045810472027121670241 2142034357854020341252681)
                      ·
                        rfl

theorem cell23_4171597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4171597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171597 prefixEnd_4171597 := by exact prefixLift 4171597
  have htrace : WordTrace (prefixWord ++ tailWord_4171597) baseStart_4171597 baseEnd_4171597 := by
    simpa [prefixWord, tailWord_4171597, baseEnd_4171597] using wordTrace_append hprefix tailTrace_4171597
  have hstable : (prefixWord ++ tailWord_4171597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171597).length < 2 ^ (prefixWord ++ tailWord_4171597).sum := by decide
  have hdescent : baseEnd_4171597 < baseStart_4171597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171687 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_4171687 : Nat := 118140960795 + 4171687 * 2 ^ 59
def prefixEnd_4171687 : Nat := 4983230072969 + 3 ^ 40 * 4171687 * 2
def baseEnd_4171687 : Nat := 2142080571112924989127267

theorem tailTrace_4171687 : CollatzResearch.WordTrace tailWord_4171687 prefixEnd_4171687 2142080571112924989127267 := by
  unfold tailWord_4171687
  simp only [CollatzResearch.WordTrace]
  refine ⟨152153924837697941262281315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101435949891798627508187543 152153924837697941262281315)
  ·
    refine ⟨228230887256546911893421973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152153924837697941262281315 228230887256546911893421973)
    ·
      refine ⟨10698322840150636495004155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228230887256546911893421973 10698322840150636495004155)
      ·
        refine ⟨16047484260225954742506233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10698322840150636495004155 16047484260225954742506233)
        ·
          refine ⟨12035613195169466056879675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16047484260225954742506233 12035613195169466056879675)
          ·
            refine ⟨18053419792754199085319513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035613195169466056879675 18053419792754199085319513)
            ·
              refine ⟨13540064844565649313989635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18053419792754199085319513 13540064844565649313989635)
              ·
                refine ⟨20310097266848473970984453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13540064844565649313989635 20310097266848473970984453)
                ·
                  refine ⟨3808143237534088869559585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20310097266848473970984453 3808143237534088869559585)
                  ·
                    refine ⟨2856107428150566652169689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808143237534088869559585 2856107428150566652169689)
                    ·
                      refine ⟨2142080571112924989127267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856107428150566652169689 2142080571112924989127267)
                      ·
                        rfl

theorem cell23_4171687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_4171687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171687 prefixEnd_4171687 := by exact prefixLift 4171687
  have htrace : WordTrace (prefixWord ++ tailWord_4171687) baseStart_4171687 baseEnd_4171687 := by
    simpa [prefixWord, tailWord_4171687, baseEnd_4171687] using wordTrace_append hprefix tailTrace_4171687
  have hstable : (prefixWord ++ tailWord_4171687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171687).length < 2 ^ (prefixWord ++ tailWord_4171687).sum := by decide
  have hdescent : baseEnd_4171687 < baseStart_4171687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171706 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_4171706 : Nat := 118140960795 + 4171706 * 2 ^ 59
def prefixEnd_4171706 : Nat := 4983230072969 + 3 ^ 40 * 4171706 * 2
def baseEnd_4171706 : Nat := 714030109081786804929893

theorem tailTrace_4171706 : CollatzResearch.WordTrace tailWord_4171706 prefixEnd_4171706 714030109081786804929893 := by
  unfold tailWord_4171706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38038654456157276876805743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101436411883086071671481981 38038654456157276876805743)
  ·
    refine ⟨57057981684235915315208615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38038654456157276876805743 57057981684235915315208615)
    ·
      refine ⟨85586972526353872972812923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57057981684235915315208615 85586972526353872972812923)
      ·
        refine ⟨128380458789530809459219385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85586972526353872972812923 128380458789530809459219385)
        ·
          refine ⟨96285344092148107094414539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128380458789530809459219385 96285344092148107094414539)
          ·
            refine ⟨144428016138222160641621809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96285344092148107094414539 144428016138222160641621809)
            ·
              refine ⟨108321012103666620481216357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144428016138222160641621809 108321012103666620481216357)
              ·
                refine ⟨20310189769437491340228067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108321012103666620481216357 20310189769437491340228067)
                ·
                  refine ⟨30465284654156237010342101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20310189769437491340228067 30465284654156237010342101)
                  ·
                    refine ⟨714030109081786804929893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30465284654156237010342101 714030109081786804929893)
                    ·
                      rfl

theorem cell23_4171706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_4171706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171706 prefixEnd_4171706 := by exact prefixLift 4171706
  have htrace : WordTrace (prefixWord ++ tailWord_4171706) baseStart_4171706 baseEnd_4171706 := by
    simpa [prefixWord, tailWord_4171706, baseEnd_4171706] using wordTrace_append hprefix tailTrace_4171706
  have hstable : (prefixWord ++ tailWord_4171706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171706).length < 2 ^ (prefixWord ++ tailWord_4171706).sum := by decide
  have hdescent : baseEnd_4171706 < baseStart_4171706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171723 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 2, 5]
def baseStart_4171723 : Nat := 118140960795 + 4171723 * 2 ^ 59
def prefixEnd_4171723 : Nat := 4983230072969 + 3 ^ 40 * 4171723 * 2
def baseEnd_4171723 : Nat := 714033018805495616092367

theorem tailTrace_4171723 : CollatzResearch.WordTrace tailWord_4171723 prefixEnd_4171723 714033018805495616092367 := by
  unfold tailWord_4171723
  simp only [CollatzResearch.WordTrace]
  refine ⟨152155237865567519410591823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101436825243711679607061215 152155237865567519410591823)
  ·
    refine ⟨228232856798351279115887735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152155237865567519410591823 228232856798351279115887735)
    ·
      refine ⟨342349285197526918673831603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228232856798351279115887735 342349285197526918673831603)
      ·
        refine ⟨513523927796290378010747405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342349285197526918673831603 513523927796290378010747405)
        ·
          refine ⟨192571472923608891754030277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513523927796290378010747405 192571472923608891754030277)
          ·
            refine ⟨36107151173176667203880677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192571472923608891754030277 36107151173176667203880677)
            ·
              refine ⟨6770090844970625100727627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36107151173176667203880677 6770090844970625100727627)
              ·
                refine ⟨10155136267455937651091441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770090844970625100727627 10155136267455937651091441)
                ·
                  refine ⟨7616352200591953238318581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155136267455937651091441 7616352200591953238318581)
                  ·
                    refine ⟨714033018805495616092367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7616352200591953238318581 714033018805495616092367)
                    ·
                      rfl

theorem cell23_4171723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 5].length) (baseStart_4171723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171723 prefixEnd_4171723 := by exact prefixLift 4171723
  have htrace : WordTrace (prefixWord ++ tailWord_4171723) baseStart_4171723 baseEnd_4171723 := by
    simpa [prefixWord, tailWord_4171723, baseEnd_4171723] using wordTrace_append hprefix tailTrace_4171723
  have hstable : (prefixWord ++ tailWord_4171723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171723).length < 2 ^ (prefixWord ++ tailWord_4171723).sum := by decide
  have hdescent : baseEnd_4171723 < baseStart_4171723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171733 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4171733 : Nat := 118140960795 + 4171733 * 2 ^ 59
def prefixEnd_4171733 : Nat := 4983230072969 + 3 ^ 40 * 4171733 * 2
def baseEnd_4171733 : Nat := 2142104191223031809152055

theorem tailTrace_4171733 : CollatzResearch.WordTrace tailWord_4171733 prefixEnd_4171733 2142104191223031809152055 := by
  unfold tailWord_4171733
  simp only [CollatzResearch.WordTrace]
  refine ⟨152155602595531291118455853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101437068397020860745637235 152155602595531291118455853)
  ·
    refine ⟨57058350973324234169420945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152155602595531291118455853 57058350973324234169420945)
    ·
      refine ⟨42793763229993175627065709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57058350973324234169420945 42793763229993175627065709)
      ·
        refine ⟨16047661211247440860149641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42793763229993175627065709 16047661211247440860149641)
        ·
          refine ⟨12035745908435580645112231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16047661211247440860149641 12035745908435580645112231)
          ·
            refine ⟨18053618862653370967668347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035745908435580645112231 18053618862653370967668347)
            ·
              refine ⟨27080428293980056451502521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18053618862653370967668347 27080428293980056451502521)
              ·
                refine ⟨20310321220485042338626891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27080428293980056451502521 20310321220485042338626891)
                ·
                  refine ⟨30465481830727563507940337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20310321220485042338626891 30465481830727563507940337)
                  ·
                    refine ⟨22849111373045672630955253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30465481830727563507940337 22849111373045672630955253)
                    ·
                      refine ⟨2142104191223031809152055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22849111373045672630955253 2142104191223031809152055)
                      ·
                        rfl

theorem cell23_4171733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4171733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171733 prefixEnd_4171733 := by exact prefixLift 4171733
  have htrace : WordTrace (prefixWord ++ tailWord_4171733) baseStart_4171733 baseEnd_4171733 := by
    simpa [prefixWord, tailWord_4171733, baseEnd_4171733] using wordTrace_append hprefix tailTrace_4171733
  have hstable : (prefixWord ++ tailWord_4171733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171733).length < 2 ^ (prefixWord ++ tailWord_4171733).sum := by decide
  have hdescent : baseEnd_4171733 < baseStart_4171733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171763 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3]
def baseStart_4171763 : Nat := 118140960795 + 4171763 * 2 ^ 59
def prefixEnd_4171763 : Nat := 4983230072969 + 3 ^ 40 * 4171763 * 2
def baseEnd_4171763 : Nat := 2142119595642666691776917

theorem tailTrace_4171763 : CollatzResearch.WordTrace tailWord_4171763 prefixEnd_4171763 2142119595642666691776917 := by
  unfold tailWord_4171763
  simp only [CollatzResearch.WordTrace]
  refine ⟨152156696785422606242047943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101437797856948404161365295 152156696785422606242047943)
  ·
    refine ⟨228235045178133909363071915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152156696785422606242047943 228235045178133909363071915)
    ·
      refine ⟨342352567767200864044607873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228235045178133909363071915 342352567767200864044607873)
      ·
        refine ⟨256764425825400648033455905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342352567767200864044607873 256764425825400648033455905)
        ·
          refine ⟨192573319369050486025091929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256764425825400648033455905 192573319369050486025091929)
          ·
            refine ⟨144429989526787864518818947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192573319369050486025091929 144429989526787864518818947)
            ·
              refine ⟨216644984290181796778228421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144429989526787864518818947 216644984290181796778228421)
              ·
                refine ⟨40620934554409086895917829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216644984290181796778228421 40620934554409086895917829)
                ·
                  refine ⟨7616425228951703792984593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40620934554409086895917829 7616425228951703792984593)
                  ·
                    refine ⟨5712318921713777844738445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616425228951703792984593 5712318921713777844738445)
                    ·
                      refine ⟨2142119595642666691776917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712318921713777844738445 2142119595642666691776917)
                      ·
                        rfl

theorem cell23_4171763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_4171763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171763 prefixEnd_4171763 := by exact prefixLift 4171763
  have htrace : WordTrace (prefixWord ++ tailWord_4171763) baseStart_4171763 baseEnd_4171763 := by
    simpa [prefixWord, tailWord_4171763, baseEnd_4171763] using wordTrace_append hprefix tailTrace_4171763
  have hstable : (prefixWord ++ tailWord_4171763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171763).length < 2 ^ (prefixWord ++ tailWord_4171763).sum := by decide
  have hdescent : baseEnd_4171763 < baseStart_4171763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171787 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 1, 4]
def baseStart_4171787 : Nat := 118140960795 + 4171787 * 2 ^ 59
def prefixEnd_4171787 : Nat := 4983230072969 + 3 ^ 40 * 4171787 * 2
def baseEnd_4171787 : Nat := 714043973059458199292269

theorem tailTrace_4171787 : CollatzResearch.WordTrace tailWord_4171787 prefixEnd_4171787 714043973059458199292269 := by
  unfold tailWord_4171787
  simp only [CollatzResearch.WordTrace]
  refine ⟨152157572137335658340921615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101438381424890438893947743 152157572137335658340921615)
  ·
    refine ⟨228236358206003487511382423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152157572137335658340921615 228236358206003487511382423)
    ·
      refine ⟨342354537309005231267073635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228236358206003487511382423 342354537309005231267073635)
      ·
        refine ⟨513531805963507846900610453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342354537309005231267073635 513531805963507846900610453)
        ·
          refine ⟨24071803404539430323466115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 513531805963507846900610453 24071803404539430323466115)
          ·
            refine ⟨36107705106809145485199173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24071803404539430323466115 36107705106809145485199173)
            ·
              refine ⟨6770194707526714778474845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36107705106809145485199173 6770194707526714778474845)
              ·
                refine ⟨2538823015322518041928067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770194707526714778474845 2538823015322518041928067)
                ·
                  refine ⟨3808234522983777062892101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538823015322518041928067 3808234522983777062892101)
                  ·
                    refine ⟨714043973059458199292269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808234522983777062892101 714043973059458199292269)
                    ·
                      rfl

theorem cell23_4171787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 4].length) (baseStart_4171787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171787 prefixEnd_4171787 := by exact prefixLift 4171787
  have htrace : WordTrace (prefixWord ++ tailWord_4171787) baseStart_4171787 baseEnd_4171787 := by
    simpa [prefixWord, tailWord_4171787, baseEnd_4171787] using wordTrace_append hprefix tailTrace_4171787
  have hstable : (prefixWord ++ tailWord_4171787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171787).length < 2 ^ (prefixWord ++ tailWord_4171787).sum := by decide
  have hdescent : baseEnd_4171787 < baseStart_4171787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171820 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_4171820 : Nat := 118140960795 + 4171820 * 2 ^ 59
def prefixEnd_4171820 : Nat := 4983230072969 + 3 ^ 40 * 4171820 * 2
def baseEnd_4171820 : Nat := 2142148864039972968764155

theorem tailTrace_4171820 : CollatzResearch.WordTrace tailWord_4171820 prefixEnd_4171820 2142148864039972968764155 := by
  unfold tailWord_4171820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76079387873108052488436457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101439183830810736651248609 76079387873108052488436457)
  ·
    refine ⟨57059540904831039366327343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76079387873108052488436457 57059540904831039366327343)
    ·
      refine ⟨85589311357246559049491015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57059540904831039366327343 85589311357246559049491015)
      ·
        refine ⟨128383967035869838574236523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85589311357246559049491015 128383967035869838574236523)
        ·
          refine ⟨192575950553804757861354785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128383967035869838574236523 192575950553804757861354785)
          ·
            refine ⟨144431962915353568396016089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192575950553804757861354785 144431962915353568396016089)
            ·
              refine ⟨108323972186515176297012067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144431962915353568396016089 108323972186515176297012067)
              ·
                refine ⟨162485958279772764445518101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108323972186515176297012067 162485958279772764445518101)
                ·
                  refine ⟨7616529294364348333383661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162485958279772764445518101 7616529294364348333383661)
                  ·
                    refine ⟨2856198485386630625018873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7616529294364348333383661 2856198485386630625018873)
                    ·
                      refine ⟨2142148864039972968764155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856198485386630625018873 2142148864039972968764155)
                      ·
                        rfl

theorem cell23_4171820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_4171820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171820 prefixEnd_4171820 := by exact prefixLift 4171820
  have htrace : WordTrace (prefixWord ++ tailWord_4171820) baseStart_4171820 baseEnd_4171820 := by
    simpa [prefixWord, tailWord_4171820, baseEnd_4171820] using wordTrace_append hprefix tailTrace_4171820
  have hstable : (prefixWord ++ tailWord_4171820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171820).length < 2 ^ (prefixWord ++ tailWord_4171820).sum := by decide
  have hdescent : baseEnd_4171820 < baseStart_4171820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171837 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4171837 : Nat := 118140960795 + 4171837 * 2 ^ 59
def prefixEnd_4171837 : Nat := 4983230072969 + 3 ^ 40 * 4171837 * 2
def baseEnd_4171837 : Nat := 2142157593211099402251577

theorem tailTrace_4171837 : CollatzResearch.WordTrace tailWord_4171837 prefixEnd_4171837 2142157593211099402251577 := by
  unfold tailWord_4171837
  simp only [CollatzResearch.WordTrace]
  refine ⟨152159395787154516880241765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101439597191436344586827843 152159395787154516880241765)
  ·
    refine ⟨28529886710091471915045331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152159395787154516880241765 28529886710091471915045331)
    ·
      refine ⟨42794830065137207872567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28529886710091471915045331 42794830065137207872567997)
      ·
        refine ⟨16048061274426452952212999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42794830065137207872567997 16048061274426452952212999)
        ·
          refine ⟨24072091911639679428319499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16048061274426452952212999 24072091911639679428319499)
          ·
            refine ⟨36108137867459519142479249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24072091911639679428319499 36108137867459519142479249)
            ·
              refine ⟨27081103400594639356859437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36108137867459519142479249 27081103400594639356859437)
              ·
                refine ⟨10155413775222989758822289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27081103400594639356859437 10155413775222989758822289)
                ·
                  refine ⟨7616560331417242319116717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155413775222989758822289 7616560331417242319116717)
                  ·
                    refine ⟨2856210124281465869668769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7616560331417242319116717 2856210124281465869668769)
                    ·
                      refine ⟨2142157593211099402251577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856210124281465869668769 2142157593211099402251577)
                      ·
                        rfl

theorem cell23_4171837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4171837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171837 prefixEnd_4171837 := by exact prefixLift 4171837
  have htrace : WordTrace (prefixWord ++ tailWord_4171837) baseStart_4171837 baseEnd_4171837 := by
    simpa [prefixWord, tailWord_4171837, baseEnd_4171837] using wordTrace_append hprefix tailTrace_4171837
  have hstable : (prefixWord ++ tailWord_4171837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171837).length < 2 ^ (prefixWord ++ tailWord_4171837).sum := by decide
  have hdescent : baseEnd_4171837 < baseStart_4171837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171838 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_4171838 : Nat := 118140960795 + 4171838 * 2 ^ 59
def prefixEnd_4171838 : Nat := 4983230072969 + 3 ^ 40 * 4171838 * 2
def baseEnd_4171838 : Nat := 714052702230584632779691

theorem tailTrace_4171838 : CollatzResearch.WordTrace tailWord_4171838 prefixEnd_4171838 714052702230584632779691 := by
  unfold tailWord_4171838
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019929032518861756378521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101439621506767262700685445 19019929032518861756378521)
  ·
    refine ⟨14264946774389146317283891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19019929032518861756378521 14264946774389146317283891)
    ·
      refine ⟨21397420161583719475925837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14264946774389146317283891 21397420161583719475925837)
      ·
        refine ⟨8024032560593894803472189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21397420161583719475925837 8024032560593894803472189)
        ·
          refine ⟨3009012210222710551302071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8024032560593894803472189 3009012210222710551302071)
          ·
            refine ⟨4513518315334065826953107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009012210222710551302071 4513518315334065826953107)
            ·
              refine ⟨6770277473001098740429661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513518315334065826953107 6770277473001098740429661)
              ·
                refine ⟨2538854052375412027661123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770277473001098740429661 2538854052375412027661123)
                ·
                  refine ⟨3808281078563118041491685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538854052375412027661123 3808281078563118041491685)
                  ·
                    refine ⟨714052702230584632779691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808281078563118041491685 714052702230584632779691)
                    ·
                      rfl

theorem cell23_4171838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_4171838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171838 prefixEnd_4171838 := by exact prefixLift 4171838
  have htrace : WordTrace (prefixWord ++ tailWord_4171838) baseStart_4171838 baseEnd_4171838 := by
    simpa [prefixWord, tailWord_4171838, baseEnd_4171838] using wordTrace_append hprefix tailTrace_4171838
  have hstable : (prefixWord ++ tailWord_4171838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171838).length < 2 ^ (prefixWord ++ tailWord_4171838).sum := by decide
  have hdescent : baseEnd_4171838 < baseStart_4171838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171861 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4171861 : Nat := 118140960795 + 4171861 * 2 ^ 59
def prefixEnd_4171861 : Nat := 4983230072969 + 3 ^ 40 * 4171861 * 2
def baseEnd_4171861 : Nat := 2142169916746807308351467

theorem tailTrace_4171861 : CollatzResearch.WordTrace tailWord_4171861 prefixEnd_4171861 2142169916746807308351467 := by
  unfold tailWord_4171861
  simp only [CollatzResearch.WordTrace]
  refine ⟨152160271139067568979115437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101440180759378379319410291 152160271139067568979115437)
  ·
    refine ⟨57060101677150338367168289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152160271139067568979115437 57060101677150338367168289)
    ·
      refine ⟨42795076257862753775376217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57060101677150338367168289 42795076257862753775376217)
      ·
        refine ⟨32096307193397065331532163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42795076257862753775376217 32096307193397065331532163)
        ·
          refine ⟨48144460790095597997298245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32096307193397065331532163 48144460790095597997298245)
          ·
            refine ⟨9027086398142924624493421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48144460790095597997298245 9027086398142924624493421)
            ·
              refine ⟨3385157399303596734185033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9027086398142924624493421 3385157399303596734185033)
              ·
                refine ⟨2538868049477697550638775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3385157399303596734185033 2538868049477697550638775)
                ·
                  refine ⟨3808302074216546325958163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538868049477697550638775 3808302074216546325958163)
                  ·
                    refine ⟨5712453111324819488937245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808302074216546325958163 5712453111324819488937245)
                    ·
                      refine ⟨2142169916746807308351467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712453111324819488937245 2142169916746807308351467)
                      ·
                        rfl

theorem cell23_4171861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4171861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171861 prefixEnd_4171861 := by exact prefixLift 4171861
  have htrace : WordTrace (prefixWord ++ tailWord_4171861) baseStart_4171861 baseEnd_4171861 := by
    simpa [prefixWord, tailWord_4171861, baseEnd_4171861] using wordTrace_append hprefix tailTrace_4171861
  have hstable : (prefixWord ++ tailWord_4171861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171861).length < 2 ^ (prefixWord ++ tailWord_4171861).sum := by decide
  have hdescent : baseEnd_4171861 < baseStart_4171861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171863 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4171863 : Nat := 118140960795 + 4171863 * 2 ^ 59
def prefixEnd_4171863 : Nat := 4983230072969 + 3 ^ 40 * 4171863 * 2
def baseEnd_4171863 : Nat := 2142170943708116300526457

theorem tailTrace_4171863 : CollatzResearch.WordTrace tailWord_4171863 prefixEnd_4171863 2142170943708116300526457 := by
  unfold tailWord_4171863
  simp only [CollatzResearch.WordTrace]
  refine ⟨152160344085060323320688243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101440229390040215547125495 152160344085060323320688243)
  ·
    refine ⟨228240516127590484981032365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152160344085060323320688243 228240516127590484981032365)
    ·
      refine ⟨85590193547846431867887137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228240516127590484981032365 85590193547846431867887137)
      ·
        refine ⟨64192645160884823900915353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85590193547846431867887137 64192645160884823900915353)
        ·
          refine ⟨48144483870663617925686515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64192645160884823900915353 48144483870663617925686515)
          ·
            refine ⟨72216725805995426888529773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48144483870663617925686515 72216725805995426888529773)
            ·
              refine ⟨27081272177248285083198665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72216725805995426888529773 27081272177248285083198665)
              ·
                refine ⟨20310954132936213812398999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27081272177248285083198665 20310954132936213812398999)
                ·
                  refine ⟨30466431199404320718598499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20310954132936213812398999 30466431199404320718598499)
                  ·
                    refine ⟨45699646799106481077897749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30466431199404320718598499 45699646799106481077897749)
                    ·
                      refine ⟨2142170943708116300526457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45699646799106481077897749 2142170943708116300526457)
                      ·
                        rfl

theorem cell23_4171863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4171863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171863 prefixEnd_4171863 := by exact prefixLift 4171863
  have htrace : WordTrace (prefixWord ++ tailWord_4171863) baseStart_4171863 baseEnd_4171863 := by
    simpa [prefixWord, tailWord_4171863, baseEnd_4171863] using wordTrace_append hprefix tailTrace_4171863
  have hstable : (prefixWord ++ tailWord_4171863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171863).length < 2 ^ (prefixWord ++ tailWord_4171863).sum := by decide
  have hdescent : baseEnd_4171863 < baseStart_4171863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171877 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_4171877 : Nat := 118140960795 + 4171877 * 2 ^ 59
def prefixEnd_4171877 : Nat := 4983230072969 + 3 ^ 40 * 4171877 * 2
def baseEnd_4171877 : Nat := 714059377479093081917131

theorem tailTrace_4171877 : CollatzResearch.WordTrace tailWord_4171877 prefixEnd_4171877 714059377479093081917131 := by
  unfold tailWord_4171877
  simp only [CollatzResearch.WordTrace]
  refine ⟨152160854707009603711697885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101440569804673069141131923 152160854707009603711697885)
  ·
    refine ⟨57060320515128601391886707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152160854707009603711697885 57060320515128601391886707)
    ·
      refine ⟨85590480772692902087830061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57060320515128601391886707 85590480772692902087830061)
      ·
        refine ⟨32096430289759838282936273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85590480772692902087830061 32096430289759838282936273)
        ·
          refine ⟨24072322717319878712202205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32096430289759838282936273 24072322717319878712202205)
          ·
            refine ⟨9027121018994954517075827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24072322717319878712202205 9027121018994954517075827)
            ·
              refine ⟨13540681528492431775613741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027121018994954517075827 13540681528492431775613741)
              ·
                refine ⟨5077755573184661915855153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13540681528492431775613741 5077755573184661915855153)
                ·
                  refine ⟨3808316679888496436891365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5077755573184661915855153 3808316679888496436891365)
                  ·
                    refine ⟨714059377479093081917131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808316679888496436891365 714059377479093081917131)
                    ·
                      rfl

theorem cell23_4171877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_4171877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171877 prefixEnd_4171877 := by exact prefixLift 4171877
  have htrace : WordTrace (prefixWord ++ tailWord_4171877) baseStart_4171877 baseEnd_4171877 := by
    simpa [prefixWord, tailWord_4171877, baseEnd_4171877] using wordTrace_append hprefix tailTrace_4171877
  have hstable : (prefixWord ++ tailWord_4171877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171877).length < 2 ^ (prefixWord ++ tailWord_4171877).sum := by decide
  have hdescent : baseEnd_4171877 < baseStart_4171877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171887 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_4171887 : Nat := 118140960795 + 4171887 * 2 ^ 59
def prefixEnd_4171887 : Nat := 4983230072969 + 3 ^ 40 * 4171887 * 2
def baseEnd_4171887 : Nat := 2142183267243824206626347

theorem tailTrace_4171887 : CollatzResearch.WordTrace tailWord_4171887 prefixEnd_4171887 2142183267243824206626347 := by
  unfold tailWord_4171887
  simp only [CollatzResearch.WordTrace]
  refine ⟨152161219436973375419561915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101440812957982250279707943 152161219436973375419561915)
  ·
    refine ⟨228241829155460063129342873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152161219436973375419561915 228241829155460063129342873)
    ·
      refine ⟨171181371866595047347007155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228241829155460063129342873 171181371866595047347007155)
      ·
        refine ⟨256772057799892571020510733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171181371866595047347007155 256772057799892571020510733)
        ·
          refine ⟨96289521674959714132691525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256772057799892571020510733 96289521674959714132691525)
          ·
            refine ⟨18054285314054946399879661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96289521674959714132691525 18054285314054946399879661)
            ·
              refine ⟨6770356992770604899954873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18054285314054946399879661 6770356992770604899954873)
              ·
                refine ⟨5077767744577953674966155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6770356992770604899954873 5077767744577953674966155)
                ·
                  refine ⟨7616651616866930512449233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5077767744577953674966155 7616651616866930512449233)
                  ·
                    refine ⟨5712488712650197884336925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7616651616866930512449233 5712488712650197884336925)
                    ·
                      refine ⟨2142183267243824206626347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712488712650197884336925 2142183267243824206626347)
                      ·
                        rfl

theorem cell23_4171887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_4171887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171887 prefixEnd_4171887 := by exact prefixLift 4171887
  have htrace : WordTrace (prefixWord ++ tailWord_4171887) baseStart_4171887 baseEnd_4171887 := by
    simpa [prefixWord, tailWord_4171887, baseEnd_4171887] using wordTrace_append hprefix tailTrace_4171887
  have hstable : (prefixWord ++ tailWord_4171887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171887).length < 2 ^ (prefixWord ++ tailWord_4171887).sum := by decide
  have hdescent : baseEnd_4171887 < baseStart_4171887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171900 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_4171900 : Nat := 118140960795 + 4171900 * 2 ^ 59
def prefixEnd_4171900 : Nat := 4983230072969 + 3 ^ 40 * 4171900 * 2
def baseEnd_4171900 : Nat := 2142189942492332655763787

theorem tailTrace_4171900 : CollatzResearch.WordTrace tailWord_4171900 prefixEnd_4171900 2142189942492332655763787 := by
  unfold tailWord_4171900
  simp only [CollatzResearch.WordTrace]
  refine ⟨76080846792963139319892577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101441129057284185759856769 76080846792963139319892577)
  ·
    refine ⟨57060635094722354489919433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76080846792963139319892577 57060635094722354489919433)
    ·
      refine ⟨42795476321041765867439575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57060635094722354489919433 42795476321041765867439575)
      ·
        refine ⟨64193214481562648801159363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42795476321041765867439575 64193214481562648801159363)
        ·
          refine ⟨96289821722343973201739045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64193214481562648801159363 96289821722343973201739045)
          ·
            refine ⟨18054341572939494975326071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96289821722343973201739045 18054341572939494975326071)
            ·
              refine ⟨27081512359409242462989107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18054341572939494975326071 27081512359409242462989107)
              ·
                refine ⟨40622268539113863694483661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27081512359409242462989107 40622268539113863694483661)
                ·
                  refine ⟨15233350702167698885431373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40622268539113863694483661 15233350702167698885431373)
                  ·
                    refine ⟨5712506513312887082036765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15233350702167698885431373 5712506513312887082036765)
                    ·
                      refine ⟨2142189942492332655763787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712506513312887082036765 2142189942492332655763787)
                      ·
                        rfl

theorem cell23_4171900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_4171900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171900 prefixEnd_4171900 := by exact prefixLift 4171900
  have htrace : WordTrace (prefixWord ++ tailWord_4171900) baseStart_4171900 baseEnd_4171900 := by
    simpa [prefixWord, tailWord_4171900, baseEnd_4171900] using wordTrace_append hprefix tailTrace_4171900
  have hstable : (prefixWord ++ tailWord_4171900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171900).length < 2 ^ (prefixWord ++ tailWord_4171900).sum := by decide
  have hdescent : baseEnd_4171900 < baseStart_4171900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171918 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4171918 : Nat := 118140960795 + 4171918 * 2 ^ 59
def prefixEnd_4171918 : Nat := 4983230072969 + 3 ^ 40 * 4171918 * 2
def baseEnd_4171918 : Nat := 2142199185144113585338705

theorem tailTrace_4171918 : CollatzResearch.WordTrace tailWord_4171918 prefixEnd_4171918 2142199185144113585338705 := by
  unfold tailWord_4171918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020293762482633464242551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101441566733240711809293605 19020293762482633464242551)
  ·
    refine ⟨28530440643723950196363827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19020293762482633464242551 28530440643723950196363827)
    ·
      refine ⟨42795660965585925294545741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28530440643723950196363827 42795660965585925294545741)
      ·
        refine ⟨16048372862094721985454653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42795660965585925294545741 16048372862094721985454653)
        ·
          refine ⟨6018139823285520744545495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16048372862094721985454653 6018139823285520744545495)
          ·
            refine ⟨9027209734928281116818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018139823285520744545495 9027209734928281116818243)
            ·
              refine ⟨13540814602392421675227365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027209734928281116818243 13540814602392421675227365)
              ·
                refine ⟨2538902737948579064105131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13540814602392421675227365 2538902737948579064105131)
                ·
                  refine ⟨3808354106922868596157697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2538902737948579064105131 3808354106922868596157697)
                  ·
                    refine ⟨2856265580192151447118273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808354106922868596157697 2856265580192151447118273)
                    ·
                      refine ⟨2142199185144113585338705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856265580192151447118273 2142199185144113585338705)
                      ·
                        rfl

theorem cell23_4171918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4171918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171918 prefixEnd_4171918 := by exact prefixLift 4171918
  have htrace : WordTrace (prefixWord ++ tailWord_4171918) baseStart_4171918 baseEnd_4171918 := by
    simpa [prefixWord, tailWord_4171918, baseEnd_4171918] using wordTrace_append hprefix tailTrace_4171918
  have hstable : (prefixWord ++ tailWord_4171918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171918).length < 2 ^ (prefixWord ++ tailWord_4171918).sum := by decide
  have hdescent : baseEnd_4171918 < baseStart_4171918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171924 : List Nat := [2, 4, 2, 3, 1, 2, 1, 8]
def baseStart_4171924 : Nat := 118140960795 + 4171924 * 2 ^ 59
def prefixEnd_4171924 : Nat := 4983230072969 + 3 ^ 40 * 4171924 * 2
def baseEnd_4171924 : Nat := 79340824667705205994951

theorem tailTrace_4171924 : CollatzResearch.WordTrace tailWord_4171924 prefixEnd_4171924 79340824667705205994951 := by
  unfold tailWord_4171924
  simp only [CollatzResearch.WordTrace]
  refine ⟨76081284468919665369329413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101441712625226220492439217 76081284468919665369329413)
  ·
    refine ⟨14265240837922437256749265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76081284468919665369329413 14265240837922437256749265)
    ·
      refine ⟨10698930628441827942561949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14265240837922437256749265 10698930628441827942561949)
      ·
        refine ⟨4012098985665685478460731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10698930628441827942561949 4012098985665685478460731)
        ·
          refine ⟨6018148478498528217691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012098985665685478460731 6018148478498528217691097)
          ·
            refine ⟨4513611358873896163268323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6018148478498528217691097 4513611358873896163268323)
            ·
              refine ⟨6770417038310844244902485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4513611358873896163268323 6770417038310844244902485)
              ·
                refine ⟨79340824667705205994951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6770417038310844244902485 79340824667705205994951)
                ·
                  rfl

theorem cell23_4171924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 8].length) (baseStart_4171924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171924 prefixEnd_4171924 := by exact prefixLift 4171924
  have htrace : WordTrace (prefixWord ++ tailWord_4171924) baseStart_4171924 baseEnd_4171924 := by
    simpa [prefixWord, tailWord_4171924, baseEnd_4171924] using wordTrace_append hprefix tailTrace_4171924
  have hstable : (prefixWord ++ tailWord_4171924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171924).length < 2 ^ (prefixWord ++ tailWord_4171924).sum := by decide
  have hdescent : baseEnd_4171924 < baseStart_4171924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171963 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 9]
def baseStart_4171963 : Nat := 118140960795 + 4171963 * 2 ^ 59
def prefixEnd_4171963 : Nat := 4983230072969 + 3 ^ 40 * 4171963 * 2
def baseEnd_4171963 : Nat := 238024699085951767697333

theorem tailTrace_4171963 : CollatzResearch.WordTrace tailWord_4171963 prefixEnd_4171963 238024699085951767697333 := by
  unfold tailWord_4171963
  simp only [CollatzResearch.WordTrace]
  refine ⟨152163991384698040399328543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101442660923132026932885695 152163991384698040399328543)
  ·
    refine ⟨228245987077047060598992815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152163991384698040399328543 228245987077047060598992815)
    ·
      refine ⟨342368980615570590898489223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228245987077047060598992815 342368980615570590898489223)
      ·
        refine ⟨513553470923355886347733835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342368980615570590898489223 513553470923355886347733835)
        ·
          refine ⟨770330206385033829521600753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513553470923355886347733835 770330206385033829521600753)
          ·
            refine ⟨577747654788775372141200565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770330206385033829521600753 577747654788775372141200565)
            ·
              refine ⟨54163842636447691138237553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 577747654788775372141200565 54163842636447691138237553)
              ·
                refine ⟨40622881977335768353678165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54163842636447691138237553 40622881977335768353678165)
                ·
                  refine ⟨238024699085951767697333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40622881977335768353678165 238024699085951767697333)
                  ·
                    rfl

theorem cell23_4171963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 9].length) (baseStart_4171963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171963 prefixEnd_4171963 := by exact prefixLift 4171963
  have htrace : WordTrace (prefixWord ++ tailWord_4171963) baseStart_4171963 baseEnd_4171963 := by
    simpa [prefixWord, tailWord_4171963, baseEnd_4171963] using wordTrace_append hprefix tailTrace_4171963
  have hstable : (prefixWord ++ tailWord_4171963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171963).length < 2 ^ (prefixWord ++ tailWord_4171963).sum := by decide
  have hdescent : baseEnd_4171963 < baseStart_4171963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4171997 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 7]
def baseStart_4171997 : Nat := 118140960795 + 4171997 * 2 ^ 59
def prefixEnd_4171997 : Nat := 4983230072969 + 3 ^ 40 * 4171997 * 2
def baseEnd_4171997 : Nat := 238026638901757641805649

theorem tailTrace_4171997 : CollatzResearch.WordTrace tailWord_4171997 prefixEnd_4171997 238026638901757641805649 := by
  unfold tailWord_4171997
  simp only [CollatzResearch.WordTrace]
  refine ⟨152165231466574864206066245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101443487644383242804044163 152165231466574864206066245)
  ·
    refine ⟨28530980899982787038637421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152165231466574864206066245 28530980899982787038637421)
    ·
      refine ⟨10699117837493545139489033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28530980899982787038637421 10699117837493545139489033)
      ·
        refine ⟨8024338378120158854616775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10699117837493545139489033 8024338378120158854616775)
        ·
          refine ⟨12036507567180238281925163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024338378120158854616775 12036507567180238281925163)
          ·
            refine ⟨18054761350770357422887745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036507567180238281925163 18054761350770357422887745)
            ·
              refine ⟨13541071013077768067165809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18054761350770357422887745 13541071013077768067165809)
              ·
                refine ⟨10155803259808326050374357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13541071013077768067165809 10155803259808326050374357)
                ·
                  refine ⟨238026638901757641805649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10155803259808326050374357 238026638901757641805649)
                  ·
                    rfl

theorem cell23_4171997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_4171997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4171997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4171997 prefixEnd_4171997 := by exact prefixLift 4171997
  have htrace : WordTrace (prefixWord ++ tailWord_4171997) baseStart_4171997 baseEnd_4171997 := by
    simpa [prefixWord, tailWord_4171997, baseEnd_4171997] using wordTrace_append hprefix tailTrace_4171997
  have hstable : (prefixWord ++ tailWord_4171997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4171997).length < 2 ^ (prefixWord ++ tailWord_4171997).sum := by decide
  have hdescent : baseEnd_4171997 < baseStart_4171997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4171997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172010 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4172010 : Nat := 118140960795 + 4172010 * 2 ^ 59
def prefixEnd_4172010 : Nat := 4983230072969 + 3 ^ 40 * 4172010 * 2
def baseEnd_4172010 : Nat := 714082141788109075129427

theorem tailTrace_4172010 : CollatzResearch.WordTrace tailWord_4172010 prefixEnd_4172010 714082141788109075129427 := by
  unfold tailWord_4172010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041426403881941856572371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101443803743685178284192989 38041426403881941856572371)
  ·
    refine ⟨57062139605822912784858557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38041426403881941856572371 57062139605822912784858557)
    ·
      refine ⟨21398302352183592294321959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57062139605822912784858557 21398302352183592294321959)
      ·
        refine ⟨32097453528275388441482939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398302352183592294321959 32097453528275388441482939)
        ·
          refine ⟨48146180292413082662224409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097453528275388441482939 48146180292413082662224409)
          ·
            refine ⟨36109635219309811996668307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48146180292413082662224409 36109635219309811996668307)
            ·
              refine ⟨54164452828964717995002461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36109635219309811996668307 54164452828964717995002461)
              ·
                refine ⟨20311669810861769248125923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54164452828964717995002461 20311669810861769248125923)
                ·
                  refine ⟨30467504716292653872188885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20311669810861769248125923 30467504716292653872188885)
                  ·
                    refine ⟨714082141788109075129427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30467504716292653872188885 714082141788109075129427)
                    ·
                      rfl

theorem cell23_4172010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4172010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172010 prefixEnd_4172010 := by exact prefixLift 4172010
  have htrace : WordTrace (prefixWord ++ tailWord_4172010) baseStart_4172010 baseEnd_4172010 := by
    simpa [prefixWord, tailWord_4172010, baseEnd_4172010] using wordTrace_append hprefix tailTrace_4172010
  have hstable : (prefixWord ++ tailWord_4172010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172010).length < 2 ^ (prefixWord ++ tailWord_4172010).sum := by decide
  have hdescent : baseEnd_4172010 < baseStart_4172010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172047 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 4, 2]
def baseStart_4172047 : Nat := 118140960795 + 4172047 * 2 ^ 59
def prefixEnd_4172047 : Nat := 4983230072969 + 3 ^ 40 * 4172047 * 2
def baseEnd_4172047 : Nat := 2142265424148543580625611

theorem tailTrace_4172047 : CollatzResearch.WordTrace tailWord_4172047 prefixEnd_4172047 2142265424148543580625611 := by
  unfold tailWord_4172047
  simp only [CollatzResearch.WordTrace]
  refine ⟨152167055116393722745386395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101444703410929148496924263 152167055116393722745386395)
  ·
    refine ⟨228250582674590584118079593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152167055116393722745386395 228250582674590584118079593)
    ·
      refine ⟨171187937005942938088559695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228250582674590584118079593 171187937005942938088559695)
      ·
        refine ⟨256781905508914407132839543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171187937005942938088559695 256781905508914407132839543)
        ·
          refine ⟨385172858263371610699259315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256781905508914407132839543 385172858263371610699259315)
          ·
            refine ⟨577759287395057416048888973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385172858263371610699259315 577759287395057416048888973)
            ·
              refine ⟨216659732773146531018333365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577759287395057416048888973 216659732773146531018333365)
              ·
                refine ⟨20311849947482487282968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216659732773146531018333365 20311849947482487282968753)
                ·
                  refine ⟨15233887460611865462226565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20311849947482487282968753 15233887460611865462226565)
                  ·
                    refine ⟨2856353898864724774167481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15233887460611865462226565 2856353898864724774167481)
                    ·
                      refine ⟨2142265424148543580625611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856353898864724774167481 2142265424148543580625611)
                      ·
                        rfl

theorem cell23_4172047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4, 2].length) (baseStart_4172047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172047 prefixEnd_4172047 := by exact prefixLift 4172047
  have htrace : WordTrace (prefixWord ++ tailWord_4172047) baseStart_4172047 baseEnd_4172047 := by
    simpa [prefixWord, tailWord_4172047, baseEnd_4172047] using wordTrace_append hprefix tailTrace_4172047
  have hstable : (prefixWord ++ tailWord_4172047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172047).length < 2 ^ (prefixWord ++ tailWord_4172047).sum := by decide
  have hdescent : baseEnd_4172047 < baseStart_4172047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172060 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4172060 : Nat := 118140960795 + 4172060 * 2 ^ 59
def prefixEnd_4172060 : Nat := 4983230072969 + 3 ^ 40 * 4172060 * 2
def baseEnd_4172060 : Nat := 2142272099397052029763051

theorem tailTrace_4172060 : CollatzResearch.WordTrace tailWord_4172060 prefixEnd_4172060 2142272099397052029763051 := by
  unfold tailWord_4172060
  simp only [CollatzResearch.WordTrace]
  refine ⟨76083764632673312982804817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101445019510231083977073089 76083764632673312982804817)
  ·
    refine ⟨57062823474504984737103613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76083764632673312982804817 57062823474504984737103613)
    ·
      refine ⟨21398558802939369276413855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57062823474504984737103613 21398558802939369276413855)
      ·
        refine ⟨32097838204409053914620783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398558802939369276413855 32097838204409053914620783)
        ·
          refine ⟨48146757306613580871931175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32097838204409053914620783 48146757306613580871931175)
          ·
            refine ⟨72220135959920371307896763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48146757306613580871931175 72220135959920371307896763)
            ·
              refine ⟨108330203939880556961845145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72220135959920371307896763 108330203939880556961845145)
              ·
                refine ⟨81247652954910417721383859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108330203939880556961845145 81247652954910417721383859)
                ·
                  refine ⟨121871479432365626582075789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81247652954910417721383859 121871479432365626582075789)
                  ·
                    refine ⟨45701804787137109968278421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121871479432365626582075789 45701804787137109968278421)
                    ·
                      refine ⟨2142272099397052029763051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45701804787137109968278421 2142272099397052029763051)
                      ·
                        rfl

theorem cell23_4172060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4172060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172060 prefixEnd_4172060 := by exact prefixLift 4172060
  have htrace : WordTrace (prefixWord ++ tailWord_4172060) baseStart_4172060 baseEnd_4172060 := by
    simpa [prefixWord, tailWord_4172060, baseEnd_4172060] using wordTrace_append hprefix tailTrace_4172060
  have hstable : (prefixWord ++ tailWord_4172060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172060).length < 2 ^ (prefixWord ++ tailWord_4172060).sum := by decide
  have hdescent : baseEnd_4172060 < baseStart_4172060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172064 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4172064 : Nat := 118140960795 + 4172064 * 2 ^ 59
def prefixEnd_4172064 : Nat := 4983230072969 + 3 ^ 40 * 4172064 * 2
def baseEnd_4172064 : Nat := 2142274153319670014113033

theorem tailTrace_4172064 : CollatzResearch.WordTrace tailWord_4172064 prefixEnd_4172064 2142274153319670014113033 := by
  unfold tailWord_4172064
  simp only [CollatzResearch.WordTrace]
  refine ⟨76083837578666067324377623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101445116771554756432503497 76083837578666067324377623)
  ·
    refine ⟨114125756367999100986566435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76083837578666067324377623 114125756367999100986566435)
    ·
      refine ⟨171188634551998651479849653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114125756367999100986566435 171188634551998651479849653)
      ·
        refine ⟨16048934489249873576235905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171188634551998651479849653 16048934489249873576235905)
        ·
          refine ⟨12036700866937405182176929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16048934489249873576235905 12036700866937405182176929)
          ·
            refine ⟨9027525650203053886632697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036700866937405182176929 9027525650203053886632697)
            ·
              refine ⟨6770644237652290414974523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027525650203053886632697 6770644237652290414974523)
              ·
                refine ⟨10155966356478435622461785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770644237652290414974523 10155966356478435622461785)
                ·
                  refine ⟨7616974767358826716846339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10155966356478435622461785 7616974767358826716846339)
                  ·
                    refine ⟨11425462151038240075269509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7616974767358826716846339 11425462151038240075269509)
                    ·
                      refine ⟨2142274153319670014113033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11425462151038240075269509 2142274153319670014113033)
                      ·
                        rfl

theorem cell23_4172064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4172064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172064 prefixEnd_4172064 := by exact prefixLift 4172064
  have htrace : WordTrace (prefixWord ++ tailWord_4172064) baseStart_4172064 baseEnd_4172064 := by
    simpa [prefixWord, tailWord_4172064, baseEnd_4172064] using wordTrace_append hprefix tailTrace_4172064
  have hstable : (prefixWord ++ tailWord_4172064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172064).length < 2 ^ (prefixWord ++ tailWord_4172064).sum := by decide
  have hdescent : baseEnd_4172064 < baseStart_4172064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172114 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_4172114 : Nat := 118140960795 + 4172114 * 2 ^ 59
def prefixEnd_4172114 : Nat := 4983230072969 + 3 ^ 40 * 4172114 * 2
def baseEnd_4172114 : Nat := 2142299827352394818487803

theorem tailTrace_4172114 : CollatzResearch.WordTrace tailWord_4172114 prefixEnd_4172114 2142299827352394818487803 := by
  unfold tailWord_4172114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38042374701787748297018849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101446332538100662125383597 38042374701787748297018849)
  ·
    refine ⟨28531781026340811222764137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38042374701787748297018849 28531781026340811222764137)
    ·
      refine ⟨21398835769755608417073103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28531781026340811222764137 21398835769755608417073103)
      ·
        refine ⟨32098253654633412625609655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21398835769755608417073103 32098253654633412625609655)
        ·
          refine ⟨48147380481950118938414483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32098253654633412625609655 48147380481950118938414483)
          ·
            refine ⟨72221070722925178407621725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48147380481950118938414483 72221070722925178407621725)
            ·
              refine ⟨27082901521096941902858147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72221070722925178407621725 27082901521096941902858147)
              ·
                refine ⟨40624352281645412854287221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27082901521096941902858147 40624352281645412854287221)
                ·
                  refine ⟨3808533026404257455089427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40624352281645412854287221 3808533026404257455089427)
                  ·
                    refine ⟨5712799539606386182634141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3808533026404257455089427 5712799539606386182634141)
                    ·
                      refine ⟨2142299827352394818487803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712799539606386182634141 2142299827352394818487803)
                      ·
                        rfl

theorem cell23_4172114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_4172114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172114 prefixEnd_4172114 := by exact prefixLift 4172114
  have htrace : WordTrace (prefixWord ++ tailWord_4172114) baseStart_4172114 baseEnd_4172114 := by
    simpa [prefixWord, tailWord_4172114, baseEnd_4172114] using wordTrace_append hprefix tailTrace_4172114
  have hstable : (prefixWord ++ tailWord_4172114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172114).length < 2 ^ (prefixWord ++ tailWord_4172114).sum := by decide
  have hdescent : baseEnd_4172114 < baseStart_4172114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172147 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 4, 4]
def baseStart_4172147 : Nat := 118140960795 + 4172147 * 2 ^ 59
def prefixEnd_4172147 : Nat := 4983230072969 + 3 ^ 40 * 4172147 * 2
def baseEnd_4172147 : Nat := 714105590737997729791717

theorem tailTrace_4172147 : CollatzResearch.WordTrace tailWord_4172147 prefixEnd_4172147 714105590737997729791717 := by
  unfold tailWord_4172147
  simp only [CollatzResearch.WordTrace]
  refine ⟨152170702416031439824026695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101447134944020959882684463 152170702416031439824026695)
  ·
    refine ⟨228256053624047159736040043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152170702416031439824026695 228256053624047159736040043)
    ·
      refine ⟨342384080436070739604060065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228256053624047159736040043 342384080436070739604060065)
      ·
        refine ⟨256788060327053054703045049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342384080436070739604060065 256788060327053054703045049)
        ·
          refine ⟨192591045245289791027283787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256788060327053054703045049 192591045245289791027283787)
          ·
            refine ⟨288886567867934686540925681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192591045245289791027283787 288886567867934686540925681)
            ·
              refine ⟨216664925900951014905694261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288886567867934686540925681 216664925900951014905694261)
              ·
                refine ⟨20312336803214157647408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216664925900951014905694261 20312336803214157647408837)
                ·
                  refine ⟨3808563150602654558889157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20312336803214157647408837 3808563150602654558889157)
                  ·
                    refine ⟨714105590737997729791717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3808563150602654558889157 714105590737997729791717)
                    ·
                      rfl

theorem cell23_4172147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 4].length) (baseStart_4172147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172147 prefixEnd_4172147 := by exact prefixLift 4172147
  have htrace : WordTrace (prefixWord ++ tailWord_4172147) baseStart_4172147 baseEnd_4172147 := by
    simpa [prefixWord, tailWord_4172147, baseEnd_4172147] using wordTrace_append hprefix tailTrace_4172147
  have hstable : (prefixWord ++ tailWord_4172147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172147).length < 2 ^ (prefixWord ++ tailWord_4172147).sum := by decide
  have hdescent : baseEnd_4172147 < baseStart_4172147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172157 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_4172157 : Nat := 118140960795 + 4172157 * 2 ^ 59
def prefixEnd_4172157 : Nat := 4983230072969 + 3 ^ 40 * 4172157 * 2
def baseEnd_4172157 : Nat := 2142321907020538150250105

theorem tailTrace_4172157 : CollatzResearch.WordTrace tailWord_4172157 prefixEnd_4172157 2142321907020538150250105 := by
  unfold tailWord_4172157
  simp only [CollatzResearch.WordTrace]
  refine ⟨152171067145995211531890725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101447378097330141021260483 152171067145995211531890725)
  ·
    refine ⟨28532075089874102162229511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152171067145995211531890725 28532075089874102162229511)
    ·
      refine ⟨42798112634811153243344267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28532075089874102162229511 42798112634811153243344267)
      ·
        refine ⟨64197168952216729865016401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42798112634811153243344267 64197168952216729865016401)
        ·
          refine ⟨48147876714162547398762301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64197168952216729865016401 48147876714162547398762301)
          ·
            refine ⟨18055453767810955274535863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48147876714162547398762301 18055453767810955274535863)
            ·
              refine ⟨27083180651716432911803795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18055453767810955274535863 27083180651716432911803795)
              ·
                refine ⟨40624770977574649367705693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27083180651716432911803795 40624770977574649367705693)
                ·
                  refine ⟨15234289116590493512889635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40624770977574649367705693 15234289116590493512889635)
                  ·
                    refine ⟨22851433674885740269334453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15234289116590493512889635 22851433674885740269334453)
                    ·
                      refine ⟨2142321907020538150250105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22851433674885740269334453 2142321907020538150250105)
                      ·
                        rfl

theorem cell23_4172157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_4172157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172157 prefixEnd_4172157 := by exact prefixLift 4172157
  have htrace : WordTrace (prefixWord ++ tailWord_4172157) baseStart_4172157 baseEnd_4172157 := by
    simpa [prefixWord, tailWord_4172157, baseEnd_4172157] using wordTrace_append hprefix tailTrace_4172157
  have hstable : (prefixWord ++ tailWord_4172157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172157).length < 2 ^ (prefixWord ++ tailWord_4172157).sum := by decide
  have hdescent : baseEnd_4172157 < baseStart_4172157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172167 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4172167 : Nat := 118140960795 + 4172167 * 2 ^ 59
def prefixEnd_4172167 : Nat := 4983230072969 + 3 ^ 40 * 4172167 * 2
def baseEnd_4172167 : Nat := 2142327041827083111125059

theorem tailTrace_4172167 : CollatzResearch.WordTrace tailWord_4172167 prefixEnd_4172167 2142327041827083111125059 := by
  unfold tailWord_4172167
  simp only [CollatzResearch.WordTrace]
  refine ⟨152171431875958983239754755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101447621250639322159836503 152171431875958983239754755)
  ·
    refine ⟨228257147813938474859632133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152171431875958983239754755 228257147813938474859632133)
    ·
      refine ⟨42798215215113464036181025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228257147813938474859632133 42798215215113464036181025)
      ·
        refine ⟨32098661411335098027135769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42798215215113464036181025 32098661411335098027135769)
        ·
          refine ⟨24073996058501323520351827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32098661411335098027135769 24073996058501323520351827)
          ·
            refine ⟨36110994087751985280527741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24073996058501323520351827 36110994087751985280527741)
            ·
              refine ⟨13541622782906994480197903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36110994087751985280527741 13541622782906994480197903)
              ·
                refine ⟨20312434174360491720296855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541622782906994480197903 20312434174360491720296855)
                ·
                  refine ⟨30468651261540737580445283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20312434174360491720296855 30468651261540737580445283)
                  ·
                    refine ⟨45702976892311106370667925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30468651261540737580445283 45702976892311106370667925)
                    ·
                      refine ⟨2142327041827083111125059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45702976892311106370667925 2142327041827083111125059)
                      ·
                        rfl

theorem cell23_4172167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4172167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172167 prefixEnd_4172167 := by exact prefixLift 4172167
  have htrace : WordTrace (prefixWord ++ tailWord_4172167) baseStart_4172167 baseEnd_4172167 := by
    simpa [prefixWord, tailWord_4172167, baseEnd_4172167] using wordTrace_append hprefix tailTrace_4172167
  have hstable : (prefixWord ++ tailWord_4172167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172167).length < 2 ^ (prefixWord ++ tailWord_4172167).sum := by decide
  have hdescent : baseEnd_4172167 < baseStart_4172167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172171 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 3, 2, 2]
def baseStart_4172171 : Nat := 118140960795 + 4172171 * 2 ^ 59
def prefixEnd_4172171 : Nat := 4983230072969 + 3 ^ 40 * 4172171 * 2
def baseEnd_4172171 : Nat := 2142329095749701095475041

theorem tailTrace_4172171 : CollatzResearch.WordTrace tailWord_4172171 prefixEnd_4172171 2142329095749701095475041 := by
  unfold tailWord_4172171
  simp only [CollatzResearch.WordTrace]
  refine ⟨152171577767944491922900367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101447718511962994615266911 152171577767944491922900367)
  ·
    refine ⟨228257366651916737884350551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152171577767944491922900367 228257366651916737884350551)
    ·
      refine ⟨342386049977875106826525827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228257366651916737884350551 342386049977875106826525827)
      ·
        refine ⟨513579074966812660239788741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342386049977875106826525827 513579074966812660239788741)
        ·
          refine ⟨96296076556277373794960389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513579074966812660239788741 96296076556277373794960389)
          ·
            refine ⟨18055514354302007586555073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96296076556277373794960389 18055514354302007586555073)
            ·
              refine ⟨13541635765726505689916305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18055514354302007586555073 13541635765726505689916305)
              ·
                refine ⟨10156226824294879267437229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13541635765726505689916305 10156226824294879267437229)
                ·
                  refine ⟨3808585059110579725288961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10156226824294879267437229 3808585059110579725288961)
                  ·
                    refine ⟨2856438794332934793966721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808585059110579725288961 2856438794332934793966721)
                    ·
                      refine ⟨2142329095749701095475041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856438794332934793966721 2142329095749701095475041)
                      ·
                        rfl

theorem cell23_4172171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2, 2].length) (baseStart_4172171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172171 prefixEnd_4172171 := by exact prefixLift 4172171
  have htrace : WordTrace (prefixWord ++ tailWord_4172171) baseStart_4172171 baseEnd_4172171 := by
    simpa [prefixWord, tailWord_4172171, baseEnd_4172171] using wordTrace_append hprefix tailTrace_4172171
  have hstable : (prefixWord ++ tailWord_4172171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172171).length < 2 ^ (prefixWord ++ tailWord_4172171).sum := by decide
  have hdescent : baseEnd_4172171 < baseStart_4172171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172225 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4172225 : Nat := 118140960795 + 4172225 * 2 ^ 59
def prefixEnd_4172225 : Nat := 4983230072969 + 3 ^ 40 * 4172225 * 2
def baseEnd_4172225 : Nat := 2142356823705043884199793

theorem tailTrace_4172225 : CollatzResearch.WordTrace tailWord_4172225 prefixEnd_4172225 2142356823705043884199793 := by
  unfold tailWord_4172225
  simp only [CollatzResearch.WordTrace]
  refine ⟨152173547309748859145366129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101449031539832572763577419 152173547309748859145366129)
  ·
    refine ⟨114130160482311644359024597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152173547309748859145366129 114130160482311644359024597)
    ·
      refine ⟨2674925636304179164664639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 114130160482311644359024597 2674925636304179164664639)
      ·
        refine ⟨4012388454456268746996959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674925636304179164664639 4012388454456268746996959)
        ·
          refine ⟨6018582681684403120495439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012388454456268746996959 6018582681684403120495439)
          ·
            refine ⟨9027874022526604680743159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018582681684403120495439 9027874022526604680743159)
            ·
              refine ⟨13541811033789907021114739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027874022526604680743159 13541811033789907021114739)
              ·
                refine ⟨20312716550684860531672109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541811033789907021114739 20312716550684860531672109)
                ·
                  refine ⟨7617268706506822699377041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20312716550684860531672109 7617268706506822699377041)
                  ·
                    refine ⟨5712951529880117024532781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617268706506822699377041 5712951529880117024532781)
                    ·
                      refine ⟨2142356823705043884199793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5712951529880117024532781 2142356823705043884199793)
                      ·
                        rfl

theorem cell23_4172225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4172225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172225 prefixEnd_4172225 := by exact prefixLift 4172225
  have htrace : WordTrace (prefixWord ++ tailWord_4172225) baseStart_4172225 baseEnd_4172225 := by
    simpa [prefixWord, tailWord_4172225, baseEnd_4172225] using wordTrace_append hprefix tailTrace_4172225
  have hstable : (prefixWord ++ tailWord_4172225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172225).length < 2 ^ (prefixWord ++ tailWord_4172225).sum := by decide
  have hdescent : baseEnd_4172225 < baseStart_4172225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172231 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_4172231 : Nat := 118140960795 + 4172231 * 2 ^ 59
def prefixEnd_4172231 : Nat := 4983230072969 + 3 ^ 40 * 4172231 * 2
def baseEnd_4172231 : Nat := 2142359904588970860724765

theorem tailTrace_4172231 : CollatzResearch.WordTrace tailWord_4172231 prefixEnd_4172231 2142359904588970860724765 := by
  unfold tailWord_4172231
  simp only [CollatzResearch.WordTrace]
  refine ⟨152173766147727122170084547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101449177431818081446723031 152173766147727122170084547)
  ·
    refine ⟨228260649221590683255126821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152173766147727122170084547 228260649221590683255126821)
    ·
      refine ⟨42798871729048253110336279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228260649221590683255126821 42798871729048253110336279)
      ·
        refine ⟨64198307593572379665504419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42798871729048253110336279 64198307593572379665504419)
        ·
          refine ⟨96297461390358569498256629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64198307593572379665504419 96297461390358569498256629)
          ·
            refine ⟨9027887005346115890461559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96297461390358569498256629 9027887005346115890461559)
            ·
              refine ⟨13541830508019173835692339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9027887005346115890461559 13541830508019173835692339)
              ·
                refine ⟨20312745762028760753538509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541830508019173835692339 20312745762028760753538509)
                ·
                  refine ⟨7617279660760785282576941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20312745762028760753538509 7617279660760785282576941)
                  ·
                    refine ⟨2856479872785294480966353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7617279660760785282576941 2856479872785294480966353)
                    ·
                      refine ⟨2142359904588970860724765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856479872785294480966353 2142359904588970860724765)
                      ·
                        rfl

theorem cell23_4172231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_4172231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172231 prefixEnd_4172231 := by exact prefixLift 4172231
  have htrace : WordTrace (prefixWord ++ tailWord_4172231) baseStart_4172231 baseEnd_4172231 := by
    simpa [prefixWord, tailWord_4172231, baseEnd_4172231] using wordTrace_append hprefix tailTrace_4172231
  have hstable : (prefixWord ++ tailWord_4172231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172231).length < 2 ^ (prefixWord ++ tailWord_4172231).sum := by decide
  have hdescent : baseEnd_4172231 < baseStart_4172231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172264 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4172264 : Nat := 118140960795 + 4172264 * 2 ^ 59
def prefixEnd_4172264 : Nat := 4983230072969 + 3 ^ 40 * 4172264 * 2
def baseEnd_4172264 : Nat := 2142376849450569231612113

theorem tailTrace_4172264 : CollatzResearch.WordTrace tailWord_4172264 prefixEnd_4172264 2142376849450569231612113 := by
  unfold tailWord_4172264
  simp only [CollatzResearch.WordTrace]
  refine ⟨76087484878303784403017923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101449979837738379204023897 76087484878303784403017923)
  ·
    refine ⟨114131227317455676604526885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76087484878303784403017923 114131227317455676604526885)
    ·
      refine ⟨21399605122022939363348791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114131227317455676604526885 21399605122022939363348791)
      ·
        refine ⟨32099407683034409045023187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399605122022939363348791 32099407683034409045023187)
        ·
          refine ⟨48149111524551613567534781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32099407683034409045023187 48149111524551613567534781)
          ·
            refine ⟨18055916821706855087825543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48149111524551613567534781 18055916821706855087825543)
            ·
              refine ⟨27083875232560282631738315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18055916821706855087825543 27083875232560282631738315)
              ·
                refine ⟨40625812848840423947607473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27083875232560282631738315 40625812848840423947607473)
                ·
                  refine ⟨30469359636630317960705605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40625812848840423947607473 30469359636630317960705605)
                  ·
                    refine ⟨5713004931868184617632301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30469359636630317960705605 5713004931868184617632301)
                    ·
                      refine ⟨2142376849450569231612113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5713004931868184617632301 2142376849450569231612113)
                      ·
                        rfl

theorem cell23_4172264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4172264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172264 prefixEnd_4172264 := by exact prefixLift 4172264
  have htrace : WordTrace (prefixWord ++ tailWord_4172264) baseStart_4172264 baseEnd_4172264 := by
    simpa [prefixWord, tailWord_4172264, baseEnd_4172264] using wordTrace_append hprefix tailTrace_4172264
  have hstable : (prefixWord ++ tailWord_4172264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172264).length < 2 ^ (prefixWord ++ tailWord_4172264).sum := by decide
  have hdescent : baseEnd_4172264 < baseStart_4172264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172267 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 7]
def baseStart_4172267 : Nat := 118140960795 + 4172267 * 2 ^ 59
def prefixEnd_4172267 : Nat := 4983230072969 + 3 ^ 40 * 4172267 * 2
def baseEnd_4172267 : Nat := 238042043321392524430511

theorem tailTrace_4172267 : CollatzResearch.WordTrace tailWord_4172267 prefixEnd_4172267 238042043321392524430511 := by
  unfold tailWord_4172267
  simp only [CollatzResearch.WordTrace]
  refine ⟨152175079175596700318395055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101450052783731133545596703 152175079175596700318395055)
  ·
    refine ⟨228262618763395050477592583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152175079175596700318395055 228262618763395050477592583)
    ·
      refine ⟨342393928145092575716388875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228262618763395050477592583 342393928145092575716388875)
      ·
        refine ⟨513590892217638863574583313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342393928145092575716388875 513590892217638863574583313)
        ·
          refine ⟨385193169163229147680937485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513590892217638863574583313 385193169163229147680937485)
          ·
            refine ⟨144447438436210930380351557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 385193169163229147680937485 144447438436210930380351557)
            ·
              refine ⟨27083894706789549446315917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144447438436210930380351557 27083894706789549446315917)
              ·
                refine ⟨10156460515046081042368469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27083894706789549446315917 10156460515046081042368469)
                ·
                  refine ⟨238042043321392524430511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10156460515046081042368469 238042043321392524430511)
                  ·
                    rfl

theorem cell23_4172267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 7].length) (baseStart_4172267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172267 prefixEnd_4172267 := by exact prefixLift 4172267
  have htrace : WordTrace (prefixWord ++ tailWord_4172267) baseStart_4172267 baseEnd_4172267 := by
    simpa [prefixWord, tailWord_4172267, baseEnd_4172267] using wordTrace_append hprefix tailTrace_4172267
  have hstable : (prefixWord ++ tailWord_4172267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172267).length < 2 ^ (prefixWord ++ tailWord_4172267).sum := by decide
  have hdescent : baseEnd_4172267 < baseStart_4172267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172278 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4172278 : Nat := 118140960795 + 4172278 * 2 ^ 59
def prefixEnd_4172278 : Nat := 4983230072969 + 3 ^ 40 * 4172278 * 2
def baseEnd_4172278 : Nat := 2142384038179732176837049

theorem tailTrace_4172278 : CollatzResearch.WordTrace tailWord_4172278 prefixEnd_4172278 2142384038179732176837049 := by
  unfold tailWord_4172278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510967523659803074815343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101450320252371232798030325 9510967523659803074815343)
  ·
    refine ⟨14266451285489704612223015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510967523659803074815343 14266451285489704612223015)
    ·
      refine ⟨21399676928234556918334523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266451285489704612223015 21399676928234556918334523)
      ·
        refine ⟨32099515392351835377501785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399676928234556918334523 32099515392351835377501785)
        ·
          refine ⟨24074636544263876533126339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32099515392351835377501785 24074636544263876533126339)
          ·
            refine ⟨36111954816395814799689509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24074636544263876533126339 36111954816395814799689509)
            ·
              refine ⟨6770991528074215274941783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36111954816395814799689509 6770991528074215274941783)
              ·
                refine ⟨10156487292111322912412675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6770991528074215274941783 10156487292111322912412675)
                ·
                  refine ⟨15234730938166984368619013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10156487292111322912412675 15234730938166984368619013)
                  ·
                    refine ⟨2856512050906309569116065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15234730938166984368619013 2856512050906309569116065)
                    ·
                      refine ⟨2142384038179732176837049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856512050906309569116065 2142384038179732176837049)
                      ·
                        rfl

theorem cell23_4172278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4172278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172278 prefixEnd_4172278 := by exact prefixLift 4172278
  have htrace : WordTrace (prefixWord ++ tailWord_4172278) baseStart_4172278 baseEnd_4172278 := by
    simpa [prefixWord, tailWord_4172278, baseEnd_4172278] using wordTrace_append hprefix tailTrace_4172278
  have hstable : (prefixWord ++ tailWord_4172278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172278).length < 2 ^ (prefixWord ++ tailWord_4172278).sum := by decide
  have hdescent : baseEnd_4172278 < baseStart_4172278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172314 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_4172314 : Nat := 118140960795 + 4172314 * 2 ^ 59
def prefixEnd_4172314 : Nat := 4983230072969 + 3 ^ 40 * 4172314 * 2
def baseEnd_4172314 : Nat := 714134174494431345328961

theorem tailTrace_4172314 : CollatzResearch.WordTrace tailWord_4172314 prefixEnd_4172314 714134174494431345328961 := by
  unfold tailWord_4172314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38044198351606606836338999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101451195604284284896903997 38044198351606606836338999)
  ·
    refine ⟨57066297527409910254508499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38044198351606606836338999 57066297527409910254508499)
    ·
      refine ⟨85599446291114865381762749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57066297527409910254508499 85599446291114865381762749)
      ·
        refine ⟨32099792359168074518161031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85599446291114865381762749 32099792359168074518161031)
        ·
          refine ⟨48149688538752111777241547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32099792359168074518161031 48149688538752111777241547)
          ·
            refine ⟨72224532808128167665862321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48149688538752111777241547 72224532808128167665862321)
            ·
              refine ⟨54168399606096125749396741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72224532808128167665862321 54168399606096125749396741)
              ·
                refine ⟨10156574926143023578011889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54168399606096125749396741 10156574926143023578011889)
                ·
                  refine ⟨7617431194607267683508917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156574926143023578011889 7617431194607267683508917)
                  ·
                    refine ⟨714134174494431345328961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7617431194607267683508917 714134174494431345328961)
                    ·
                      rfl

theorem cell23_4172314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_4172314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172314 prefixEnd_4172314 := by exact prefixLift 4172314
  have htrace : WordTrace (prefixWord ++ tailWord_4172314) baseStart_4172314 baseEnd_4172314 := by
    simpa [prefixWord, tailWord_4172314, baseEnd_4172314] using wordTrace_append hprefix tailTrace_4172314
  have hstable : (prefixWord ++ tailWord_4172314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172314).length < 2 ^ (prefixWord ++ tailWord_4172314).sum := by decide
  have hdescent : baseEnd_4172314 < baseStart_4172314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172405 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4172405 : Nat := 118140960795 + 4172405 * 2 ^ 59
def prefixEnd_4172405 : Nat := 4983230072969 + 3 ^ 40 * 4172405 * 2
def baseEnd_4172405 : Nat := 2142449250222853179948965

theorem tailTrace_4172405 : CollatzResearch.WordTrace tailWord_4172405 prefixEnd_4172405 2142449250222853179948965 := by
  unfold tailWord_4172405
  simp only [CollatzResearch.WordTrace]
  refine ⟨152180112449096749886918669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101453408299397833257945779 152180112449096749886918669)
  ·
    refine ⟨57067542168411281207594501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152180112449096749886918669 57067542168411281207594501)
    ·
      refine ⟨10700164156577115226423969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57067542168411281207594501 10700164156577115226423969)
      ·
        refine ⟨8025123117432836419817977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10700164156577115226423969 8025123117432836419817977)
        ·
          refine ⟨6018842338074627314863483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8025123117432836419817977 6018842338074627314863483)
          ·
            refine ⟨9028263507111940972295225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018842338074627314863483 9028263507111940972295225)
            ·
              refine ⟨6771197630333955729221419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028263507111940972295225 6771197630333955729221419)
              ·
                refine ⟨10156796445500933593832129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771197630333955729221419 10156796445500933593832129)
                ·
                  refine ⟨7617597334125700195374097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156796445500933593832129 7617597334125700195374097)
                  ·
                    refine ⟨5713198000594275146530573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7617597334125700195374097 5713198000594275146530573)
                    ·
                      refine ⟨2142449250222853179948965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5713198000594275146530573 2142449250222853179948965)
                      ·
                        rfl

theorem cell23_4172405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4172405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172405 prefixEnd_4172405 := by exact prefixLift 4172405
  have htrace : WordTrace (prefixWord ++ tailWord_4172405) baseStart_4172405 baseEnd_4172405 := by
    simpa [prefixWord, tailWord_4172405, baseEnd_4172405] using wordTrace_append hprefix tailTrace_4172405
  have hstable : (prefixWord ++ tailWord_4172405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172405).length < 2 ^ (prefixWord ++ tailWord_4172405).sum := by decide
  have hdescent : baseEnd_4172405 < baseStart_4172405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172462 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4172462 : Nat := 118140960795 + 4172462 * 2 ^ 59
def prefixEnd_4172462 : Nat := 4983230072969 + 3 ^ 40 * 4172462 * 2
def baseEnd_4172462 : Nat := 2142478518620159456936203

theorem tailTrace_4172462 : CollatzResearch.WordTrace tailWord_4172462 prefixEnd_4172462 2142478518620159456936203 := by
  unfold tailWord_4172462
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022773926236281077717955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101454794273260165747829093 19022773926236281077717955)
  ·
    refine ⟨28534160889354421616576933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19022773926236281077717955 28534160889354421616576933)
    ·
      refine ⟨5350155166753954053108175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28534160889354421616576933 5350155166753954053108175)
      ·
        refine ⟨8025232750130931079662263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350155166753954053108175 8025232750130931079662263)
        ·
          refine ⟨12037849125196396619493395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025232750130931079662263 12037849125196396619493395)
          ·
            refine ⟨18056773687794594929240093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037849125196396619493395 18056773687794594929240093)
            ·
              refine ⟨6771290132922973098465035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18056773687794594929240093 6771290132922973098465035)
              ·
                refine ⟨10156935199384459647697553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771290132922973098465035 10156935199384459647697553)
                ·
                  refine ⟨7617701399538344735773165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10156935199384459647697553 7617701399538344735773165)
                  ·
                    refine ⟨2856638024826879275914937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7617701399538344735773165 2856638024826879275914937)
                    ·
                      refine ⟨2142478518620159456936203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856638024826879275914937 2142478518620159456936203)
                      ·
                        rfl

theorem cell23_4172462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4172462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172462 prefixEnd_4172462 := by exact prefixLift 4172462
  have htrace : WordTrace (prefixWord ++ tailWord_4172462) baseStart_4172462 baseEnd_4172462 := by
    simpa [prefixWord, tailWord_4172462, baseEnd_4172462] using wordTrace_append hprefix tailTrace_4172462
  have hstable : (prefixWord ++ tailWord_4172462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172462).length < 2 ^ (prefixWord ++ tailWord_4172462).sum := by decide
  have hdescent : baseEnd_4172462 < baseStart_4172462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172492 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4172492 : Nat := 118140960795 + 4172492 * 2 ^ 59
def prefixEnd_4172492 : Nat := 4983230072969 + 3 ^ 40 * 4172492 * 2
def baseEnd_4172492 : Nat := 2142493923039794339561065

theorem tailTrace_4172492 : CollatzResearch.WordTrace tailWord_4172492 prefixEnd_4172492 2142493923039794339561065 := by
  unfold tailWord_4172492
  simp only [CollatzResearch.WordTrace]
  refine ⟨76091642799890781872667865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101455523733187709163557153 76091642799890781872667865)
  ·
    refine ⟨57068732099918086404500899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76091642799890781872667865 57068732099918086404500899)
    ·
      refine ⟨85603098149877129606751349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57068732099918086404500899 85603098149877129606751349)
      ·
        refine ⟨8025290451550980900632939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85603098149877129606751349 8025290451550980900632939)
        ·
          refine ⟨12037935677326471350949409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025290451550980900632939 12037935677326471350949409)
          ·
            refine ⟨9028451757994853513212057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12037935677326471350949409 9028451757994853513212057)
            ·
              refine ⟨6771338818496140134909043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028451757994853513212057 6771338818496140134909043)
              ·
                refine ⟨10157008227744210202363565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771338818496140134909043 10157008227744210202363565)
                ·
                  refine ⟨3808878085404078825886337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10157008227744210202363565 3808878085404078825886337)
                  ·
                    refine ⟨2856658564053059119414753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3808878085404078825886337 2856658564053059119414753)
                    ·
                      refine ⟨2142493923039794339561065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856658564053059119414753 2142493923039794339561065)
                      ·
                        rfl

theorem cell23_4172492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4172492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172492 prefixEnd_4172492 := by exact prefixLift 4172492
  have htrace : WordTrace (prefixWord ++ tailWord_4172492) baseStart_4172492 baseEnd_4172492 := by
    simpa [prefixWord, tailWord_4172492, baseEnd_4172492] using wordTrace_append hprefix tailTrace_4172492
  have hstable : (prefixWord ++ tailWord_4172492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172492).length < 2 ^ (prefixWord ++ tailWord_4172492).sum := by decide
  have hdescent : baseEnd_4172492 < baseStart_4172492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172532 : List Nat := [2, 6, 1, 1, 3, 1, 9]
def baseStart_4172532 : Nat := 118140960795 + 4172532 * 2 ^ 59
def prefixEnd_4172532 : Nat := 4983230072969 + 3 ^ 40 * 4172532 * 2
def baseEnd_4172532 : Nat := 26450795830444125716801

theorem tailTrace_4172532 : CollatzResearch.WordTrace tailWord_4172532 prefixEnd_4172532 26450795830444125716801 := by
  unfold tailWord_4172532
  simp only [CollatzResearch.WordTrace]
  refine ⟨76092372259818325288395925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101456496346424433717861233 76092372259818325288395925)
  ·
    refine ⟨3566829949678983997893559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76092372259818325288395925 3566829949678983997893559)
    ·
      refine ⟨5350244924518475996840339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566829949678983997893559 5350244924518475996840339)
      ·
        refine ⟨8025367386777713995260509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350244924518475996840339 8025367386777713995260509)
        ·
          refine ⟨3009512770041642748222691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8025367386777713995260509 3009512770041642748222691)
          ·
            refine ⟨4514269155062464122334037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009512770041642748222691 4514269155062464122334037)
            ·
              refine ⟨26450795830444125716801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4514269155062464122334037 26450795830444125716801)
              ·
                rfl

theorem cell23_4172532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 9].length) (baseStart_4172532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172532 prefixEnd_4172532 := by exact prefixLift 4172532
  have htrace : WordTrace (prefixWord ++ tailWord_4172532) baseStart_4172532 baseEnd_4172532 := by
    simpa [prefixWord, tailWord_4172532, baseEnd_4172532] using wordTrace_append hprefix tailTrace_4172532
  have hstable : (prefixWord ++ tailWord_4172532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172532).length < 2 ^ (prefixWord ++ tailWord_4172532).sum := by decide
  have hdescent : baseEnd_4172532 < baseStart_4172532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172561 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_4172561 : Nat := 118140960795 + 4172561 * 2 ^ 59
def prefixEnd_4172561 : Nat := 4983230072969 + 3 ^ 40 * 4172561 * 2
def baseEnd_4172561 : Nat := 2142529353204954569598247

theorem tailTrace_4172561 : CollatzResearch.WordTrace tailWord_4172561 prefixEnd_4172561 2142529353204954569598247 := by
  unfold tailWord_4172561
  simp only [CollatzResearch.WordTrace]
  refine ⟨152185802236531588529597537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101457201491021059019731691 152185802236531588529597537)
  ·
    refine ⟨114139351677398691397198153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152185802236531588529597537 114139351677398691397198153)
    ·
      refine ⟨85604513758049018547898615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114139351677398691397198153 85604513758049018547898615)
      ·
        refine ⟨128406770637073527821847923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85604513758049018547898615 128406770637073527821847923)
        ·
          refine ⟨192610155955610291732771885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128406770637073527821847923 192610155955610291732771885)
          ·
            refine ⟨72228808483353859399789457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192610155955610291732771885 72228808483353859399789457)
            ·
              refine ⟨54171606362515394549842093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72228808483353859399789457 54171606362515394549842093)
              ·
                refine ⟨20314352385943272956190785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54171606362515394549842093 20314352385943272956190785)
                ·
                  refine ⟨15235764289457454717143089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20314352385943272956190785 15235764289457454717143089)
                  ·
                    refine ⟨11426823217093091037857317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15235764289457454717143089 11426823217093091037857317)
                    ·
                      refine ⟨2142529353204954569598247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11426823217093091037857317 2142529353204954569598247)
                      ·
                        rfl

theorem cell23_4172561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_4172561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172561 prefixEnd_4172561 := by exact prefixLift 4172561
  have htrace : WordTrace (prefixWord ++ tailWord_4172561) baseStart_4172561 baseEnd_4172561 := by
    simpa [prefixWord, tailWord_4172561, baseEnd_4172561] using wordTrace_append hprefix tailTrace_4172561
  have hstable : (prefixWord ++ tailWord_4172561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172561).length < 2 ^ (prefixWord ++ tailWord_4172561).sum := by decide
  have hdescent : baseEnd_4172561 < baseStart_4172561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172586 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4172586 : Nat := 118140960795 + 4172586 * 2 ^ 59
def prefixEnd_4172586 : Nat := 4983230072969 + 3 ^ 40 * 4172586 * 2
def baseEnd_4172586 : Nat := 2142542190221316971785633

theorem tailTrace_4172586 : CollatzResearch.WordTrace tailWord_4172586 prefixEnd_4172586 2142542190221316971785633 := by
  unfold tailWord_4172586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38046678515360254449814403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101457809374294011866171741 38046678515360254449814403)
  ·
    refine ⟨57070017773040381674721605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38046678515360254449814403 57070017773040381674721605)
    ·
      refine ⟨10700628332445071564010301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57070017773040381674721605 10700628332445071564010301)
      ·
        refine ⟨4012735624666901836503863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10700628332445071564010301 4012735624666901836503863)
        ·
          refine ⟨6019103437000352754755795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012735624666901836503863 6019103437000352754755795)
          ·
            refine ⟨9028655155500529132133693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019103437000352754755795 9028655155500529132133693)
            ·
              refine ⟨3385745683312698424550135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9028655155500529132133693 3385745683312698424550135)
              ·
                refine ⟨5078618524969047636825203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385745683312698424550135 5078618524969047636825203)
                ·
                  refine ⟨7617927787453571455237805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5078618524969047636825203 7617927787453571455237805)
                  ·
                    refine ⟨2856722920295089295714177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7617927787453571455237805 2856722920295089295714177)
                    ·
                      refine ⟨2142542190221316971785633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856722920295089295714177 2142542190221316971785633)
                      ·
                        rfl

theorem cell23_4172586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4172586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172586 prefixEnd_4172586 := by exact prefixLift 4172586
  have htrace : WordTrace (prefixWord ++ tailWord_4172586) baseStart_4172586 baseEnd_4172586 := by
    simpa [prefixWord, tailWord_4172586, baseEnd_4172586] using wordTrace_append hprefix tailTrace_4172586
  have hstable : (prefixWord ++ tailWord_4172586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172586).length < 2 ^ (prefixWord ++ tailWord_4172586).sum := by decide
  have hdescent : baseEnd_4172586 < baseStart_4172586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172588 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 5]
def baseStart_4172588 : Nat := 118140960795 + 4172588 * 2 ^ 59
def prefixEnd_4172588 : Nat := 4983230072969 + 3 ^ 40 * 4172588 * 2
def baseEnd_4172588 : Nat := 238060357464736218217847

theorem tailTrace_4172588 : CollatzResearch.WordTrace tailWord_4172588 prefixEnd_4172588 238060357464736218217847 := by
  unfold tailWord_4172588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76093393503716886070415209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101457858004955848093886945 76093393503716886070415209)
  ·
    refine ⟨57070045127787664552811407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76093393503716886070415209 57070045127787664552811407)
    ·
      refine ⟨85605067691681496829217111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57070045127787664552811407 85605067691681496829217111)
      ·
        refine ⟨128407601537522245243825667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85605067691681496829217111 128407601537522245243825667)
        ·
          refine ⟨192611402306283367865738501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128407601537522245243825667 192611402306283367865738501)
          ·
            refine ⟨36114637932428131474825969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192611402306283367865738501 36114637932428131474825969)
            ·
              refine ⟨27085978449321098606119477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36114637932428131474825969 27085978449321098606119477)
              ·
                refine ⟨2539310479623852994323701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27085978449321098606119477 2539310479623852994323701)
                ·
                  refine ⟨238060357464736218217847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539310479623852994323701 238060357464736218217847)
                  ·
                    rfl

theorem cell23_4172588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_4172588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172588 prefixEnd_4172588 := by exact prefixLift 4172588
  have htrace : WordTrace (prefixWord ++ tailWord_4172588) baseStart_4172588 baseEnd_4172588 := by
    simpa [prefixWord, tailWord_4172588, baseEnd_4172588] using wordTrace_append hprefix tailTrace_4172588
  have hstable : (prefixWord ++ tailWord_4172588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172588).length < 2 ^ (prefixWord ++ tailWord_4172588).sum := by decide
  have hdescent : baseEnd_4172588 < baseStart_4172588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172611 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_4172611 : Nat := 118140960795 + 4172611 * 2 ^ 59
def prefixEnd_4172611 : Nat := 4983230072969 + 3 ^ 40 * 4172611 * 2
def baseEnd_4172611 : Nat := 2142555027237679373973017

theorem tailTrace_4172611 : CollatzResearch.WordTrace tailWord_4172611 prefixEnd_4172611 2142555027237679373973017 := by
  unfold tailWord_4172611
  simp only [CollatzResearch.WordTrace]
  refine ⟨152187625886350447068917687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101458417257566964712611791 152187625886350447068917687)
  ·
    refine ⟨228281438829525670603376531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152187625886350447068917687 228281438829525670603376531)
    ·
      refine ⟨342422158244288505905064797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228281438829525670603376531 342422158244288505905064797)
      ·
        refine ⟨128408309341608189714399299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342422158244288505905064797 128408309341608189714399299)
        ·
          refine ⟨192612464012412284571598949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128408309341608189714399299 192612464012412284571598949)
          ·
            refine ⟨36114837002327303357174803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192612464012412284571598949 36114837002327303357174803)
            ·
              refine ⟨54172255503490955035762205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36114837002327303357174803 54172255503490955035762205)
              ·
                refine ⟨20314595813809108138410827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54172255503490955035762205 20314595813809108138410827)
                ·
                  refine ⟨30471893720713662207616241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20314595813809108138410827 30471893720713662207616241)
                  ·
                    refine ⟨22853920290535246655712181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30471893720713662207616241 22853920290535246655712181)
                    ·
                      refine ⟨2142555027237679373973017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22853920290535246655712181 2142555027237679373973017)
                      ·
                        rfl

theorem cell23_4172611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_4172611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172611 prefixEnd_4172611 := by exact prefixLift 4172611
  have htrace : WordTrace (prefixWord ++ tailWord_4172611) baseStart_4172611 baseEnd_4172611 := by
    simpa [prefixWord, tailWord_4172611, baseEnd_4172611] using wordTrace_append hprefix tailTrace_4172611
  have hstable : (prefixWord ++ tailWord_4172611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172611).length < 2 ^ (prefixWord ++ tailWord_4172611).sum := by decide
  have hdescent : baseEnd_4172611 < baseStart_4172611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172612 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4172612 : Nat := 118140960795 + 4172612 * 2 ^ 59
def prefixEnd_4172612 : Nat := 4983230072969 + 3 ^ 40 * 4172612 * 2
def baseEnd_4172612 : Nat := 2142555540718333870060513

theorem tailTrace_4172612 : CollatzResearch.WordTrace tailWord_4172612 prefixEnd_4172612 2142555540718333870060513 := by
  unfold tailWord_4172612
  simp only [CollatzResearch.WordTrace]
  refine ⟨76093831179673412119852045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101458441572897882826469393 76093831179673412119852045)
  ·
    refine ⟨28535186692377529544944517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76093831179673412119852045 28535186692377529544944517)
    ·
      refine ⟨5350347504820786789677097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28535186692377529544944517 5350347504820786789677097)
      ·
        refine ⟨4012760628615590092257823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5350347504820786789677097 4012760628615590092257823)
        ·
          refine ⟨6019140942923385138386735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012760628615590092257823 6019140942923385138386735)
          ·
            refine ⟨9028711414385077707580103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019140942923385138386735 9028711414385077707580103)
            ·
              refine ⟨13543067121577616561370155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028711414385077707580103 13543067121577616561370155)
              ·
                refine ⟨20314600682366424842055233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543067121577616561370155 20314600682366424842055233)
                ·
                  refine ⟨15235950511774818631541425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20314600682366424842055233 15235950511774818631541425)
                  ·
                    refine ⟨11426962883831113973656069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15235950511774818631541425 11426962883831113973656069)
                    ·
                      refine ⟨2142555540718333870060513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11426962883831113973656069 2142555540718333870060513)
                      ·
                        rfl

theorem cell23_4172612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4172612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172612 prefixEnd_4172612 := by exact prefixLift 4172612
  have htrace : WordTrace (prefixWord ++ tailWord_4172612) baseStart_4172612 baseEnd_4172612 := by
    simpa [prefixWord, tailWord_4172612, baseEnd_4172612] using wordTrace_append hprefix tailTrace_4172612
  have hstable : (prefixWord ++ tailWord_4172612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172612).length < 2 ^ (prefixWord ++ tailWord_4172612).sum := by decide
  have hdescent : baseEnd_4172612 < baseStart_4172612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172641 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4172641 : Nat := 118140960795 + 4172641 * 2 ^ 59
def prefixEnd_4172641 : Nat := 4983230072969 + 3 ^ 40 * 4172641 * 2
def baseEnd_4172641 : Nat := 2142570431657314256597879

theorem tailTrace_4172641 : CollatzResearch.WordTrace tailWord_4172641 prefixEnd_4172641 2142570431657314256597879 := by
  unfold tailWord_4172641
  simp only [CollatzResearch.WordTrace]
  refine ⟨152188720076241762192509777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101459146717494508128339851 152188720076241762192509777)
  ·
    refine ⟨114141540057181321644382333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152188720076241762192509777 114141540057181321644382333)
    ·
      refine ⟨42803077521442995616643375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114141540057181321644382333 42803077521442995616643375)
      ·
        refine ⟨64204616282164493424965063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42803077521442995616643375 64204616282164493424965063)
        ·
          refine ⟨96306924423246740137447595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64204616282164493424965063 96306924423246740137447595)
          ·
            refine ⟨144460386634870110206171393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96306924423246740137447595 144460386634870110206171393)
            ·
              refine ⟨108345289976152582654628545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144460386634870110206171393 108345289976152582654628545)
              ·
                refine ⟨81258967482114436990971409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108345289976152582654628545 81258967482114436990971409)
                ·
                  refine ⟨60944225611585827743228557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81258967482114436990971409 60944225611585827743228557)
                  ·
                    refine ⟨22854084604344685403710709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60944225611585827743228557 22854084604344685403710709)
                    ·
                      refine ⟨2142570431657314256597879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22854084604344685403710709 2142570431657314256597879)
                      ·
                        rfl

theorem cell23_4172641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4172641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172641 prefixEnd_4172641 := by exact prefixLift 4172641
  have htrace : WordTrace (prefixWord ++ tailWord_4172641) baseStart_4172641 baseEnd_4172641 := by
    simpa [prefixWord, tailWord_4172641, baseEnd_4172641] using wordTrace_append hprefix tailTrace_4172641
  have hstable : (prefixWord ++ tailWord_4172641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172641).length < 2 ^ (prefixWord ++ tailWord_4172641).sum := by decide
  have hdescent : baseEnd_4172641 < baseStart_4172641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172651 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_4172651 : Nat := 118140960795 + 4172651 * 2 ^ 59
def prefixEnd_4172651 : Nat := 4983230072969 + 3 ^ 40 * 4172651 * 2
def baseEnd_4172651 : Nat := 2142575566463859217472833

theorem tailTrace_4172651 : CollatzResearch.WordTrace tailWord_4172651 prefixEnd_4172651 2142575566463859217472833 := by
  unfold tailWord_4172651
  simp only [CollatzResearch.WordTrace]
  refine ⟨152189084806205533900373807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101459389870803689266915871 152189084806205533900373807)
  ·
    refine ⟨228283627209308300850560711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152189084806205533900373807 228283627209308300850560711)
    ·
      refine ⟨342425440813962451275841067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228283627209308300850560711 342425440813962451275841067)
      ·
        refine ⟨513638161220943676913761601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342425440813962451275841067 513638161220943676913761601)
        ·
          refine ⟨385228620915707757685321201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513638161220943676913761601 385228620915707757685321201)
          ·
            refine ⟨288921465686780818263990901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385228620915707757685321201 288921465686780818263990901)
            ·
              refine ⟨27086387408135701712249147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288921465686780818263990901 27086387408135701712249147)
              ·
                refine ⟨40629581112203552568373721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27086387408135701712249147 40629581112203552568373721)
                ·
                  refine ⟨30472185834152664426280291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40629581112203552568373721 30472185834152664426280291)
                  ·
                    refine ⟨45708278751228996639420437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30472185834152664426280291 45708278751228996639420437)
                    ·
                      refine ⟨2142575566463859217472833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45708278751228996639420437 2142575566463859217472833)
                      ·
                        rfl

theorem cell23_4172651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_4172651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172651 prefixEnd_4172651 := by exact prefixLift 4172651
  have htrace : WordTrace (prefixWord ++ tailWord_4172651) baseStart_4172651 baseEnd_4172651 := by
    simpa [prefixWord, tailWord_4172651, baseEnd_4172651] using wordTrace_append hprefix tailTrace_4172651
  have hstable : (prefixWord ++ tailWord_4172651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172651).length < 2 ^ (prefixWord ++ tailWord_4172651).sum := by decide
  have hdescent : baseEnd_4172651 < baseStart_4172651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172665 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_4172665 : Nat := 118140960795 + 4172665 * 2 ^ 59
def prefixEnd_4172665 : Nat := 4983230072969 + 3 ^ 40 * 4172665 * 2
def baseEnd_4172665 : Nat := 714194251731007387565923

theorem tailTrace_4172665 : CollatzResearch.WordTrace tailWord_4172665 prefixEnd_4172665 714194251731007387565923 := by
  unfold tailWord_4172665
  simp only [CollatzResearch.WordTrace]
  refine ⟨152189595428154814291383449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101459730285436542860922299 152189595428154814291383449)
  ·
    refine ⟨114142196571116110718537587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152189595428154814291383449 114142196571116110718537587)
    ·
      refine ⟨171213294856674166077806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114142196571116110718537587 171213294856674166077806381)
      ·
        refine ⟨64204985571252812279177393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171213294856674166077806381 64204985571252812279177393)
        ·
          refine ⟨48153739178439609209383045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64204985571252812279177393 48153739178439609209383045)
          ·
            refine ⟨9028826095957426726759321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48153739178439609209383045 9028826095957426726759321)
            ·
              refine ⟨6771619571968070045069491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9028826095957426726759321 6771619571968070045069491)
              ·
                refine ⟨10157429357952105067604237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771619571968070045069491 10157429357952105067604237)
                ·
                  refine ⟨3809036009232039400351589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10157429357952105067604237 3809036009232039400351589)
                  ·
                    refine ⟨714194251731007387565923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3809036009232039400351589 714194251731007387565923)
                    ·
                      rfl

theorem cell23_4172665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_4172665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172665 prefixEnd_4172665 := by exact prefixLift 4172665
  have htrace : WordTrace (prefixWord ++ tailWord_4172665) baseStart_4172665 baseEnd_4172665 := by
    simpa [prefixWord, tailWord_4172665, baseEnd_4172665] using wordTrace_append hprefix tailTrace_4172665
  have hstable : (prefixWord ++ tailWord_4172665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172665).length < 2 ^ (prefixWord ++ tailWord_4172665).sum := by decide
  have hdescent : baseEnd_4172665 < baseStart_4172665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172715 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 2, 3, 2]
def baseStart_4172715 : Nat := 118140960795 + 4172715 * 2 ^ 59
def prefixEnd_4172715 : Nat := 4983230072969 + 3 ^ 40 * 4172715 * 2
def baseEnd_4172715 : Nat := 2142608429225746967072539

theorem tailTrace_4172715 : CollatzResearch.WordTrace tailWord_4172715 prefixEnd_4172715 2142608429225746967072539 := by
  unfold tailWord_4172715
  simp only [CollatzResearch.WordTrace]
  refine ⟨152191419077973672830703599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101460946051982448553802399 152191419077973672830703599)
  ·
    refine ⟨228287128616960509246055399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152191419077973672830703599 228287128616960509246055399)
    ·
      refine ⟨342430692925440763869083099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228287128616960509246055399 342430692925440763869083099)
      ·
        refine ⟨513646039388161145803624649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342430692925440763869083099 513646039388161145803624649)
        ·
          refine ⟨385234529541120859352718487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513646039388161145803624649 385234529541120859352718487)
          ·
            refine ⟨577851794311681289029077731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385234529541120859352718487 577851794311681289029077731)
            ·
              refine ⟨866777691467521933543616597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577851794311681289029077731 866777691467521933543616597)
              ·
                refine ⟨10157551071885022658714257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 866777691467521933543616597 10157551071885022658714257)
                ·
                  refine ⟨7618163303913766994035693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10157551071885022658714257 7618163303913766994035693)
                  ·
                    refine ⟨2856811238967662622763385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7618163303913766994035693 2856811238967662622763385)
                    ·
                      refine ⟨2142608429225746967072539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856811238967662622763385 2142608429225746967072539)
                      ·
                        rfl

theorem cell23_4172715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3, 2].length) (baseStart_4172715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172715 prefixEnd_4172715 := by exact prefixLift 4172715
  have htrace : WordTrace (prefixWord ++ tailWord_4172715) baseStart_4172715 baseEnd_4172715 := by
    simpa [prefixWord, tailWord_4172715, baseEnd_4172715] using wordTrace_append hprefix tailTrace_4172715
  have hstable : (prefixWord ++ tailWord_4172715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172715).length < 2 ^ (prefixWord ++ tailWord_4172715).sum := by decide
  have hdescent : baseEnd_4172715 < baseStart_4172715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172785 : List Nat := [1, 2, 2, 2, 4, 3, 1, 8]
def baseStart_4172785 : Nat := 118140960795 + 4172785 * 2 ^ 59
def prefixEnd_4172785 : Nat := 4983230072969 + 3 ^ 40 * 4172785 * 2
def baseEnd_4172785 : Nat := 79357198995243025673971

theorem tailTrace_4172785 : CollatzResearch.WordTrace tailWord_4172785 prefixEnd_4172785 79357198995243025673971 := by
  unfold tailWord_4172785
  simp only [CollatzResearch.WordTrace]
  refine ⟨152193972187720074785751809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101462648125146716523834539 152193972187720074785751809)
  ·
    refine ⟨114145479140790056089313857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152193972187720074785751809 114145479140790056089313857)
    ·
      refine ⟨85609109355592542066985393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114145479140790056089313857 85609109355592542066985393)
      ·
        refine ⟨64206832016694406550239045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85609109355592542066985393 64206832016694406550239045)
        ·
          refine ⟨12038781003130201228169821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64206832016694406550239045 12038781003130201228169821)
          ·
            refine ⟨4514542876173825460563683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12038781003130201228169821 4514542876173825460563683)
            ·
              refine ⟨6771814314260738190845525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514542876173825460563683 6771814314260738190845525)
              ·
                refine ⟨79357198995243025673971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6771814314260738190845525 79357198995243025673971)
                ·
                  rfl

theorem cell23_4172785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 8].length) (baseStart_4172785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172785 prefixEnd_4172785 := by exact prefixLift 4172785
  have htrace : WordTrace (prefixWord ++ tailWord_4172785) baseStart_4172785 baseEnd_4172785 := by
    simpa [prefixWord, tailWord_4172785, baseEnd_4172785] using wordTrace_append hprefix tailTrace_4172785
  have hstable : (prefixWord ++ tailWord_4172785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172785).length < 2 ^ (prefixWord ++ tailWord_4172785).sum := by decide
  have hdescent : baseEnd_4172785 < baseStart_4172785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172789 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4172789 : Nat := 118140960795 + 4172789 * 2 ^ 59
def prefixEnd_4172789 : Nat := 4983230072969 + 3 ^ 40 * 4172789 * 2
def baseEnd_4172789 : Nat := 714215475598059892515733

theorem tailTrace_4172789 : CollatzResearch.WordTrace tailWord_4172789 prefixEnd_4172789 714215475598059892515733 := by
  unfold tailWord_4172789
  simp only [CollatzResearch.WordTrace]
  refine ⟨152194118079705583468897421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101462745386470388979264947 152194118079705583468897421)
  ·
    refine ⟨57072794279889593800836533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152194118079705583468897421 57072794279889593800836533)
    ·
      refine ⟨5350574463739649418828425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57072794279889593800836533 5350574463739649418828425)
      ·
        refine ⟨4012930847804737064121319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5350574463739649418828425 4012930847804737064121319)
        ·
          refine ⟨6019396271707105596181979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012930847804737064121319 6019396271707105596181979)
          ·
            refine ⟨9029094407560658394272969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019396271707105596181979 9029094407560658394272969)
            ·
              refine ⟨6771820805670493795704727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9029094407560658394272969 6771820805670493795704727)
              ·
                refine ⟨10157731208505740693557091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6771820805670493795704727 10157731208505740693557091)
                ·
                  refine ⟨15236596812758611040335637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10157731208505740693557091 15236596812758611040335637)
                  ·
                    refine ⟨714215475598059892515733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15236596812758611040335637 714215475598059892515733)
                    ·
                      rfl

theorem cell23_4172789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4172789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172789 prefixEnd_4172789 := by exact prefixLift 4172789
  have htrace : WordTrace (prefixWord ++ tailWord_4172789) baseStart_4172789 baseEnd_4172789 := by
    simpa [prefixWord, tailWord_4172789, baseEnd_4172789] using wordTrace_append hprefix tailTrace_4172789
  have hstable : (prefixWord ++ tailWord_4172789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172789).length < 2 ^ (prefixWord ++ tailWord_4172789).sum := by decide
  have hdescent : baseEnd_4172789 < baseStart_4172789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172795 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 3]
def baseStart_4172795 : Nat := 118140960795 + 4172795 * 2 ^ 59
def prefixEnd_4172795 : Nat := 4983230072969 + 3 ^ 40 * 4172795 * 2
def baseEnd_4172795 : Nat := 2142649507678106654072171

theorem tailTrace_4172795 : CollatzResearch.WordTrace tailWord_4172795 prefixEnd_4172795 2142649507678106654072171 := by
  unfold tailWord_4172795
  simp only [CollatzResearch.WordTrace]
  refine ⟨152194336917683846493615839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101462891278455897662410559 152194336917683846493615839)
  ·
    refine ⟨228291505376525769740423759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152194336917683846493615839 228291505376525769740423759)
    ·
      refine ⟨342437258064788654610635639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228291505376525769740423759 342437258064788654610635639)
      ·
        refine ⟨513655887097182981915953459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342437258064788654610635639 513655887097182981915953459)
        ·
          refine ⟨770483830645774472873930189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513655887097182981915953459 770483830645774472873930189)
          ·
            refine ⟨288931436492165427327723821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770483830645774472873930189 288931436492165427327723821)
            ·
              refine ⟨108349288684562035247896433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288931436492165427327723821 108349288684562035247896433)
              ·
                refine ⟨81261966513421526435922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108349288684562035247896433 81261966513421526435922325)
                ·
                  refine ⟨3809154680316634051683859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81261966513421526435922325 3809154680316634051683859)
                  ·
                    refine ⟨5713732020474951077525789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809154680316634051683859 5713732020474951077525789)
                    ·
                      refine ⟨2142649507678106654072171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5713732020474951077525789 2142649507678106654072171)
                      ·
                        rfl

theorem cell23_4172795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 1, 3].length) (baseStart_4172795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172795 prefixEnd_4172795 := by exact prefixLift 4172795
  have htrace : WordTrace (prefixWord ++ tailWord_4172795) baseStart_4172795 baseEnd_4172795 := by
    simpa [prefixWord, tailWord_4172795, baseEnd_4172795] using wordTrace_append hprefix tailTrace_4172795
  have hstable : (prefixWord ++ tailWord_4172795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172795).length < 2 ^ (prefixWord ++ tailWord_4172795).sum := by decide
  have hdescent : baseEnd_4172795 < baseStart_4172795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172829 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4172829 : Nat := 118140960795 + 4172829 * 2 ^ 59
def prefixEnd_4172829 : Nat := 4983230072969 + 3 ^ 40 * 4172829 * 2
def baseEnd_4172829 : Nat := 2142666966020359521047015

theorem tailTrace_4172829 : CollatzResearch.WordTrace tailWord_4172829 prefixEnd_4172829 2142666966020359521047015 := by
  unfold tailWord_4172829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152195576999560670300353541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101463717999707113533569027 152195576999560670300353541)
  ·
    refine ⟨28536670687417625681316289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152195576999560670300353541 28536670687417625681316289)
    ·
      refine ⟨21402503015563219260987217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28536670687417625681316289 21402503015563219260987217)
      ·
        refine ⟨16051877261672414445740413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21402503015563219260987217 16051877261672414445740413)
        ·
          refine ⟨6019453973127155417152655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16051877261672414445740413 6019453973127155417152655)
          ·
            refine ⟨9029180959690733125728983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019453973127155417152655 9029180959690733125728983)
            ·
              refine ⟨13543771439536099688593475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029180959690733125728983 13543771439536099688593475)
              ·
                refine ⟨20315657159304149532890213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13543771439536099688593475 20315657159304149532890213)
                ·
                  refine ⟨3809185717369528037416915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20315657159304149532890213 3809185717369528037416915)
                  ·
                    refine ⟨5713778576054292056125373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809185717369528037416915 5713778576054292056125373)
                    ·
                      refine ⟨2142666966020359521047015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5713778576054292056125373 2142666966020359521047015)
                      ·
                        rfl

theorem cell23_4172829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4172829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172829 prefixEnd_4172829 := by exact prefixLift 4172829
  have htrace : WordTrace (prefixWord ++ tailWord_4172829) baseStart_4172829 baseEnd_4172829 := by
    simpa [prefixWord, tailWord_4172829, baseEnd_4172829] using wordTrace_append hprefix tailTrace_4172829
  have hstable : (prefixWord ++ tailWord_4172829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172829).length < 2 ^ (prefixWord ++ tailWord_4172829).sum := by decide
  have hdescent : baseEnd_4172829 < baseStart_4172829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172846 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4172846 : Nat := 118140960795 + 4172846 * 2 ^ 59
def prefixEnd_4172846 : Nat := 4983230072969 + 3 ^ 40 * 4172846 * 2
def baseEnd_4172846 : Nat := 2142675695191485954534437

theorem tailTrace_4172846 : CollatzResearch.WordTrace tailWord_4172846 prefixEnd_4172846 2142675695191485954534437 := by
  unfold tailWord_4172846
  simp only [CollatzResearch.WordTrace]
  refine ⟨19024524630062385275465299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101464131360332721469148261 19024524630062385275465299)
  ·
    refine ⟨28536786945093577913197949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19024524630062385275465299 28536786945093577913197949)
    ·
      refine ⟨10701295104410091717449231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28536786945093577913197949 10701295104410091717449231)
      ·
        refine ⟨16051942656615137576173847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10701295104410091717449231 16051942656615137576173847)
        ·
          refine ⟨24077913984922706364260771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16051942656615137576173847 24077913984922706364260771)
          ·
            refine ⟨36116870977384059546391157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24077913984922706364260771 36116870977384059546391157)
            ·
              refine ⟨3385956654129755582474171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36116870977384059546391157 3385956654129755582474171)
              ·
                refine ⟨5078934981194633373711257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385956654129755582474171 5078934981194633373711257)
                ·
                  refine ⟨3809201235895975030283443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5078934981194633373711257 3809201235895975030283443)
                  ·
                    refine ⟨5713801853843962545425165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809201235895975030283443 5713801853843962545425165)
                    ·
                      refine ⟨2142675695191485954534437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5713801853843962545425165 2142675695191485954534437)
                      ·
                        rfl

theorem cell23_4172846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4172846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172846 prefixEnd_4172846 := by exact prefixLift 4172846
  have htrace : WordTrace (prefixWord ++ tailWord_4172846) baseStart_4172846 baseEnd_4172846 := by
    simpa [prefixWord, tailWord_4172846, baseEnd_4172846] using wordTrace_append hprefix tailTrace_4172846
  have hstable : (prefixWord ++ tailWord_4172846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172846).length < 2 ^ (prefixWord ++ tailWord_4172846).sum := by decide
  have hdescent : baseEnd_4172846 < baseStart_4172846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172903 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_4172903 : Nat := 118140960795 + 4172903 * 2 ^ 59
def prefixEnd_4172903 : Nat := 4983230072969 + 3 ^ 40 * 4172903 * 2
def baseEnd_4172903 : Nat := 2142704963588792231521675

theorem tailTrace_4172903 : CollatzResearch.WordTrace tailWord_4172903 prefixEnd_4172903 2142704963588792231521675 := by
  unfold tailWord_4172903
  simp only [CollatzResearch.WordTrace]
  refine ⟨152198276001292580938547363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101465517334195053959031575 152198276001292580938547363)
  ·
    refine ⟨228297414001938871407821045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152198276001292580938547363 228297414001938871407821045)
    ·
      refine ⟨21402882562681769194483223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228297414001938871407821045 21402882562681769194483223)
      ·
        refine ⟨32104323844022653791724835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21402882562681769194483223 32104323844022653791724835)
        ·
          refine ⟨48156485766033980687587253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32104323844022653791724835 48156485766033980687587253)
          ·
            refine ⟨4514670540565685689461305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48156485766033980687587253 4514670540565685689461305)
            ·
              refine ⟨3386002905424264267095979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4514670540565685689461305 3386002905424264267095979)
              ·
                refine ⟨5079004358136396400643969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386002905424264267095979 5079004358136396400643969)
                ·
                  refine ⟨3809253268602297300482977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079004358136396400643969 3809253268602297300482977)
                  ·
                    refine ⟨2856939951451722975362233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809253268602297300482977 2856939951451722975362233)
                    ·
                      refine ⟨2142704963588792231521675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2856939951451722975362233 2142704963588792231521675)
                      ·
                        rfl

theorem cell23_4172903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_4172903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172903 prefixEnd_4172903 := by exact prefixLift 4172903
  have htrace : WordTrace (prefixWord ++ tailWord_4172903) baseStart_4172903 baseEnd_4172903 := by
    simpa [prefixWord, tailWord_4172903, baseEnd_4172903] using wordTrace_append hprefix tailTrace_4172903
  have hstable : (prefixWord ++ tailWord_4172903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172903).length < 2 ^ (prefixWord ++ tailWord_4172903).sum := by decide
  have hdescent : baseEnd_4172903 < baseStart_4172903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4172995 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 5, 5]
def baseStart_4172995 : Nat := 118140960795 + 4172995 * 2 ^ 59
def prefixEnd_4172995 : Nat := 4983230072969 + 3 ^ 40 * 4172995 * 2
def baseEnd_4172995 : Nat := 714250734603001957190417

theorem tailTrace_4172995 : CollatzResearch.WordTrace tailWord_4172995 prefixEnd_4172995 714250734603001957190417 := by
  unfold tailWord_4172995
  simp only [CollatzResearch.WordTrace]
  refine ⟨152201631516959280650896439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101467754344639520433930959 152201631516959280650896439)
  ·
    refine ⟨228302447275438920976344659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152201631516959280650896439 228302447275438920976344659)
    ·
      refine ⟨342453670913158381464516989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228302447275438920976344659 342453670913158381464516989)
      ·
        refine ⟨128420126592434393049193871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342453670913158381464516989 128420126592434393049193871)
        ·
          refine ⟨192630189888651589573790807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128420126592434393049193871 192630189888651589573790807)
          ·
            refine ⟨288945284832977384360686211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192630189888651589573790807 288945284832977384360686211)
            ·
              refine ⟨433417927249466076541029317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288945284832977384360686211 433417927249466076541029317)
              ·
                refine ⟨81265861359274889351442997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433417927249466076541029317 81265861359274889351442997)
                ·
                  refine ⟨7618674502432020876697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81265861359274889351442997 7618674502432020876697781)
                  ·
                    refine ⟨714250734603001957190417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7618674502432020876697781 714250734603001957190417)
                    ·
                      rfl

theorem cell23_4172995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 5].length) (baseStart_4172995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4172995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4172995 prefixEnd_4172995 := by exact prefixLift 4172995
  have htrace : WordTrace (prefixWord ++ tailWord_4172995) baseStart_4172995 baseEnd_4172995 := by
    simpa [prefixWord, tailWord_4172995, baseEnd_4172995] using wordTrace_append hprefix tailTrace_4172995
  have hstable : (prefixWord ++ tailWord_4172995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4172995).length < 2 ^ (prefixWord ++ tailWord_4172995).sum := by decide
  have hdescent : baseEnd_4172995 < baseStart_4172995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4172995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173043 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 1, 1, 3]
def baseStart_4173043 : Nat := 118140960795 + 4173043 * 2 ^ 59
def prefixEnd_4173043 : Nat := 4983230072969 + 3 ^ 40 * 4173043 * 2
def baseEnd_4173043 : Nat := 2142776850880421683771031

theorem tailTrace_4173043 : CollatzResearch.WordTrace tailWord_4173043 prefixEnd_4173043 2142776850880421683771031 := by
  unfold tailWord_4173043
  simp only [CollatzResearch.WordTrace]
  refine ⟨152203382220785384848643783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101468921480523589899095855 152203382220785384848643783)
  ·
    refine ⟨228305073331178077272965675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152203382220785384848643783 228305073331178077272965675)
    ·
      refine ⟨342457609996767115909448513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228305073331178077272965675 342457609996767115909448513)
      ·
        refine ⟨256843207497575336932086385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342457609996767115909448513 256843207497575336932086385)
        ·
          refine ⟨192632405623181502699064789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256843207497575336932086385 192632405623181502699064789)
          ·
            refine ⟨4514822006793316469509331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 192632405623181502699064789 4514822006793316469509331)
            ·
              refine ⟨6772233010189974704263997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4514822006793316469509331 6772233010189974704263997)
              ·
                refine ⟨2539587378821240514098999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6772233010189974704263997 2539587378821240514098999)
                ·
                  refine ⟨3809381068231860771148499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539587378821240514098999 3809381068231860771148499)
                  ·
                    refine ⟨5714071602347791156722749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809381068231860771148499 5714071602347791156722749)
                    ·
                      refine ⟨2142776850880421683771031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714071602347791156722749 2142776850880421683771031)
                      ·
                        rfl

theorem cell23_4173043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 1, 3].length) (baseStart_4173043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173043 prefixEnd_4173043 := by exact prefixLift 4173043
  have htrace : WordTrace (prefixWord ++ tailWord_4173043) baseStart_4173043 baseEnd_4173043 := by
    simpa [prefixWord, tailWord_4173043, baseEnd_4173043] using wordTrace_append hprefix tailTrace_4173043
  have hstable : (prefixWord ++ tailWord_4173043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173043).length < 2 ^ (prefixWord ++ tailWord_4173043).sum := by decide
  have hdescent : baseEnd_4173043 < baseStart_4173043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173055 : List Nat := [1, 1, 2, 2, 1, 5, 11]
def baseStart_4173055 : Nat := 118140960795 + 4173055 * 2 ^ 59
def prefixEnd_4173055 : Nat := 4983230072969 + 3 ^ 40 * 4173055 * 2
def baseEnd_4173055 : Nat := 26454111267262662182975

theorem tailTrace_4173055 : CollatzResearch.WordTrace tailWord_4173055 prefixEnd_4173055 26454111267262662182975 := by
  unfold tailWord_4173055
  simp only [CollatzResearch.WordTrace]
  refine ⟨152203819896741910898080619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101469213264494607265387079 152203819896741910898080619)
  ·
    refine ⟨228305729845112866347120929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152203819896741910898080619 228305729845112866347120929)
    ·
      refine ⟨171229297383834649760340697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228305729845112866347120929 171229297383834649760340697)
      ·
        refine ⟨128421973037875987320255523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171229297383834649760340697 128421973037875987320255523)
        ·
          refine ⟨192632959556813980980383285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128421973037875987320255523 192632959556813980980383285)
          ·
            refine ⟨18059339958451310716910933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192632959556813980980383285 18059339958451310716910933)
            ·
              refine ⟨26454111267262662182975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18059339958451310716910933 26454111267262662182975)
              ·
                rfl

theorem cell23_4173055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 11].length) (baseStart_4173055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173055 prefixEnd_4173055 := by exact prefixLift 4173055
  have htrace : WordTrace (prefixWord ++ tailWord_4173055) baseStart_4173055 baseEnd_4173055 := by
    simpa [prefixWord, tailWord_4173055, baseEnd_4173055] using wordTrace_append hprefix tailTrace_4173055
  have hstable : (prefixWord ++ tailWord_4173055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173055).length < 2 ^ (prefixWord ++ tailWord_4173055).sum := by decide
  have hdescent : baseEnd_4173055 < baseStart_4173055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173060 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4173060 : Nat := 118140960795 + 4173060 * 2 ^ 59
def prefixEnd_4173060 : Nat := 4983230072969 + 3 ^ 40 * 4173060 * 2
def baseEnd_4173060 : Nat := 2142785580051548117258453

theorem tailTrace_4173060 : CollatzResearch.WordTrace tailWord_4173060 prefixEnd_4173060 2142785580051548117258453 := by
  unfold tailWord_4173060
  simp only [CollatzResearch.WordTrace]
  refine ⟨76102001130861898376006317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101469334841149197834675089 76102001130861898376006317)
  ·
    refine ⟨28538250424073211891002369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76102001130861898376006317 28538250424073211891002369)
    ·
      refine ⟨21403687818054908918251777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28538250424073211891002369 21403687818054908918251777)
      ·
        refine ⟨16052765863541181688688833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21403687818054908918251777 16052765863541181688688833)
        ·
          refine ⟨12039574397655886266516625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16052765863541181688688833 12039574397655886266516625)
          ·
            refine ⟨9029680798241914699887469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12039574397655886266516625 9029680798241914699887469)
            ·
              refine ⟨3386130299340718012457801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9029680798241914699887469 3386130299340718012457801)
              ·
                refine ⟨2539597724505538509343351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386130299340718012457801 2539597724505538509343351)
                ·
                  refine ⟨3809396586758307764015027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539597724505538509343351 3809396586758307764015027)
                  ·
                    refine ⟨5714094880137461646022541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809396586758307764015027 5714094880137461646022541)
                    ·
                      refine ⟨2142785580051548117258453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714094880137461646022541 2142785580051548117258453)
                      ·
                        rfl

theorem cell23_4173060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4173060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173060 prefixEnd_4173060 := by exact prefixLift 4173060
  have htrace : WordTrace (prefixWord ++ tailWord_4173060) baseStart_4173060 baseEnd_4173060 := by
    simpa [prefixWord, tailWord_4173060, baseEnd_4173060] using wordTrace_append hprefix tailTrace_4173060
  have hstable : (prefixWord ++ tailWord_4173060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173060).length < 2 ^ (prefixWord ++ tailWord_4173060).sum := by decide
  have hdescent : baseEnd_4173060 < baseStart_4173060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173110 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4173110 : Nat := 118140960795 + 4173110 * 2 ^ 59
def prefixEnd_4173110 : Nat := 4983230072969 + 3 ^ 40 * 4173110 * 2
def baseEnd_4173110 : Nat := 714270418028090973877741

theorem tailTrace_4173110 : CollatzResearch.WordTrace tailWord_4173110 prefixEnd_4173110 714270418028090973877741 := by
  unfold tailWord_4173110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512864119471415955708299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101470550607695103527555189 9512864119471415955708299)
  ·
    refine ⟨14269296179207123933562449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9512864119471415955708299 14269296179207123933562449)
    ·
      refine ⟨10701972134405342950171837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14269296179207123933562449 10701972134405342950171837)
      ·
        refine ⟨4013239550402003606314439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10701972134405342950171837 4013239550402003606314439)
        ·
          refine ⟨6019859325603005409471659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013239550402003606314439 6019859325603005409471659)
          ·
            refine ⟨9029788988404508114207489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019859325603005409471659 9029788988404508114207489)
            ·
              refine ⟨6772341741303381085655617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9029788988404508114207489 6772341741303381085655617)
              ·
                refine ⟨5079256305977535814241713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6772341741303381085655617 5079256305977535814241713)
                ·
                  refine ⟨3809442229483151860681285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079256305977535814241713 3809442229483151860681285)
                  ·
                    refine ⟨714270418028090973877741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3809442229483151860681285 714270418028090973877741)
                    ·
                      rfl

theorem cell23_4173110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4173110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173110 prefixEnd_4173110 := by exact prefixLift 4173110
  have htrace : WordTrace (prefixWord ++ tailWord_4173110) baseStart_4173110 baseEnd_4173110 := by
    simpa [prefixWord, tailWord_4173110, baseEnd_4173110] using wordTrace_append hprefix tailTrace_4173110
  have hstable : (prefixWord ++ tailWord_4173110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173110).length < 2 ^ (prefixWord ++ tailWord_4173110).sum := by decide
  have hdescent : baseEnd_4173110 < baseStart_4173110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173116 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_4173116 : Nat := 118140960795 + 4173116 * 2 ^ 59
def prefixEnd_4173116 : Nat := 4983230072969 + 3 ^ 40 * 4173116 * 2
def baseEnd_4173116 : Nat := 2142814334968199898158195

theorem tailTrace_4173116 : CollatzResearch.WordTrace tailWord_4173116 prefixEnd_4173116 2142814334968199898158195 := by
  unfold tailWord_4173116
  simp only [CollatzResearch.WordTrace]
  refine ⟨76103022374760459158025601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101470696499680612210700801 76103022374760459158025601)
  ·
    refine ⟨57077266781070344368519201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76103022374760459158025601 57077266781070344368519201)
    ·
      refine ⟨42807950085802758276389401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57077266781070344368519201 42807950085802758276389401)
      ·
        refine ⟨32105962564352068707292051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42807950085802758276389401 32105962564352068707292051)
        ·
          refine ⟨48158943846528103060938077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32105962564352068707292051 48158943846528103060938077)
          ·
            refine ⟨18059603942448038647851779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48158943846528103060938077 18059603942448038647851779)
            ·
              refine ⟨27089405913672057971777669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059603942448038647851779 27089405913672057971777669)
              ·
                refine ⟨5079263608813510869708313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27089405913672057971777669 5079263608813510869708313)
                ·
                  refine ⟨3809447706610133152281235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5079263608813510869708313 3809447706610133152281235)
                  ·
                    refine ⟨5714171559915199728421853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809447706610133152281235 5714171559915199728421853)
                    ·
                      refine ⟨2142814334968199898158195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714171559915199728421853 2142814334968199898158195)
                      ·
                        rfl

theorem cell23_4173116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_4173116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173116 prefixEnd_4173116 := by exact prefixLift 4173116
  have htrace : WordTrace (prefixWord ++ tailWord_4173116) baseStart_4173116 baseEnd_4173116 := by
    simpa [prefixWord, tailWord_4173116, baseEnd_4173116] using wordTrace_append hprefix tailTrace_4173116
  have hstable : (prefixWord ++ tailWord_4173116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173116).length < 2 ^ (prefixWord ++ tailWord_4173116).sum := by decide
  have hdescent : baseEnd_4173116 < baseStart_4173116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173117 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4173117 : Nat := 118140960795 + 4173117 * 2 ^ 59
def prefixEnd_4173117 : Nat := 4983230072969 + 3 ^ 40 * 4173117 * 2
def baseEnd_4173117 : Nat := 2142814848448854394245691

theorem tailTrace_4173117 : CollatzResearch.WordTrace tailWord_4173117 prefixEnd_4173117 2142814848448854394245691 := by
  unfold tailWord_4173117
  simp only [CollatzResearch.WordTrace]
  refine ⟨152206081222517295486837605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101470720815011530324558403 152206081222517295486837605)
  ·
    refine ⟨28538640229221992903782051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152206081222517295486837605 28538640229221992903782051)
    ·
      refine ⟨42807960343832989355673077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28538640229221992903782051 42807960343832989355673077)
      ·
        refine ⟨4013246282234342752094351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42807960343832989355673077 4013246282234342752094351)
        ·
          refine ⟨6019869423351514128141527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013246282234342752094351 6019869423351514128141527)
          ·
            refine ⟨9029804135027271192212291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019869423351514128141527 9029804135027271192212291)
            ·
              refine ⟨13544706202540906788318437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9029804135027271192212291 13544706202540906788318437)
              ·
                refine ⟨2539632412976420022809707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13544706202540906788318437 2539632412976420022809707)
                ·
                  refine ⟨3809448619464630034214561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539632412976420022809707 3809448619464630034214561)
                  ·
                    refine ⟨2857086464598472525660921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809448619464630034214561 2857086464598472525660921)
                    ·
                      refine ⟨2142814848448854394245691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857086464598472525660921 2142814848448854394245691)
                      ·
                        rfl

theorem cell23_4173117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4173117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173117 prefixEnd_4173117 := by exact prefixLift 4173117
  have htrace : WordTrace (prefixWord ++ tailWord_4173117) baseStart_4173117 baseEnd_4173117 := by
    simpa [prefixWord, tailWord_4173117, baseEnd_4173117] using wordTrace_append hprefix tailTrace_4173117
  have hstable : (prefixWord ++ tailWord_4173117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173117).length < 2 ^ (prefixWord ++ tailWord_4173117).sum := by decide
  have hdescent : baseEnd_4173117 < baseStart_4173117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173132 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_4173132 : Nat := 118140960795 + 4173132 * 2 ^ 59
def prefixEnd_4173132 : Nat := 4983230072969 + 3 ^ 40 * 4173132 * 2
def baseEnd_4173132 : Nat := 714274183552890611852707

theorem tailTrace_4173132 : CollatzResearch.WordTrace tailWord_4173132 prefixEnd_4173132 714274183552890611852707 := by
  unfold tailWord_4173132
  simp only [CollatzResearch.WordTrace]
  refine ⟨76103314158731476524316825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101471085544975302032422433 76103314158731476524316825)
  ·
    refine ⟨57077485619048607393237619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76103314158731476524316825 57077485619048607393237619)
    ·
      refine ⟨85616228428572911089856429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57077485619048607393237619 85616228428572911089856429)
      ·
        refine ⟨32106085660714841658696161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85616228428572911089856429 32106085660714841658696161)
        ·
          refine ⟨24079564245536131244022121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32106085660714841658696161 24079564245536131244022121)
          ·
            refine ⟨18059673184152098433016591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24079564245536131244022121 18059673184152098433016591)
            ·
              refine ⟨27089509776228147649524887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18059673184152098433016591 27089509776228147649524887)
              ·
                refine ⟨40634264664342221474287331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27089509776228147649524887 40634264664342221474287331)
                ·
                  refine ⟨60951396996513332211430997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40634264664342221474287331 60951396996513332211430997)
                  ·
                    refine ⟨714274183552890611852707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60951396996513332211430997 714274183552890611852707)
                    ·
                      rfl

theorem cell23_4173132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_4173132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173132 prefixEnd_4173132 := by exact prefixLift 4173132
  have htrace : WordTrace (prefixWord ++ tailWord_4173132) baseStart_4173132 baseEnd_4173132 := by
    simpa [prefixWord, tailWord_4173132, baseEnd_4173132] using wordTrace_append hprefix tailTrace_4173132
  have hstable : (prefixWord ++ tailWord_4173132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173132).length < 2 ^ (prefixWord ++ tailWord_4173132).sum := by decide
  have hdescent : baseEnd_4173132 < baseStart_4173132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173156 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_4173156 : Nat := 118140960795 + 4173156 * 2 ^ 59
def prefixEnd_4173156 : Nat := 4983230072969 + 3 ^ 40 * 4173156 * 2
def baseEnd_4173156 : Nat := 2142834874194379741658011

theorem tailTrace_4173156 : CollatzResearch.WordTrace tailWord_4173156 prefixEnd_4173156 2142834874194379741658011 := by
  unfold tailWord_4173156
  simp only [CollatzResearch.WordTrace]
  refine ⟨76103751834688002573753661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101471669112917336765004881 76103751834688002573753661)
  ·
    refine ⟨28538906938008000965157623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76103751834688002573753661 28538906938008000965157623)
    ·
      refine ⟨42808360407012001447736435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28538906938008000965157623 42808360407012001447736435)
      ·
        refine ⟨64212540610518002171604653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42808360407012001447736435 64212540610518002171604653)
        ·
          refine ⟨24079702728944250814351745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64212540610518002171604653 24079702728944250814351745)
          ·
            refine ⟨18059777046708188110763809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24079702728944250814351745 18059777046708188110763809)
            ·
              refine ⟨13544832785031141083072857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18059777046708188110763809 13544832785031141083072857)
              ·
                refine ⟨10158624588773355812304643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13544832785031141083072857 10158624588773355812304643)
                ·
                  refine ⟨15237936883160033718456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10158624588773355812304643 15237936883160033718456965)
                  ·
                    refine ⟨2857113165592506322210681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15237936883160033718456965 2857113165592506322210681)
                    ·
                      refine ⟨2142834874194379741658011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857113165592506322210681 2142834874194379741658011)
                      ·
                        rfl

theorem cell23_4173156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_4173156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173156 prefixEnd_4173156 := by exact prefixLift 4173156
  have htrace : WordTrace (prefixWord ++ tailWord_4173156) baseStart_4173156 baseEnd_4173156 := by
    simpa [prefixWord, tailWord_4173156, baseEnd_4173156] using wordTrace_append hprefix tailTrace_4173156
  have hstable : (prefixWord ++ tailWord_4173156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173156).length < 2 ^ (prefixWord ++ tailWord_4173156).sum := by decide
  have hdescent : baseEnd_4173156 < baseStart_4173156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173179 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 5]
def baseStart_4173179 : Nat := 118140960795 + 4173179 * 2 ^ 59
def prefixEnd_4173179 : Nat := 4983230072969 + 3 ^ 40 * 4173179 * 2
def baseEnd_4173179 : Nat := 238094076027714794630045

theorem tailTrace_4173179 : CollatzResearch.WordTrace tailWord_4173179 prefixEnd_4173179 238094076027714794630045 := by
  unfold tailWord_4173179
  simp only [CollatzResearch.WordTrace]
  refine ⟨152208342548292680075594591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101472228365528453383729727 152208342548292680075594591)
  ·
    refine ⟨228312513822439020113391887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152208342548292680075594591 228312513822439020113391887)
    ·
      refine ⟨342468770733658530170087831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228312513822439020113391887 342468770733658530170087831)
      ·
        refine ⟨513703156100487795255131747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342468770733658530170087831 513703156100487795255131747)
        ·
          refine ⟨770554734150731692882697621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513703156100487795255131747 770554734150731692882697621)
          ·
            refine ⟨36119753163315548103876451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 770554734150731692882697621 36119753163315548103876451)
            ·
              refine ⟨54179629744973322155814677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36119753163315548103876451 54179629744973322155814677)
              ·
                refine ⟨2539670144295624476053813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54179629744973322155814677 2539670144295624476053813)
                ·
                  refine ⟨238094076027714794630045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539670144295624476053813 238094076027714794630045)
                  ·
                    rfl

theorem cell23_4173179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 5].length) (baseStart_4173179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173179 prefixEnd_4173179 := by exact prefixLift 4173179
  have htrace : WordTrace (prefixWord ++ tailWord_4173179) baseStart_4173179 baseEnd_4173179 := by
    simpa [prefixWord, tailWord_4173179, baseEnd_4173179] using wordTrace_append hprefix tailTrace_4173179
  have hstable : (prefixWord ++ tailWord_4173179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173179).length < 2 ^ (prefixWord ++ tailWord_4173179).sum := by decide
  have hdescent : baseEnd_4173179 < baseStart_4173179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173189 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_4173189 : Nat := 118140960795 + 4173189 * 2 ^ 59
def prefixEnd_4173189 : Nat := 4983230072969 + 3 ^ 40 * 4173189 * 2
def baseEnd_4173189 : Nat := 2142851819055978112545359

theorem tailTrace_4173189 : CollatzResearch.WordTrace tailWord_4173189 prefixEnd_4173189 2142851819055978112545359 := by
  unfold tailWord_4173189
  simp only [CollatzResearch.WordTrace]
  refine ⟨152208707278256451783458621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101472471518837634522305747 152208707278256451783458621)
  ·
    refine ⟨57078265229346169418796983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152208707278256451783458621 57078265229346169418796983)
    ·
      refine ⟨85617397844019254128195475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57078265229346169418796983 85617397844019254128195475)
      ·
        refine ⟨128426096766028881192293213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85617397844019254128195475 128426096766028881192293213)
        ·
          refine ⟨48159786287260830447109955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128426096766028881192293213 48159786287260830447109955)
          ·
            refine ⟨72239679430891245670664933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48159786287260830447109955 72239679430891245670664933)
            ·
              refine ⟨13544939893292108563249675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72239679430891245670664933 13544939893292108563249675)
              ·
                refine ⟨20317409839938162844874513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13544939893292108563249675 20317409839938162844874513)
                ·
                  refine ⟨15238057379953622133655885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20317409839938162844874513 15238057379953622133655885)
                  ·
                    refine ⟨5714271517482608300120957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238057379953622133655885 5714271517482608300120957)
                    ·
                      refine ⟨2142851819055978112545359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714271517482608300120957 2142851819055978112545359)
                      ·
                        rfl

theorem cell23_4173189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_4173189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173189 prefixEnd_4173189 := by exact prefixLift 4173189
  have htrace : WordTrace (prefixWord ++ tailWord_4173189) baseStart_4173189 baseEnd_4173189 := by
    simpa [prefixWord, tailWord_4173189, baseEnd_4173189] using wordTrace_append hprefix tailTrace_4173189
  have hstable : (prefixWord ++ tailWord_4173189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173189).length < 2 ^ (prefixWord ++ tailWord_4173189).sum := by decide
  have hdescent : baseEnd_4173189 < baseStart_4173189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173213 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 5]
def baseStart_4173213 : Nat := 118140960795 + 4173213 * 2 ^ 59
def prefixEnd_4173213 : Nat := 4983230072969 + 3 ^ 40 * 4173213 * 2
def baseEnd_4173213 : Nat := 238096015843520668738361

theorem tailTrace_4173213 : CollatzResearch.WordTrace tailWord_4173213 prefixEnd_4173213 238096015843520668738361 := by
  unfold tailWord_4173213
  simp only [CollatzResearch.WordTrace]
  refine ⟨152209582630169503882332293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101473055086779669254888195 152209582630169503882332293)
  ·
    refine ⟨28539296743156781977937305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152209582630169503882332293 28539296743156781977937305)
    ·
      refine ⟨21404472557367586483452979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28539296743156781977937305 21404472557367586483452979)
      ·
        refine ⟨32106708836051379725179469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21404472557367586483452979 32106708836051379725179469)
        ·
          refine ⟨12040015813519267396942301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32106708836051379725179469 12040015813519267396942301)
          ·
            refine ⟨4515005930069725273853363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12040015813519267396942301 4515005930069725273853363)
            ·
              refine ⟨6772508895104587910780045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515005930069725273853363 6772508895104587910780045)
              ·
                refine ⟨2539690835664220466542517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6772508895104587910780045 2539690835664220466542517)
                ·
                  refine ⟨238096015843520668738361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539690835664220466542517 238096015843520668738361)
                  ·
                    rfl

theorem cell23_4173213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_4173213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173213 prefixEnd_4173213 := by exact prefixLift 4173213
  have htrace : WordTrace (prefixWord ++ tailWord_4173213) baseStart_4173213 baseEnd_4173213 := by
    simpa [prefixWord, tailWord_4173213, baseEnd_4173213] using wordTrace_append hprefix tailTrace_4173213
  have hstable : (prefixWord ++ tailWord_4173213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173213).length < 2 ^ (prefixWord ++ tailWord_4173213).sum := by decide
  have hdescent : baseEnd_4173213 < baseStart_4173213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173232 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_4173232 : Nat := 118140960795 + 4173232 * 2 ^ 59
def prefixEnd_4173232 : Nat := 4983230072969 + 3 ^ 40 * 4173232 * 2
def baseEnd_4173232 : Nat := 2142873898724121444307661

theorem tailTrace_4173232 : CollatzResearch.WordTrace tailWord_4173232 prefixEnd_4173232 2142873898724121444307661 := by
  unfold tailWord_4173232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76105137808550335063636975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101473517078067113418182633 76105137808550335063636975)
  ·
    refine ⟨114157706712825502595455463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76105137808550335063636975 114157706712825502595455463)
    ·
      refine ⟨171236560069238253893183195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114157706712825502595455463 171236560069238253893183195)
      ·
        refine ⟨256854840103857380839774793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171236560069238253893183195 256854840103857380839774793)
        ·
          refine ⟨192641130077893035629831095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256854840103857380839774793 192641130077893035629831095)
          ·
            refine ⟨288961695116839553444746643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192641130077893035629831095 288961695116839553444746643)
            ·
              refine ⟨433442542675259330167119965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288961695116839553444746643 433442542675259330167119965)
              ·
                refine ⟨162540953503222248812669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433442542675259330167119965 162540953503222248812669987)
                ·
                  refine ⟨243811430254833373219004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162540953503222248812669987 243811430254833373219004981)
                  ·
                    refine ⟨22857321586390628739281717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243811430254833373219004981 22857321586390628739281717)
                    ·
                      refine ⟨2142873898724121444307661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22857321586390628739281717 2142873898724121444307661)
                      ·
                        rfl

theorem cell23_4173232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_4173232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173232 prefixEnd_4173232 := by exact prefixLift 4173232
  have htrace : WordTrace (prefixWord ++ tailWord_4173232) baseStart_4173232 baseEnd_4173232 := by
    simpa [prefixWord, tailWord_4173232, baseEnd_4173232] using wordTrace_append hprefix tailTrace_4173232
  have hstable : (prefixWord ++ tailWord_4173232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173232).length < 2 ^ (prefixWord ++ tailWord_4173232).sum := by decide
  have hdescent : baseEnd_4173232 < baseStart_4173232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173246 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_4173246 : Nat := 118140960795 + 4173246 * 2 ^ 59
def prefixEnd_4173246 : Nat := 4983230072969 + 3 ^ 40 * 4173246 * 2
def baseEnd_4173246 : Nat := 2142881087453284389532597

theorem tailTrace_4173246 : CollatzResearch.WordTrace tailWord_4173246 prefixEnd_4173246 2142881087453284389532597 := by
  unfold tailWord_4173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨19026348279881243814785449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101473857492699967012189061 19026348279881243814785449)
  ·
    refine ⟨14269761209910932861089087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19026348279881243814785449 14269761209910932861089087)
    ·
      refine ⟨21404641814866399291633631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14269761209910932861089087 21404641814866399291633631)
      ·
        refine ⟨32106962722299598937450447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21404641814866399291633631 32106962722299598937450447)
        ·
          refine ⟨48160444083449398406175671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32106962722299598937450447 48160444083449398406175671)
          ·
            refine ⟨72240666125174097609263507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48160444083449398406175671 72240666125174097609263507)
            ·
              refine ⟨108360999187761146413895261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72240666125174097609263507 108360999187761146413895261)
              ·
                refine ⟨40635374695410429905210723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108360999187761146413895261 40635374695410429905210723)
                ·
                  refine ⟨60953062043115644857816085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40635374695410429905210723 60953062043115644857816085)
                  ·
                    refine ⟨2857174783271045852710129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60953062043115644857816085 2857174783271045852710129)
                    ·
                      refine ⟨2142881087453284389532597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857174783271045852710129 2142881087453284389532597)
                      ·
                        rfl

theorem cell23_4173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_4173246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173246 prefixEnd_4173246 := by exact prefixLift 4173246
  have htrace : WordTrace (prefixWord ++ tailWord_4173246) baseStart_4173246 baseEnd_4173246 := by
    simpa [prefixWord, tailWord_4173246, baseEnd_4173246] using wordTrace_append hprefix tailTrace_4173246
  have hstable : (prefixWord ++ tailWord_4173246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173246).length < 2 ^ (prefixWord ++ tailWord_4173246).sum := by decide
  have hdescent : baseEnd_4173246 < baseStart_4173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173290 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_4173290 : Nat := 118140960795 + 4173290 * 2 ^ 59
def prefixEnd_4173290 : Nat := 4983230072969 + 3 ^ 40 * 4173290 * 2
def baseEnd_4173290 : Nat := 714301226867360739127465

theorem tailTrace_4173290 : CollatzResearch.WordTrace tailWord_4173290 prefixEnd_4173290 714301226867360739127465 := by
  unfold tailWord_4173290
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053097762722636508221331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101474927367260364021923549 38053097762722636508221331)
  ·
    refine ⟨57079646644083954762331997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38053097762722636508221331 57079646644083954762331997)
    ·
      refine ⟨21404867491531483035874499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57079646644083954762331997 21404867491531483035874499)
      ·
        refine ⟨32107301237297224553811749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21404867491531483035874499 32107301237297224553811749)
        ·
          refine ⟨6020118981993229603839703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32107301237297224553811749 6020118981993229603839703)
          ·
            refine ⟨9030178472989844405759555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020118981993229603839703 9030178472989844405759555)
            ·
              refine ⟨13545267709484766608639333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030178472989844405759555 13545267709484766608639333)
              ·
                refine ⟨2539737695528393739119875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13545267709484766608639333 2539737695528393739119875)
                ·
                  refine ⟨3809606543292590608679813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539737695528393739119875 3809606543292590608679813)
                  ·
                    refine ⟨714301226867360739127465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3809606543292590608679813 714301226867360739127465)
                    ·
                      rfl

theorem cell23_4173290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_4173290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173290 prefixEnd_4173290 := by exact prefixLift 4173290
  have htrace : WordTrace (prefixWord ++ tailWord_4173290) baseStart_4173290 baseEnd_4173290 := by
    simpa [prefixWord, tailWord_4173290, baseEnd_4173290] using wordTrace_append hprefix tailTrace_4173290
  have hstable : (prefixWord ++ tailWord_4173290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173290).length < 2 ^ (prefixWord ++ tailWord_4173290).sum := by decide
  have hdescent : baseEnd_4173290 < baseStart_4173290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173306 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_4173306 : Nat := 118140960795 + 4173306 * 2 ^ 59
def prefixEnd_4173306 : Nat := 4983230072969 + 3 ^ 40 * 4173306 * 2
def baseEnd_4173306 : Nat := 2142911896292554154782321

theorem tailTrace_4173306 : CollatzResearch.WordTrace tailWord_4173306 prefixEnd_4173306 2142911896292554154782321 := by
  unfold tailWord_4173306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053243654708145191366943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101475316412555053843645181 38053243654708145191366943)
  ·
    refine ⟨57079865482062217787050415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38053243654708145191366943 57079865482062217787050415)
    ·
      refine ⟨85619798223093326680575623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57079865482062217787050415 85619798223093326680575623)
      ·
        refine ⟨128429697334639990020863435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85619798223093326680575623 128429697334639990020863435)
        ·
          refine ⟨192644546001959985031295153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128429697334639990020863435 192644546001959985031295153)
          ·
            refine ⟨144483409501469988773471365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192644546001959985031295153 144483409501469988773471365)
            ·
              refine ⟨27090639281525622895025881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144483409501469988773471365 27090639281525622895025881)
              ·
                refine ⟨20317979461144217171269411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27090639281525622895025881 20317979461144217171269411)
                ·
                  refine ⟨30476969191716325756904117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20317979461144217171269411 30476969191716325756904117)
                  ·
                    refine ⟨2857215861723405539709761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30476969191716325756904117 2857215861723405539709761)
                    ·
                      refine ⟨2142911896292554154782321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857215861723405539709761 2142911896292554154782321)
                      ·
                        rfl

theorem cell23_4173306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_4173306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173306 prefixEnd_4173306 := by exact prefixLift 4173306
  have htrace : WordTrace (prefixWord ++ tailWord_4173306) baseStart_4173306 baseEnd_4173306 := by
    simpa [prefixWord, tailWord_4173306, baseEnd_4173306] using wordTrace_append hprefix tailTrace_4173306
  have hstable : (prefixWord ++ tailWord_4173306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173306).length < 2 ^ (prefixWord ++ tailWord_4173306).sum := by decide
  have hdescent : baseEnd_4173306 < baseStart_4173306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173323 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 5, 2]
def baseStart_4173323 : Nat := 118140960795 + 4173323 * 2 ^ 59
def prefixEnd_4173323 : Nat := 4983230072969 + 3 ^ 40 * 4173323 * 2
def baseEnd_4173323 : Nat := 2142920625463680588269743

theorem tailTrace_4173323 : CollatzResearch.WordTrace tailWord_4173323 prefixEnd_4173323 2142920625463680588269743 := by
  unfold tailWord_4173323
  simp only [CollatzResearch.WordTrace]
  refine ⟨152213594659770992668836623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101475729773180661779224415 152213594659770992668836623)
  ·
    refine ⟨228320391989656489003254935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152213594659770992668836623 228320391989656489003254935)
    ·
      refine ⟨342480587984484733504882403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228320391989656489003254935 342480587984484733504882403)
      ·
        refine ⟨513720881976727100257323605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342480587984484733504882403 513720881976727100257323605)
        ·
          refine ⟨6020166585664770706140511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 513720881976727100257323605 6020166585664770706140511)
          ·
            refine ⟨9030249878497156059210767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020166585664770706140511 9030249878497156059210767)
            ·
              refine ⟨13545374817745734088816151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030249878497156059210767 13545374817745734088816151)
              ·
                refine ⟨20318062226618601133224227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545374817745734088816151 20318062226618601133224227)
                ·
                  refine ⟨30477093339927901699836341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20318062226618601133224227 30477093339927901699836341)
                  ·
                    refine ⟨2857227500618240784359657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30477093339927901699836341 2857227500618240784359657)
                    ·
                      refine ⟨2142920625463680588269743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857227500618240784359657 2142920625463680588269743)
                      ·
                        rfl

theorem cell23_4173323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5, 2].length) (baseStart_4173323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173323 prefixEnd_4173323 := by exact prefixLift 4173323
  have htrace : WordTrace (prefixWord ++ tailWord_4173323) baseStart_4173323 baseEnd_4173323 := by
    simpa [prefixWord, tailWord_4173323, baseEnd_4173323] using wordTrace_append hprefix tailTrace_4173323
  have hstable : (prefixWord ++ tailWord_4173323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173323).length < 2 ^ (prefixWord ++ tailWord_4173323).sum := by decide
  have hdescent : baseEnd_4173323 < baseStart_4173323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173329 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_4173329 : Nat := 118140960795 + 4173329 * 2 ^ 59
def prefixEnd_4173329 : Nat := 4983230072969 + 3 ^ 40 * 4173329 * 2
def baseEnd_4173329 : Nat := 714307902115869188264905

theorem tailTrace_4173329 : CollatzResearch.WordTrace tailWord_4173329 prefixEnd_4173329 714307902115869188264905 := by
  unfold tailWord_4173329
  simp only [CollatzResearch.WordTrace]
  refine ⟨152213813497749255693555041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101475875665166170462370027 152213813497749255693555041)
  ·
    refine ⟨114160360123311941770166281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152213813497749255693555041 114160360123311941770166281)
    ·
      refine ⟨85620270092483956327624711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114160360123311941770166281 85620270092483956327624711)
      ·
        refine ⟨128430405138725934491437067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85620270092483956327624711 128430405138725934491437067)
        ·
          refine ⟨192645607708088901737155601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128430405138725934491437067 192645607708088901737155601)
          ·
            refine ⟨144484205781066676302866701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192645607708088901737155601 144484205781066676302866701)
            ·
              refine ⟨54181577167900003613575013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144484205781066676302866701 54181577167900003613575013)
              ·
                refine ⟨10159045718981250677545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54181577167900003613575013 10159045718981250677545315)
                ·
                  refine ⟨15238568578471876016317973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159045718981250677545315 15238568578471876016317973)
                  ·
                    refine ⟨714307902115869188264905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15238568578471876016317973 714307902115869188264905)
                    ·
                      rfl

theorem cell23_4173329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_4173329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173329 prefixEnd_4173329 := by exact prefixLift 4173329
  have htrace : WordTrace (prefixWord ++ tailWord_4173329) baseStart_4173329 baseEnd_4173329 := by
    simpa [prefixWord, tailWord_4173329, baseEnd_4173329] using wordTrace_append hprefix tailTrace_4173329
  have hstable : (prefixWord ++ tailWord_4173329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173329).length < 2 ^ (prefixWord ++ tailWord_4173329).sum := by decide
  have hdescent : baseEnd_4173329 < baseStart_4173329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173333 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_4173333 : Nat := 118140960795 + 4173333 * 2 ^ 59
def prefixEnd_4173333 : Nat := 4983230072969 + 3 ^ 40 * 4173333 * 2
def baseEnd_4173333 : Nat := 714308586756741849714899

theorem tailTrace_4173333 : CollatzResearch.WordTrace tailWord_4173333 prefixEnd_4173333 714308586756741849714899 := by
  unfold tailWord_4173333
  simp only [CollatzResearch.WordTrace]
  refine ⟨152213959389734764376700653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101475972926489842917800435 152213959389734764376700653)
  ·
    refine ⟨57080234771150536641262745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152213959389734764376700653 57080234771150536641262745)
    ·
      refine ⟨42810176078362902480947059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57080234771150536641262745 42810176078362902480947059)
      ·
        refine ⟨64215264117544353721420589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42810176078362902480947059 64215264117544353721420589)
        ·
          refine ⟨24080724044079132645532721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64215264117544353721420589 24080724044079132645532721)
          ·
            refine ⟨18060543033059349484149541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24080724044079132645532721 18060543033059349484149541)
            ·
              refine ⟨3386351818698628028278039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18060543033059349484149541 3386351818698628028278039)
              ·
                refine ⟨5079527728047942042417059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386351818698628028278039 5079527728047942042417059)
                ·
                  refine ⟨7619291592071913063625589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079527728047942042417059 7619291592071913063625589)
                  ·
                    refine ⟨714308586756741849714899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7619291592071913063625589 714308586756741849714899)
                    ·
                      rfl

theorem cell23_4173333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_4173333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173333 prefixEnd_4173333 := by exact prefixLift 4173333
  have htrace : WordTrace (prefixWord ++ tailWord_4173333) baseStart_4173333 baseEnd_4173333 := by
    simpa [prefixWord, tailWord_4173333, baseEnd_4173333] using wordTrace_append hprefix tailTrace_4173333
  have hstable : (prefixWord ++ tailWord_4173333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173333).length < 2 ^ (prefixWord ++ tailWord_4173333).sum := by decide
  have hdescent : baseEnd_4173333 < baseStart_4173333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173349 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_4173349 : Nat := 118140960795 + 4173349 * 2 ^ 59
def prefixEnd_4173349 : Nat := 4983230072969 + 3 ^ 40 * 4173349 * 2
def baseEnd_4173349 : Nat := 2142933975960697486544623

theorem tailTrace_4173349 : CollatzResearch.WordTrace tailWord_4173349 prefixEnd_4173349 2142933975960697486544623 := by
  unfold tailWord_4173349
  simp only [CollatzResearch.WordTrace]
  refine ⟨152214542957676799109283101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101476361971784532739522067 152214542957676799109283101)
  ·
    refine ⟨57080453609128799665981163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152214542957676799109283101 57080453609128799665981163)
    ·
      refine ⟨85620680413693199498971745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57080453609128799665981163 85620680413693199498971745)
      ·
        refine ⟨64215510310269899624228809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85620680413693199498971745 64215510310269899624228809)
        ·
          refine ⟨48161632732702424718171607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64215510310269899624228809 48161632732702424718171607)
          ·
            refine ⟨72242449099053637077257411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48161632732702424718171607 72242449099053637077257411)
            ·
              refine ⟨108363673648580455615886117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72242449099053637077257411 108363673648580455615886117)
              ·
                refine ⟨20318188809108835427978647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108363673648580455615886117 20318188809108835427978647)
                ·
                  refine ⟨30477283213663253141967971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20318188809108835427978647 30477283213663253141967971)
                  ·
                    refine ⟨45715924820494879712951957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30477283213663253141967971 45715924820494879712951957)
                    ·
                      refine ⟨2142933975960697486544623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45715924820494879712951957 2142933975960697486544623)
                      ·
                        rfl

theorem cell23_4173349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_4173349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173349 prefixEnd_4173349 := by exact prefixLift 4173349
  have htrace : WordTrace (prefixWord ++ tailWord_4173349) baseStart_4173349 baseEnd_4173349 := by
    simpa [prefixWord, tailWord_4173349, baseEnd_4173349] using wordTrace_append hprefix tailTrace_4173349
  have hstable : (prefixWord ++ tailWord_4173349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173349).length < 2 ^ (prefixWord ++ tailWord_4173349).sum := by decide
  have hdescent : baseEnd_4173349 < baseStart_4173349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173386 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_4173386 : Nat := 118140960795 + 4173386 * 2 ^ 59
def prefixEnd_4173386 : Nat := 4983230072969 + 3 ^ 40 * 4173386 * 2
def baseEnd_4173386 : Nat := 2142952974744913841781953

theorem tailTrace_4173386 : CollatzResearch.WordTrace tailWord_4173386 prefixEnd_4173386 2142952974744913841781953 := by
  unfold tailWord_4173386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053973114635688607095003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101477261639028502952253341 38053973114635688607095003)
  ·
    refine ⟨57080959671953532910642505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38053973114635688607095003 57080959671953532910642505)
    ·
      refine ⟨42810719753965149682981879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57080959671953532910642505 42810719753965149682981879)
      ·
        refine ⟨64216079630947724524472819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42810719753965149682981879 64216079630947724524472819)
        ·
          refine ⟨96324119446421586786709229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64216079630947724524472819 96324119446421586786709229)
          ·
            refine ⟨36121544792408095045015961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96324119446421586786709229 36121544792408095045015961)
            ·
              refine ⟨27091158594306071283761971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36121544792408095045015961 27091158594306071283761971)
              ·
                refine ⟨40636737891459106925642957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27091158594306071283761971 40636737891459106925642957)
                ·
                  refine ⟨15238776709297165097116109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40636737891459106925642957 15238776709297165097116109)
                  ·
                    refine ⟨5714541265986436911418541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15238776709297165097116109 5714541265986436911418541)
                    ·
                      refine ⟨2142952974744913841781953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714541265986436911418541 2142952974744913841781953)
                      ·
                        rfl

theorem cell23_4173386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_4173386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173386 prefixEnd_4173386 := by exact prefixLift 4173386
  have htrace : WordTrace (prefixWord ++ tailWord_4173386) baseStart_4173386 baseEnd_4173386 := by
    simpa [prefixWord, tailWord_4173386, baseEnd_4173386] using wordTrace_append hprefix tailTrace_4173386
  have hstable : (prefixWord ++ tailWord_4173386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173386).length < 2 ^ (prefixWord ++ tailWord_4173386).sum := by decide
  have hdescent : baseEnd_4173386 < baseStart_4173386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173398 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4173398 : Nat := 118140960795 + 4173398 * 2 ^ 59
def prefixEnd_4173398 : Nat := 4983230072969 + 3 ^ 40 * 4173398 * 2
def baseEnd_4173398 : Nat := 2142959136512767794831899

theorem tailTrace_4173398 : CollatzResearch.WordTrace tailWord_4173398 prefixEnd_4173398 2142959136512767794831899 := by
  unfold tailWord_4173398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513520633406205029863553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101477553422999520318544565 9513520633406205029863553)
  ·
    refine ⟨7135140475054653772397665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9513520633406205029863553 7135140475054653772397665)
    ·
      refine ⟨5351355356290990329298249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7135140475054653772397665 5351355356290990329298249)
      ·
        refine ⟨4013516517218242746973687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5351355356290990329298249 4013516517218242746973687)
        ·
          refine ⟨6020274775827364120460531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013516517218242746973687 6020274775827364120460531)
          ·
            refine ⟨9030412163741046180690797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020274775827364120460531 9030412163741046180690797)
            ·
              refine ⟨3386404561402892317759049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9030412163741046180690797 3386404561402892317759049)
              ·
                refine ⟨2539803421052169238319287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386404561402892317759049 2539803421052169238319287)
                ·
                  refine ⟨3809705131578253857478931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539803421052169238319287 3809705131578253857478931)
                  ·
                    refine ⟨5714557697367380786218397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809705131578253857478931 5714557697367380786218397)
                    ·
                      refine ⟨2142959136512767794831899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714557697367380786218397 2142959136512767794831899)
                      ·
                        rfl

theorem cell23_4173398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4173398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173398 prefixEnd_4173398 := by exact prefixLift 4173398
  have htrace : WordTrace (prefixWord ++ tailWord_4173398) baseStart_4173398 baseEnd_4173398 := by
    simpa [prefixWord, tailWord_4173398, baseEnd_4173398] using wordTrace_append hprefix tailTrace_4173398
  have hstable : (prefixWord ++ tailWord_4173398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173398).length < 2 ^ (prefixWord ++ tailWord_4173398).sum := by decide
  have hdescent : baseEnd_4173398 < baseStart_4173398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173419 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 6, 6]
def baseStart_4173419 : Nat := 118140960795 + 4173419 * 2 ^ 59
def prefixEnd_4173419 : Nat := 4983230072969 + 3 ^ 40 * 4173419 * 2
def baseEnd_4173419 : Nat := 714323306535504070889767

theorem tailTrace_4173419 : CollatzResearch.WordTrace tailWord_4173419 prefixEnd_4173419 714323306535504070889767 := by
  unfold tailWord_4173419
  simp only [CollatzResearch.WordTrace]
  refine ⟨152217096067423201064331311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101478064044948800709554207 152217096067423201064331311)
  ·
    refine ⟨228325644101134801596496967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152217096067423201064331311 228325644101134801596496967)
    ·
      refine ⟨342488466151702202394745451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228325644101134801596496967 342488466151702202394745451)
      ·
        refine ⟨513732699227553303592118177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342488466151702202394745451 513732699227553303592118177)
        ·
          refine ⟨385299524420664977694088633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513732699227553303592118177 385299524420664977694088633)
          ·
            refine ⟨288974643315498733270566475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385299524420664977694088633 288974643315498733270566475)
            ·
              refine ⟨433461964973248099905849713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288974643315498733270566475 433461964973248099905849713)
              ·
                refine ⟨325096473729936074929387285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433461964973248099905849713 325096473729936074929387285)
                ·
                  refine ⟨15238897206090753512315029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 325096473729936074929387285 15238897206090753512315029)
                  ·
                    refine ⟨714323306535504070889767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15238897206090753512315029 714323306535504070889767)
                    ·
                      rfl

theorem cell23_4173419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_4173419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173419 prefixEnd_4173419 := by exact prefixLift 4173419
  have htrace : WordTrace (prefixWord ++ tailWord_4173419) baseStart_4173419 baseEnd_4173419 := by
    simpa [prefixWord, tailWord_4173419, baseEnd_4173419] using wordTrace_append hprefix tailTrace_4173419
  have hstable : (prefixWord ++ tailWord_4173419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173419).length < 2 ^ (prefixWord ++ tailWord_4173419).sum := by decide
  have hdescent : baseEnd_4173419 < baseStart_4173419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_4173439 : Nat := 118140960795 + 4173439 * 2 ^ 59
def prefixEnd_4173439 : Nat := 4983230072969 + 3 ^ 40 * 4173439 * 2
def baseEnd_4173439 : Nat := 2142980189219602134419209

theorem tailTrace_4173439 : CollatzResearch.WordTrace tailWord_4173439 prefixEnd_4173439 2142980189219602134419209 := by
  unfold tailWord_4173439
  simp only [CollatzResearch.WordTrace]
  refine ⟨152217825527350744480059371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101478550351567162986706247 152217825527350744480059371)
  ·
    refine ⟨228326738291026116720089057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152217825527350744480059371 228326738291026116720089057)
    ·
      refine ⟨171245053718269587540066793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228326738291026116720089057 171245053718269587540066793)
      ·
        refine ⟨128433790288702190655050095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171245053718269587540066793 128433790288702190655050095)
        ·
          refine ⟨192650685433053285982575143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128433790288702190655050095 192650685433053285982575143)
          ·
            refine ⟨288976028149579928973862715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192650685433053285982575143 288976028149579928973862715)
            ·
              refine ⟨433464042224369893460794073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288976028149579928973862715 433464042224369893460794073)
              ·
                refine ⟨325098031668277420095595555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433464042224369893460794073 325098031668277420095595555)
                ·
                  refine ⟨487647047502416130143393333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325098031668277420095595555 487647047502416130143393333)
                  ·
                    refine ⟨45716910703351512200943125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 487647047502416130143393333 45716910703351512200943125)
                    ·
                      refine ⟨2142980189219602134419209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45716910703351512200943125 2142980189219602134419209)
                      ·
                        rfl

theorem cell23_4173439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_4173439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173439 prefixEnd_4173439 := by exact prefixLift 4173439
  have htrace : WordTrace (prefixWord ++ tailWord_4173439) baseStart_4173439 baseEnd_4173439 := by
    simpa [prefixWord, tailWord_4173439, baseEnd_4173439] using wordTrace_append hprefix tailTrace_4173439
  have hstable : (prefixWord ++ tailWord_4173439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173439).length < 2 ^ (prefixWord ++ tailWord_4173439).sum := by decide
  have hdescent : baseEnd_4173439 < baseStart_4173439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173447 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_4173447 : Nat := 118140960795 + 4173447 * 2 ^ 59
def prefixEnd_4173447 : Nat := 4983230072969 + 3 ^ 40 * 4173447 * 2
def baseEnd_4173447 : Nat := 2142984297064838103119173

theorem tailTrace_4173447 : CollatzResearch.WordTrace tailWord_4173447 prefixEnd_4173447 2142984297064838103119173 := by
  unfold tailWord_4173447
  simp only [CollatzResearch.WordTrace]
  refine ⟨152218117311321761846350595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101478744874214507897567063 152218117311321761846350595)
  ·
    refine ⟨228327175966982642769525893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152218117311321761846350595 228327175966982642769525893)
    ·
      refine ⟨42811345493809245519286105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228327175966982642769525893 42811345493809245519286105)
      ·
        refine ⟨32108509120356934139464579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42811345493809245519286105 32108509120356934139464579)
        ·
          refine ⟨48162763680535401209196869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32108509120356934139464579 48162763680535401209196869)
          ·
            refine ⟨9030518190100387726724413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48162763680535401209196869 9030518190100387726724413)
            ·
              refine ⟨3386444321287645397521655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9030518190100387726724413 3386444321287645397521655)
              ·
                refine ⟨5079666481931468096282483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386444321287645397521655 5079666481931468096282483)
                ·
                  refine ⟨7619499722897202144423725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079666481931468096282483 7619499722897202144423725)
                  ·
                    refine ⟨2857312396086450804158897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7619499722897202144423725 2857312396086450804158897)
                    ·
                      refine ⟨2142984297064838103119173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857312396086450804158897 2142984297064838103119173)
                      ·
                        rfl

theorem cell23_4173447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_4173447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173447 prefixEnd_4173447 := by exact prefixLift 4173447
  have htrace : WordTrace (prefixWord ++ tailWord_4173447) baseStart_4173447 baseEnd_4173447 := by
    simpa [prefixWord, tailWord_4173447, baseEnd_4173447] using wordTrace_append hprefix tailTrace_4173447
  have hstable : (prefixWord ++ tailWord_4173447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173447).length < 2 ^ (prefixWord ++ tailWord_4173447).sum := by decide
  have hdescent : baseEnd_4173447 < baseStart_4173447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173473 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4173473 : Nat := 118140960795 + 4173473 * 2 ^ 59
def prefixEnd_4173473 : Nat := 4983230072969 + 3 ^ 40 * 4173473 * 2
def baseEnd_4173473 : Nat := 2142997647561855001394053

theorem tailTrace_4173473 : CollatzResearch.WordTrace tailWord_4173473 prefixEnd_4173473 2142997647561855001394053 := by
  unfold tailWord_4173473
  simp only [CollatzResearch.WordTrace]
  refine ⟨152219065609227568286797073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101479377072818378857864715 152219065609227568286797073)
  ·
    refine ⟨114164299206920676215097805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152219065609227568286797073 114164299206920676215097805)
    ·
      refine ⟨42811612202595253580661677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114164299206920676215097805 42811612202595253580661677)
      ·
        refine ⟨16054354575973220092748129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42811612202595253580661677 16054354575973220092748129)
        ·
          refine ⟨12040765931979915069561097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16054354575973220092748129 12040765931979915069561097)
          ·
            refine ⟨9030574448984936302170823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12040765931979915069561097 9030574448984936302170823)
            ·
              refine ⟨13545861673477404453256235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030574448984936302170823 13545861673477404453256235)
              ·
                refine ⟨20318792510216106679884353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545861673477404453256235 20318792510216106679884353)
                ·
                  refine ⟨15239094382662080009913265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20318792510216106679884353 15239094382662080009913265)
                  ·
                    refine ⟨11429320786996560007434949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15239094382662080009913265 11429320786996560007434949)
                    ·
                      refine ⟨2142997647561855001394053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11429320786996560007434949 2142997647561855001394053)
                      ·
                        rfl

theorem cell23_4173473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4173473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173473 prefixEnd_4173473 := by exact prefixLift 4173473
  have htrace : WordTrace (prefixWord ++ tailWord_4173473) baseStart_4173473 baseEnd_4173473 := by
    simpa [prefixWord, tailWord_4173473, baseEnd_4173473] using wordTrace_append hprefix tailTrace_4173473
  have hstable : (prefixWord ++ tailWord_4173473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173473).length < 2 ^ (prefixWord ++ tailWord_4173473).sum := by decide
  have hdescent : baseEnd_4173473 < baseStart_4173473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173500 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 5]
def baseStart_4173500 : Nat := 118140960795 + 4173500 * 2 ^ 59
def prefixEnd_4173500 : Nat := 4983230072969 + 3 ^ 40 * 4173500 * 2
def baseEnd_4173500 : Nat := 238112390171058488417381

theorem tailTrace_4173500 : CollatzResearch.WordTrace tailWord_4173500 prefixEnd_4173500 238112390171058488417381 := by
  unfold tailWord_4173500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76110025190064875949014977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101480033586753167932019969 76110025190064875949014977)
  ·
    refine ⟨57082518892548656961761233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76110025190064875949014977 57082518892548656961761233)
    ·
      refine ⟨42811889169411492721320925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57082518892548656961761233 42811889169411492721320925)
      ·
        refine ⟨16054458438529309770495347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42811889169411492721320925 16054458438529309770495347)
        ·
          refine ⟨24081687657793964655743021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16054458438529309770495347 24081687657793964655743021)
          ·
            refine ⟨9030632871672736745903633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24081687657793964655743021 9030632871672736745903633)
            ·
              refine ⟨6772974653754552559427725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030632871672736745903633 6772974653754552559427725)
              ·
                refine ⟨2539865495157957209785397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6772974653754552559427725 2539865495157957209785397)
                ·
                  refine ⟨238112390171058488417381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539865495157957209785397 238112390171058488417381)
                  ·
                    rfl

theorem cell23_4173500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_4173500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173500 prefixEnd_4173500 := by exact prefixLift 4173500
  have htrace : WordTrace (prefixWord ++ tailWord_4173500) baseStart_4173500 baseEnd_4173500 := by
    simpa [prefixWord, tailWord_4173500, baseEnd_4173500] using wordTrace_append hprefix tailTrace_4173500
  have hstable : (prefixWord ++ tailWord_4173500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173500).length < 2 ^ (prefixWord ++ tailWord_4173500).sum := by decide
  have hdescent : baseEnd_4173500 < baseStart_4173500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173517 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4173517 : Nat := 118140960795 + 4173517 * 2 ^ 59
def prefixEnd_4173517 : Nat := 4983230072969 + 3 ^ 40 * 4173517 * 2
def baseEnd_4173517 : Nat := 238113360078961425471539

theorem tailTrace_4173517 : CollatzResearch.WordTrace tailWord_4173517 prefixEnd_4173517 238113360078961425471539 := by
  unfold tailWord_4173517
  simp only [CollatzResearch.WordTrace]
  refine ⟨152220670421068163801398805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101480446947378775867599203 152220670421068163801398805)
  ·
    refine ⟨7135343925987570178190569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152220670421068163801398805 7135343925987570178190569)
    ·
      refine ⟨5351507944490677633642927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7135343925987570178190569 5351507944490677633642927)
      ·
        refine ⟨8027261916736016450464391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351507944490677633642927 8027261916736016450464391)
        ·
          refine ⟨12040892875104024675696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027261916736016450464391 12040892875104024675696587)
          ·
            refine ⟨18061339312656037013544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040892875104024675696587 18061339312656037013544881)
            ·
              refine ⟨13546004484492027760158661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18061339312656037013544881 13546004484492027760158661)
              ·
                refine ⟨2539875840842255205029749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13546004484492027760158661 2539875840842255205029749)
                ·
                  refine ⟨238113360078961425471539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2539875840842255205029749 238113360078961425471539)
                  ·
                    rfl

theorem cell23_4173517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4173517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173517 prefixEnd_4173517 := by exact prefixLift 4173517
  have htrace : WordTrace (prefixWord ++ tailWord_4173517) baseStart_4173517 baseEnd_4173517 := by
    simpa [prefixWord, tailWord_4173517, baseEnd_4173517] using wordTrace_append hprefix tailTrace_4173517
  have hstable : (prefixWord ++ tailWord_4173517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173517).length < 2 ^ (prefixWord ++ tailWord_4173517).sum := by decide
  have hdescent : baseEnd_4173517 < baseStart_4173517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173553 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_4173553 : Nat := 118140960795 + 4173553 * 2 ^ 59
def prefixEnd_4173553 : Nat := 4983230072969 + 3 ^ 40 * 4173553 * 2
def baseEnd_4173553 : Nat := 2143038726014214688393685

theorem tailTrace_4173553 : CollatzResearch.WordTrace tailWord_4173553 prefixEnd_4173553 2143038726014214688393685 := by
  unfold tailWord_4173553
  simp only [CollatzResearch.WordTrace]
  refine ⟨152221983448937741949709313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101481322299291827966472875 152221983448937741949709313)
  ·
    refine ⟨114166487586703306462281985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152221983448937741949709313 114166487586703306462281985)
    ·
      refine ⟨85624865690027479846711489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114166487586703306462281985 85624865690027479846711489)
      ·
        refine ⟨64218649267520609885033617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85624865690027479846711489 64218649267520609885033617)
        ·
          refine ⟨48163986950640457413775213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64218649267520609885033617 48163986950640457413775213)
          ·
            refine ⟨18061495106490171530165705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48163986950640457413775213 18061495106490171530165705)
            ·
              refine ⟨13546121329867628647624279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18061495106490171530165705 13546121329867628647624279)
              ·
                refine ⟨20319181994801442971436419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13546121329867628647624279 20319181994801442971436419)
                ·
                  refine ⟨30478772992202164457154629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20319181994801442971436419 30478772992202164457154629)
                  ·
                    refine ⟨5714769936037905835716493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30478772992202164457154629 5714769936037905835716493)
                    ·
                      refine ⟨2143038726014214688393685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714769936037905835716493 2143038726014214688393685)
                      ·
                        rfl

theorem cell23_4173553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_4173553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173553 prefixEnd_4173553 := by exact prefixLift 4173553
  have htrace : WordTrace (prefixWord ++ tailWord_4173553) baseStart_4173553 baseEnd_4173553 := by
    simpa [prefixWord, tailWord_4173553, baseEnd_4173553] using wordTrace_append hprefix tailTrace_4173553
  have hstable : (prefixWord ++ tailWord_4173553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173553).length < 2 ^ (prefixWord ++ tailWord_4173553).sum := by decide
  have hdescent : baseEnd_4173553 < baseStart_4173553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173560 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 1, 4]
def baseStart_4173560 : Nat := 118140960795 + 4173560 * 2 ^ 59
def prefixEnd_4173560 : Nat := 4983230072969 + 3 ^ 40 * 4173560 * 2
def baseEnd_4173560 : Nat := 714347440126265387002051

theorem tailTrace_4173560 : CollatzResearch.WordTrace tailWord_4173560 prefixEnd_4173560 714347440126265387002051 := by
  unfold tailWord_4173560
  simp only [CollatzResearch.WordTrace]
  refine ⟨76111119379956191072607067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101481492506608254763476089 76111119379956191072607067)
  ·
    refine ⟨114166679069934286608910601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76111119379956191072607067 114166679069934286608910601)
    ·
      refine ⟨85625009302450714956682951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114166679069934286608910601 85625009302450714956682951)
      ·
        refine ⟨128437513953676072435024427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85625009302450714956682951 128437513953676072435024427)
        ·
          refine ⟨192656270930514108652536641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128437513953676072435024427 192656270930514108652536641)
          ·
            refine ⟨144492203197885581489402481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192656270930514108652536641 144492203197885581489402481)
            ·
              refine ⟨108369152398414186117051861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144492203197885581489402481 108369152398414186117051861)
              ·
                refine ⟨2539902009337832487118403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108369152398414186117051861 2539902009337832487118403)
                ·
                  refine ⟨3809853014006748730677605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2539902009337832487118403 3809853014006748730677605)
                  ·
                    refine ⟨714347440126265387002051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3809853014006748730677605 714347440126265387002051)
                    ·
                      rfl

theorem cell23_4173560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_4173560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173560 prefixEnd_4173560 := by exact prefixLift 4173560
  have htrace : WordTrace (prefixWord ++ tailWord_4173560) baseStart_4173560 baseEnd_4173560 := by
    simpa [prefixWord, tailWord_4173560, baseEnd_4173560] using wordTrace_append hprefix tailTrace_4173560
  have hstable : (prefixWord ++ tailWord_4173560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173560).length < 2 ^ (prefixWord ++ tailWord_4173560).sum := by decide
  have hdescent : baseEnd_4173560 < baseStart_4173560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173600 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4173600 : Nat := 118140960795 + 4173600 * 2 ^ 59
def prefixEnd_4173600 : Nat := 4983230072969 + 3 ^ 40 * 4173600 * 2
def baseEnd_4173600 : Nat := 2143062859604976004505969

theorem tailTrace_4173600 : CollatzResearch.WordTrace tailWord_4173600 prefixEnd_4173600 2143062859604976004505969 := by
  unfold tailWord_4173600
  simp only [CollatzResearch.WordTrace]
  refine ⟨76111848839883734488335127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101482465119844979317780169 76111848839883734488335127)
  ·
    refine ⟨114167773259825601732502691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76111848839883734488335127 114167773259825601732502691)
    ·
      refine ⟨171251659889738402598754037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114167773259825601732502691 171251659889738402598754037)
      ·
        refine ⟨16054843114662975243633191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171251659889738402598754037 16054843114662975243633191)
        ·
          refine ⟨24082264671994462865449787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16054843114662975243633191 24082264671994462865449787)
          ·
            refine ⟨36123397007991694298174681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24082264671994462865449787 36123397007991694298174681)
            ·
              refine ⟨27092547755993770723631011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36123397007991694298174681 27092547755993770723631011)
              ·
                refine ⟨40638821633990656085446517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27092547755993770723631011 40638821633990656085446517)
                ·
                  refine ⟨3809889528186624008010611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40638821633990656085446517 3809889528186624008010611)
                  ·
                    refine ⟨5714834292279936012015917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3809889528186624008010611 5714834292279936012015917)
                    ·
                      refine ⟨2143062859604976004505969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5714834292279936012015917 2143062859604976004505969)
                      ·
                        rfl

theorem cell23_4173600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4173600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173600 prefixEnd_4173600 := by exact prefixLift 4173600
  have htrace : WordTrace (prefixWord ++ tailWord_4173600) baseStart_4173600 baseEnd_4173600 := by
    simpa [prefixWord, tailWord_4173600, baseEnd_4173600] using wordTrace_append hprefix tailTrace_4173600
  have hstable : (prefixWord ++ tailWord_4173600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173600).length < 2 ^ (prefixWord ++ tailWord_4173600).sum := by decide
  have hdescent : baseEnd_4173600 < baseStart_4173600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173650 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_4173650 : Nat := 118140960795 + 4173650 * 2 ^ 59
def prefixEnd_4173650 : Nat := 4983230072969 + 3 ^ 40 * 4173650 * 2
def baseEnd_4173650 : Nat := 714362844545900269626913

theorem tailTrace_4173650 : CollatzResearch.WordTrace tailWord_4173650 prefixEnd_4173650 714362844545900269626913 := by
  unfold tailWord_4173650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38056380332396581878997601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101483680886390885010660269 38056380332396581878997601)
  ·
    refine ⟨28542285249297436409248201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38056380332396581878997601 28542285249297436409248201)
    ·
      refine ⟨21406713936973077306936151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28542285249297436409248201 21406713936973077306936151)
      ·
        refine ⟨32110070905459615960404227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21406713936973077306936151 32110070905459615960404227)
        ·
          refine ⟨48165106358189423940606341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32110070905459615960404227 48165106358189423940606341)
          ·
            refine ⟨9030957442160516988863689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48165106358189423940606341 9030957442160516988863689)
            ·
              refine ⟨6773218081620387741647767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9030957442160516988863689 6773218081620387741647767)
              ·
                refine ⟨10159827122430581612471651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773218081620387741647767 10159827122430581612471651)
                ·
                  refine ⟨15239740683645872418707477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159827122430581612471651 15239740683645872418707477)
                  ·
                    refine ⟨714362844545900269626913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15239740683645872418707477 714362844545900269626913)
                    ·
                      rfl

theorem cell23_4173650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_4173650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173650 prefixEnd_4173650 := by exact prefixLift 4173650
  have htrace : WordTrace (prefixWord ++ tailWord_4173650) baseStart_4173650 baseEnd_4173650 := by
    simpa [prefixWord, tailWord_4173650, baseEnd_4173650] using wordTrace_append hprefix tailTrace_4173650
  have hstable : (prefixWord ++ tailWord_4173650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173650).length < 2 ^ (prefixWord ++ tailWord_4173650).sum := by decide
  have hdescent : baseEnd_4173650 < baseStart_4173650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173657 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 3, 2, 2]
def baseStart_4173657 : Nat := 118140960795 + 4173657 * 2 ^ 59
def prefixEnd_4173657 : Nat := 4983230072969 + 3 ^ 40 * 4173657 * 2
def baseEnd_4173657 : Nat := 2143092128002282281493207

theorem tailTrace_4173657 : CollatzResearch.WordTrace tailWord_4173657 prefixEnd_4173657 2143092128002282281493207 := by
  unfold tailWord_4173657
  simp only [CollatzResearch.WordTrace]
  refine ⟨152225776640560967711495225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101483851093707311807663483 152225776640560967711495225)
  ·
    refine ⟨114169332480420725783621419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152225776640560967711495225 114169332480420725783621419)
    ·
      refine ⟨171253998720631088675432129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114169332480420725783621419 171253998720631088675432129)
      ·
        refine ⟨128440499040473316506574097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171253998720631088675432129 128440499040473316506574097)
        ·
          refine ⟨96330374280354987379930573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128440499040473316506574097 96330374280354987379930573)
          ·
            refine ⟨36123890355133120267473965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96330374280354987379930573 36123890355133120267473965)
            ·
              refine ⟨13546458883174920100302737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36123890355133120267473965 13546458883174920100302737)
              ·
                refine ⟨10159844162381190075227053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13546458883174920100302737 10159844162381190075227053)
                ·
                  refine ⟨3809941560892946278210145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10159844162381190075227053 3809941560892946278210145)
                  ·
                    refine ⟨2857456170669709708657609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3809941560892946278210145 2857456170669709708657609)
                    ·
                      refine ⟨2143092128002282281493207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857456170669709708657609 2143092128002282281493207)
                      ·
                        rfl

theorem cell23_4173657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_4173657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173657 prefixEnd_4173657 := by exact prefixLift 4173657
  have htrace : WordTrace (prefixWord ++ tailWord_4173657) baseStart_4173657 baseEnd_4173657 := by
    simpa [prefixWord, tailWord_4173657, baseEnd_4173657] using wordTrace_append hprefix tailTrace_4173657
  have hstable : (prefixWord ++ tailWord_4173657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173657).length < 2 ^ (prefixWord ++ tailWord_4173657).sum := by decide
  have hdescent : baseEnd_4173657 < baseStart_4173657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173674 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4173674 : Nat := 118140960795 + 4173674 * 2 ^ 59
def prefixEnd_4173674 : Nat := 4983230072969 + 3 ^ 40 * 4173674 * 2
def baseEnd_4173674 : Nat := 2143100857173408714980629

theorem tailTrace_4173674 : CollatzResearch.WordTrace tailWord_4173674 prefixEnd_4173674 2143100857173408714980629 := by
  unfold tailWord_4173674
  simp only [CollatzResearch.WordTrace]
  refine ⟨38056599170374844903716019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101484264454332919743242717 38056599170374844903716019)
  ·
    refine ⟨57084898755562267355574029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38056599170374844903716019 57084898755562267355574029)
    ·
      refine ⟨21406837033335850258340261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57084898755562267355574029 21406837033335850258340261)
      ·
        refine ⟨4013781943750471923438799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21406837033335850258340261 4013781943750471923438799)
        ·
          refine ⟨6020672915625707885158199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013781943750471923438799 6020672915625707885158199)
          ·
            refine ⟨9031009373438561827737299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020672915625707885158199 9031009373438561827737299)
            ·
              refine ⟨13546514060157842741605949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031009373438561827737299 13546514060157842741605949)
              ·
                refine ⟨5079942772559191028102231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13546514060157842741605949 5079942772559191028102231)
                ·
                  refine ⟨7619914158838786542153347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5079942772559191028102231 7619914158838786542153347)
                  ·
                    refine ⟨11429871238258179813230021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7619914158838786542153347 11429871238258179813230021)
                    ·
                      refine ⟨2143100857173408714980629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11429871238258179813230021 2143100857173408714980629)
                      ·
                        rfl

theorem cell23_4173674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4173674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173674 prefixEnd_4173674 := by exact prefixLift 4173674
  have htrace : WordTrace (prefixWord ++ tailWord_4173674) baseStart_4173674 baseEnd_4173674 := by
    simpa [prefixWord, tailWord_4173674, baseEnd_4173674] using wordTrace_append hprefix tailTrace_4173674
  have hstable : (prefixWord ++ tailWord_4173674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173674).length < 2 ^ (prefixWord ++ tailWord_4173674).sum := by decide
  have hdescent : baseEnd_4173674 < baseStart_4173674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173704 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_4173704 : Nat := 118140960795 + 4173704 * 2 ^ 59
def prefixEnd_4173704 : Nat := 4983230072969 + 3 ^ 40 * 4173704 * 2
def baseEnd_4173704 : Nat := 2143116261593043597605491

theorem tailTrace_4173704 : CollatzResearch.WordTrace tailWord_4173704 prefixEnd_4173704 2143116261593043597605491 := by
  unfold tailWord_4173704
  simp only [CollatzResearch.WordTrace]
  refine ⟨76113745435695347369228083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101484993914260463158970777 76113745435695347369228083)
  ·
    refine ⟨114170618153543021053842125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76113745435695347369228083 114170618153543021053842125)
    ·
      refine ⟨42813981807578632895190797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114170618153543021053842125 42813981807578632895190797)
      ·
        refine ⟨16055243177841987335696549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42813981807578632895190797 16055243177841987335696549)
        ·
          refine ⟨3010358095845372625443103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16055243177841987335696549 3010358095845372625443103)
          ·
            refine ⟨4515537143768058938164655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010358095845372625443103 4515537143768058938164655)
            ·
              refine ⟨6773305715652088407246983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515537143768058938164655 6773305715652088407246983)
              ·
                refine ⟨10159958573478132610870475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773305715652088407246983 10159958573478132610870475)
                ·
                  refine ⟨15239937860217198916305713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10159958573478132610870475 15239937860217198916305713)
                  ·
                    refine ⟨11429953395162899187229285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15239937860217198916305713 11429953395162899187229285)
                    ·
                      refine ⟨2143116261593043597605491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11429953395162899187229285 2143116261593043597605491)
                      ·
                        rfl

theorem cell23_4173704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_4173704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173704 prefixEnd_4173704 := by exact prefixLift 4173704
  have htrace : WordTrace (prefixWord ++ tailWord_4173704) baseStart_4173704 baseEnd_4173704 := by
    simpa [prefixWord, tailWord_4173704, baseEnd_4173704] using wordTrace_append hprefix tailTrace_4173704
  have hstable : (prefixWord ++ tailWord_4173704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173704).length < 2 ^ (prefixWord ++ tailWord_4173704).sum := by decide
  have hdescent : baseEnd_4173704 < baseStart_4173704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173713 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_4173713 : Nat := 118140960795 + 4173713 * 2 ^ 59
def prefixEnd_4173713 : Nat := 4983230072969 + 3 ^ 40 * 4173713 * 2
def baseEnd_4173713 : Nat := 2143120882918934062392949

theorem tailTrace_4173713 : CollatzResearch.WordTrace tailWord_4173713 prefixEnd_4173713 2143120882918934062392949 := by
  unfold tailWord_4173713
  simp only [CollatzResearch.WordTrace]
  refine ⟨152227819128358089275533793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101485212752238726183689195 152227819128358089275533793)
  ·
    refine ⟨114170864346268566956650345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152227819128358089275533793 114170864346268566956650345)
    ·
      refine ⟨85628148259701425217487759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114170864346268566956650345 85628148259701425217487759)
      ·
        refine ⟨128442222389552137826231639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85628148259701425217487759 128442222389552137826231639)
        ·
          refine ⟨192663333584328206739347459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128442222389552137826231639 192663333584328206739347459)
          ·
            refine ⟨288995000376492310109021189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192663333584328206739347459 288995000376492310109021189)
            ·
              refine ⟨54186562570592308145441473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288995000376492310109021189 54186562570592308145441473)
              ·
                refine ⟨40639921927944231109081105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54186562570592308145441473 40639921927944231109081105)
                ·
                  refine ⟨30479941445958173331810829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40639921927944231109081105 30479941445958173331810829)
                  ·
                    refine ⟨11429978042234314999429061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30479941445958173331810829 11429978042234314999429061)
                    ·
                      refine ⟨2143120882918934062392949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11429978042234314999429061 2143120882918934062392949)
                      ·
                        rfl

theorem cell23_4173713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_4173713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173713 prefixEnd_4173713 := by exact prefixLift 4173713
  have htrace : WordTrace (prefixWord ++ tailWord_4173713) baseStart_4173713 baseEnd_4173713 := by
    simpa [prefixWord, tailWord_4173713, baseEnd_4173713] using wordTrace_append hprefix tailTrace_4173713
  have hstable : (prefixWord ++ tailWord_4173713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173713).length < 2 ^ (prefixWord ++ tailWord_4173713).sum := by decide
  have hdescent : baseEnd_4173713 < baseStart_4173713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173742 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4173742 : Nat := 118140960795 + 4173742 * 2 ^ 59
def prefixEnd_4173742 : Nat := 4983230072969 + 3 ^ 40 * 4173742 * 2
def baseEnd_4173742 : Nat := 2143135773857914448930317

theorem tailTrace_4173742 : CollatzResearch.WordTrace tailWord_4173742 prefixEnd_4173742 2143135773857914448930317 := by
  unfold tailWord_4173742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028609605656628403542435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101485917896835351485559653 19028609605656628403542435)
  ·
    refine ⟨28542914408484942605313653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028609605656628403542435 28542914408484942605313653)
    ·
      refine ⟨2675898225795463369248155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28542914408484942605313653 2675898225795463369248155)
      ·
        refine ⟨4013847338693195053872233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675898225795463369248155 4013847338693195053872233)
        ·
          refine ⟨3010385504019896290404175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4013847338693195053872233 3010385504019896290404175)
          ·
            refine ⟨4515578256029844435606263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010385504019896290404175 4515578256029844435606263)
            ·
              refine ⟨6773367384044766653409395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515578256029844435606263 6773367384044766653409395)
              ·
                refine ⟨10160051076067149980114093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6773367384044766653409395 10160051076067149980114093)
                ·
                  refine ⟨3810019153525181242542785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10160051076067149980114093 3810019153525181242542785)
                  ·
                    refine ⟨2857514365143885931907089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810019153525181242542785 2857514365143885931907089)
                    ·
                      refine ⟨2143135773857914448930317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857514365143885931907089 2143135773857914448930317)
                      ·
                        rfl

theorem cell23_4173742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4173742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173742 prefixEnd_4173742 := by exact prefixLift 4173742
  have htrace : WordTrace (prefixWord ++ tailWord_4173742) baseStart_4173742 baseEnd_4173742 := by
    simpa [prefixWord, tailWord_4173742, baseEnd_4173742] using wordTrace_append hprefix tailTrace_4173742
  have hstable : (prefixWord ++ tailWord_4173742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173742).length < 2 ^ (prefixWord ++ tailWord_4173742).sum := by decide
  have hdescent : baseEnd_4173742 < baseStart_4173742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173747 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 4, 2, 2]
def baseStart_4173747 : Nat := 118140960795 + 4173747 * 2 ^ 59
def prefixEnd_4173747 : Nat := 4983230072969 + 3 ^ 40 * 4173747 * 2
def baseEnd_4173747 : Nat := 2143138341261186929367793

theorem tailTrace_4173747 : CollatzResearch.WordTrace tailWord_4173747 prefixEnd_4173747 2143138341261186929367793 := by
  unfold tailWord_4173747
  simp only [CollatzResearch.WordTrace]
  refine ⟨152229059210234913082271495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101486039473489942054847663 152229059210234913082271495)
  ·
    refine ⟨228343588815352369623407243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152229059210234913082271495 228343588815352369623407243)
    ·
      refine ⟨342515383223028554435110865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228343588815352369623407243 342515383223028554435110865)
      ·
        refine ⟨256886537417271415826333149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342515383223028554435110865 256886537417271415826333149)
        ·
          refine ⟨96332451531476780934874931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256886537417271415826333149 96332451531476780934874931)
          ·
            refine ⟨144498677297215171402312397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96332451531476780934874931 144498677297215171402312397)
            ·
              refine ⟨54187003986455689275867149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144498677297215171402312397 54187003986455689275867149)
              ·
                refine ⟨20320126494920883478450181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54187003986455689275867149 20320126494920883478450181)
                ·
                  refine ⟨3810023717797665652209409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20320126494920883478450181 3810023717797665652209409)
                  ·
                    refine ⟨2857517788348249239157057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3810023717797665652209409 2857517788348249239157057)
                    ·
                      refine ⟨2143138341261186929367793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2857517788348249239157057 2143138341261186929367793)
                      ·
                        rfl

theorem cell23_4173747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 2, 2].length) (baseStart_4173747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173747 prefixEnd_4173747 := by exact prefixLift 4173747
  have htrace : WordTrace (prefixWord ++ tailWord_4173747) baseStart_4173747 baseEnd_4173747 := by
    simpa [prefixWord, tailWord_4173747, baseEnd_4173747] using wordTrace_append hprefix tailTrace_4173747
  have hstable : (prefixWord ++ tailWord_4173747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173747).length < 2 ^ (prefixWord ++ tailWord_4173747).sum := by decide
  have hdescent : baseEnd_4173747 < baseStart_4173747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173814 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4173814 : Nat := 118140960795 + 4173814 * 2 ^ 59
def prefixEnd_4173814 : Nat := 4983230072969 + 3 ^ 40 * 4173814 * 2
def baseEnd_4173814 : Nat := 2143172744465038167229985

theorem tailTrace_4173814 : CollatzResearch.WordTrace tailWord_4173814 prefixEnd_4173814 2143172744465038167229985 := by
  unfold tailWord_4173814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514468931312011470310031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101487668600661455683306997 9514468931312011470310031)
  ·
    refine ⟨14271703396968017205465047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9514468931312011470310031 14271703396968017205465047)
    ·
      refine ⟨21407555095452025808197571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14271703396968017205465047 21407555095452025808197571)
      ·
        refine ⟨32111332643178038712296357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21407555095452025808197571 32111332643178038712296357)
        ·
          refine ⟨6020874870595882258555567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32111332643178038712296357 6020874870595882258555567)
          ·
            refine ⟨9031312305893823387833351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020874870595882258555567 9031312305893823387833351)
            ·
              refine ⟨13546968458840735081750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9031312305893823387833351 13546968458840735081750027)
              ·
                refine ⟨20320452688261102622625041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13546968458840735081750027 20320452688261102622625041)
                ·
                  refine ⟨15240339516195826966968781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20320452688261102622625041 15240339516195826966968781)
                  ·
                    refine ⟨5715127318573435112613293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15240339516195826966968781 5715127318573435112613293)
                    ·
                      refine ⟨2143172744465038167229985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5715127318573435112613293 2143172744465038167229985)
                      ·
                        rfl

theorem cell23_4173814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4173814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173814 prefixEnd_4173814 := by exact prefixLift 4173814
  have htrace : WordTrace (prefixWord ++ tailWord_4173814) baseStart_4173814 baseEnd_4173814 := by
    simpa [prefixWord, tailWord_4173814, baseEnd_4173814] using wordTrace_append hprefix tailTrace_4173814
  have hstable : (prefixWord ++ tailWord_4173814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173814).length < 2 ^ (prefixWord ++ tailWord_4173814).sum := by decide
  have hdescent : baseEnd_4173814 < baseStart_4173814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4173820 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_4173820 : Nat := 118140960795 + 4173820 * 2 ^ 59
def prefixEnd_4173820 : Nat := 4983230072969 + 3 ^ 40 * 4173820 * 2
def baseEnd_4173820 : Nat := 2143175825348965143754957

theorem tailTrace_4173820 : CollatzResearch.WordTrace tailWord_4173820 prefixEnd_4173820 2143175825348965143754957 := by
  unfold tailWord_4173820
  simp only [CollatzResearch.WordTrace]
  refine ⟨76115860869485223274839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101487814492646964366452609 76115860869485223274839457)
  ·
    refine ⟨57086895652113917456129593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76115860869485223274839457 57086895652113917456129593)
    ·
      refine ⟨42815171739085438092097195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57086895652113917456129593 42815171739085438092097195)
      ·
        refine ⟨64222757608628157138145793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42815171739085438092097195 64222757608628157138145793)
        ·
          refine ⟨48167068206471117853609345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64222757608628157138145793 48167068206471117853609345)
          ·
            refine ⟨36125301154853338390207009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48167068206471117853609345 36125301154853338390207009)
            ·
              refine ⟨27093975866140003792655257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36125301154853338390207009 27093975866140003792655257)
              ·
                refine ⟨20320481899605002844491443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27093975866140003792655257 20320481899605002844491443)
                ·
                  refine ⟨30480722849407504266737165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20320481899605002844491443 30480722849407504266737165)
                  ·
                    refine ⟨11430271068527814100026437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30480722849407504266737165 11430271068527814100026437)
                    ·
                      refine ⟨2143175825348965143754957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11430271068527814100026437 2143175825348965143754957)
                      ·
                        rfl

theorem cell23_4173820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_4173820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4173820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4173820 prefixEnd_4173820 := by exact prefixLift 4173820
  have htrace : WordTrace (prefixWord ++ tailWord_4173820) baseStart_4173820 baseEnd_4173820 := by
    simpa [prefixWord, tailWord_4173820, baseEnd_4173820] using wordTrace_append hprefix tailTrace_4173820
  have hstable : (prefixWord ++ tailWord_4173820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4173820).length < 2 ^ (prefixWord ++ tailWord_4173820).sum := by decide
  have hdescent : baseEnd_4173820 < baseStart_4173820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4173820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
