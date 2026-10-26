import V185TrunkScan22Chunk054

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_494055 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 4]
def baseStart_494055 : Nat := 118140960795 + 494055 * 2 ^ 59
def prefixEnd_494055 : Nat := 4983230072969 + 3 ^ 40 * 494055 * 2
def baseEnd_494055 : Nat := 56375041057148831386753

theorem tailTrace_494055 : CollatzResearch.WordTrace tailWord_494055 prefixEnd_494055 56375041057148831386753 := by
  unfold tailWord_494055
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019666225130587721443619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12013110816753725147629079 18019666225130587721443619)
  ·
    refine ⟨27029499337695881582165429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18019666225130587721443619 27029499337695881582165429)
    ·
      refine ⟨2534015562908988898328009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27029499337695881582165429 2534015562908988898328009)
      ·
        refine ⟨1900511672181741673746007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2534015562908988898328009 1900511672181741673746007)
        ·
          refine ⟨2850767508272612510619011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900511672181741673746007 2850767508272612510619011)
          ·
            refine ⟨4276151262408918765928517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850767508272612510619011 4276151262408918765928517)
            ·
              refine ⟨801778361701672268611597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4276151262408918765928517 801778361701672268611597)
              ·
                refine ⟨300666885638127100729349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801778361701672268611597 300666885638127100729349)
                ·
                  refine ⟨56375041057148831386753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300666885638127100729349 56375041057148831386753)
                  ·
                    rfl

theorem cell22_494055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 4].length) (baseStart_494055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494055 prefixEnd_494055 := by exact prefixLift 494055
  have htrace : WordTrace (prefixWord ++ tailWord_494055) baseStart_494055 baseEnd_494055 := by
    simpa [prefixWord, tailWord_494055, baseEnd_494055] using wordTrace_append hprefix tailTrace_494055
  have hstable : (prefixWord ++ tailWord_494055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494055).length < 2 ^ (prefixWord ++ tailWord_494055).sum := by decide
  have hdescent : baseEnd_494055 < baseStart_494055 := by decide
  rcases family_descends (prefixWord ++ tailWord_494055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494070 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_494070 : Nat := 118140960795 + 494070 * 2 ^ 59
def prefixEnd_494070 : Nat := 4983230072969 + 3 ^ 40 * 494070 * 2
def baseEnd_494070 : Nat := 169130257977991455035213

theorem tailTrace_494070 : CollatzResearch.WordTrace tailWord_494070 prefixEnd_494070 169130257977991455035213 := by
  unfold tailWord_494070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126263332504765330202479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12013475546717496855493109 1126263332504765330202479)
  ·
    refine ⟨1689394998757147995303719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1126263332504765330202479 1689394998757147995303719)
    ·
      refine ⟨2534092498135721992955579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689394998757147995303719 2534092498135721992955579)
      ·
        refine ⟨3801138747203582989433369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534092498135721992955579 3801138747203582989433369)
        ·
          refine ⟨2850854060402687242075027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3801138747203582989433369 2850854060402687242075027)
          ·
            refine ⟨4276281090604030863112541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850854060402687242075027 4276281090604030863112541)
            ·
              refine ⟨1603605408976511573667203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4276281090604030863112541 1603605408976511573667203)
              ·
                refine ⟨2405408113464767360500805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603605408976511573667203 2405408113464767360500805)
                ·
                  refine ⟨451014021274643880093901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405408113464767360500805 451014021274643880093901)
                  ·
                    refine ⟨169130257977991455035213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451014021274643880093901 169130257977991455035213)
                    ·
                      rfl

theorem cell22_494070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_494070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494070 prefixEnd_494070 := by exact prefixLift 494070
  have htrace : WordTrace (prefixWord ++ tailWord_494070) baseStart_494070 baseEnd_494070 := by
    simpa [prefixWord, tailWord_494070, baseEnd_494070] using wordTrace_append hprefix tailTrace_494070
  have hstable : (prefixWord ++ tailWord_494070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494070).length < 2 ^ (prefixWord ++ tailWord_494070).sum := by decide
  have hdescent : baseEnd_494070 < baseStart_494070 := by decide
  rcases family_descends (prefixWord ++ tailWord_494070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494087 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 5]
def baseStart_494087 : Nat := 118140960795 + 494087 * 2 ^ 59
def prefixEnd_494087 : Nat := 4983230072969 + 3 ^ 40 * 494087 * 2
def baseEnd_494087 : Nat := 169136077425409077360161

theorem tailTrace_494087 : CollatzResearch.WordTrace tailWord_494087 prefixEnd_494087 169136077425409077360161 := by
  unfold tailWord_494087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18020833361014657186608515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12013888907343104791072343 18020833361014657186608515)
  ·
    refine ⟨27031250041521985779912773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18020833361014657186608515 27031250041521985779912773)
    ·
      refine ⟨5068359382785372333733645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27031250041521985779912773 5068359382785372333733645)
      ·
        refine ⟨1900634768544514625150117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5068359382785372333733645 1900634768544514625150117)
        ·
          refine ⟨356369019102096492215647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1900634768544514625150117 356369019102096492215647)
          ·
            refine ⟨534553528653144738323471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356369019102096492215647 534553528653144738323471)
            ·
              refine ⟨801830292979717107485207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534553528653144738323471 801830292979717107485207)
              ·
                refine ⟨1202745439469575661227811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801830292979717107485207 1202745439469575661227811)
                ·
                  refine ⟨1804118159204363491841717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202745439469575661227811 1804118159204363491841717)
                  ·
                    refine ⟨169136077425409077360161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1804118159204363491841717 169136077425409077360161)
                    ·
                      rfl

theorem cell22_494087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_494087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494087 prefixEnd_494087 := by exact prefixLift 494087
  have htrace : WordTrace (prefixWord ++ tailWord_494087) baseStart_494087 baseEnd_494087 := by
    simpa [prefixWord, tailWord_494087, baseEnd_494087] using wordTrace_append hprefix tailTrace_494087
  have hstable : (prefixWord ++ tailWord_494087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494087).length < 2 ^ (prefixWord ++ tailWord_494087).sum := by decide
  have hdescent : baseEnd_494087 < baseStart_494087 := by decide
  rcases family_descends (prefixWord ++ tailWord_494087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494100 : List Nat := [2, 4, 3, 1, 1, 2, 1, 8]
def baseStart_494100 : Nat := 118140960795 + 494100 * 2 ^ 59
def prefixEnd_494100 : Nat := 4983230072969 + 3 ^ 40 * 494100 * 2
def baseEnd_494100 : Nat := 18793391954564597420569

theorem tailTrace_494100 : CollatzResearch.WordTrace tailWord_494100 prefixEnd_494100 18793391954564597420569 := by
  unfold tailWord_494100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010653754983780203415877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12014205006645040271221169 9010653754983780203415877)
  ·
    refine ⟨1689497579059458788140477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9010653754983780203415877 1689497579059458788140477)
    ·
      refine ⟨633561592147297045552679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1689497579059458788140477 633561592147297045552679)
      ·
        refine ⟨950342388220945568329019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633561592147297045552679 950342388220945568329019)
        ·
          refine ⟨1425513582331418352493529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950342388220945568329019 1425513582331418352493529)
          ·
            refine ⟨1069135186748563764370147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425513582331418352493529 1069135186748563764370147)
            ·
              refine ⟨1603702780122845646555221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069135186748563764370147 1603702780122845646555221)
              ·
                refine ⟨18793391954564597420569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1603702780122845646555221 18793391954564597420569)
                ·
                  rfl

theorem cell22_494100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_494100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494100 prefixEnd_494100 := by exact prefixLift 494100
  have htrace : WordTrace (prefixWord ++ tailWord_494100) baseStart_494100 baseEnd_494100 := by
    simpa [prefixWord, tailWord_494100, baseEnd_494100] using wordTrace_append hprefix tailTrace_494100
  have hstable : (prefixWord ++ tailWord_494100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494100).length < 2 ^ (prefixWord ++ tailWord_494100).sum := by decide
  have hdescent : baseEnd_494100 < baseStart_494100 := by decide
  rcases family_descends (prefixWord ++ tailWord_494100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494145 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 5]
def baseStart_494145 : Nat := 118140960795 + 494145 * 2 ^ 59
def prefixEnd_494145 : Nat := 4983230072969 + 3 ^ 40 * 494145 * 2
def baseEnd_494145 : Nat := 56385310670238753136661

theorem tailTrace_494145 : CollatzResearch.WordTrace tailWord_494145 prefixEnd_494145 56385310670238753136661 := by
  unfold tailWord_494145
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022948794804533092219889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12015299196536355394813259 18022948794804533092219889)
  ·
    refine ⟨13517211596103399819164917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18022948794804533092219889 13517211596103399819164917)
    ·
      refine ⟨1267238587134693733046711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13517211596103399819164917 1267238587134693733046711)
      ·
        refine ⟨1900857880702040599570067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267238587134693733046711 1900857880702040599570067)
        ·
          refine ⟨2851286821053060899355101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900857880702040599570067 2851286821053060899355101)
          ·
            refine ⟨1069232557894897837258163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2851286821053060899355101 1069232557894897837258163)
            ·
              refine ⟨1603848836842346755887245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069232557894897837258163 1603848836842346755887245)
              ·
                refine ⟨601443313815880033457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603848836842346755887245 601443313815880033457717)
                ·
                  refine ⟨56385310670238753136661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601443313815880033457717 56385310670238753136661)
                  ·
                    rfl

theorem cell22_494145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_494145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494145 prefixEnd_494145 := by exact prefixLift 494145
  have htrace : WordTrace (prefixWord ++ tailWord_494145) baseStart_494145 baseEnd_494145 := by
    simpa [prefixWord, tailWord_494145, baseEnd_494145] using wordTrace_append hprefix tailTrace_494145
  have hstable : (prefixWord ++ tailWord_494145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494145).length < 2 ^ (prefixWord ++ tailWord_494145).sum := by decide
  have hdescent : baseEnd_494145 < baseStart_494145 := by decide
  rcases family_descends (prefixWord ++ tailWord_494145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494344 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_494344 : Nat := 118140960795 + 494344 * 2 ^ 59
def prefixEnd_494344 : Nat := 4983230072969 + 3 ^ 40 * 494344 * 2
def baseEnd_494344 : Nat := 169224053777546073684373

theorem tailTrace_494344 : CollatzResearch.WordTrace tailWord_494344 prefixEnd_494344 169224053777546073684373 := by
  unfold tailWord_494344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015103460541795039357043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12020137947389060052476057 9015103460541795039357043)
  ·
    refine ⟨13522655190812692559035565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015103460541795039357043 13522655190812692559035565)
    ·
      refine ⟨5070995696554759709638337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13522655190812692559035565 5070995696554759709638337)
      ·
        refine ⟨3803246772416069782228753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070995696554759709638337 3803246772416069782228753)
        ·
          refine ⟨2852435079312052336671565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803246772416069782228753 2852435079312052336671565)
          ·
            refine ⟨1069663154742019626251837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2852435079312052336671565 1069663154742019626251837)
            ·
              refine ⟨401123683028257359844439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069663154742019626251837 401123683028257359844439)
              ·
                refine ⟨601685524542386039766659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401123683028257359844439 601685524542386039766659)
                ·
                  refine ⟨902528286813579059649989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601685524542386039766659 902528286813579059649989)
                  ·
                    refine ⟨169224053777546073684373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902528286813579059649989 169224053777546073684373)
                    ·
                      rfl

theorem cell22_494344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_494344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494344 prefixEnd_494344 := by exact prefixLift 494344
  have htrace : WordTrace (prefixWord ++ tailWord_494344) baseStart_494344 baseEnd_494344 := by
    simpa [prefixWord, tailWord_494344, baseEnd_494344] using wordTrace_append hprefix tailTrace_494344
  have hstable : (prefixWord ++ tailWord_494344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494344).length < 2 ^ (prefixWord ++ tailWord_494344).sum := by decide
  have hdescent : baseEnd_494344 < baseStart_494344 := by decide
  rcases family_descends (prefixWord ++ tailWord_494344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494355 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_494355 : Nat := 118140960795 + 494355 * 2 ^ 59
def prefixEnd_494355 : Nat := 4983230072969 + 3 ^ 40 * 494355 * 2
def baseEnd_494355 : Nat := 169227819302345711659339

theorem tailTrace_494355 : CollatzResearch.WordTrace tailWord_494355 prefixEnd_494355 169227819302345711659339 := by
  unfold tailWord_494355
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030608124043738957364519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12020405416029159304909679 18030608124043738957364519)
  ·
    refine ⟨27045912186065608436046779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18030608124043738957364519 27045912186065608436046779)
    ·
      refine ⟨40568868279098412654070169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27045912186065608436046779 40568868279098412654070169)
      ·
        refine ⟨30426651209323809490552627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40568868279098412654070169 30426651209323809490552627)
        ·
          refine ⟨45639976813985714235828941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30426651209323809490552627 45639976813985714235828941)
          ·
            refine ⟨17114991305244642838435853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45639976813985714235828941 17114991305244642838435853)
            ·
              refine ⟨6418121739466741064413445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17114991305244642838435853 6418121739466741064413445)
              ·
                refine ⟨1203397826150013949577521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6418121739466741064413445 1203397826150013949577521)
                ·
                  refine ⟨902548369612510462183141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203397826150013949577521 902548369612510462183141)
                  ·
                    refine ⟨169227819302345711659339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902548369612510462183141 169227819302345711659339)
                    ·
                      rfl

theorem cell22_494355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_494355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494355 prefixEnd_494355 := by exact prefixLift 494355
  have htrace : WordTrace (prefixWord ++ tailWord_494355) baseStart_494355 baseEnd_494355 := by
    simpa [prefixWord, tailWord_494355, baseEnd_494355] using wordTrace_append hprefix tailTrace_494355
  have hstable : (prefixWord ++ tailWord_494355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494355).length < 2 ^ (prefixWord ++ tailWord_494355).sum := by decide
  have hdescent : baseEnd_494355 < baseStart_494355 := by decide
  rcases family_descends (prefixWord ++ tailWord_494355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494359 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 4]
def baseStart_494359 : Nat := 118140960795 + 494359 * 2 ^ 59
def prefixEnd_494359 : Nat := 4983230072969 + 3 ^ 40 * 494359 * 2
def baseEnd_494359 : Nat := 56409729528030344853109

theorem tailTrace_494359 : CollatzResearch.WordTrace tailWord_494359 prefixEnd_494359 56409729528030344853109 := by
  unfold tailWord_494359
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030754016029247640510131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12020502677352831760340087 18030754016029247640510131)
  ·
    refine ⟨27046131024043871460765197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18030754016029247640510131 27046131024043871460765197)
    ·
      refine ⟨10142299134016451797786949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27046131024043871460765197 10142299134016451797786949)
      ·
        refine ⟨1901681087628084712085053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10142299134016451797786949 1901681087628084712085053)
        ·
          refine ⟨713130407860531767031895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901681087628084712085053 713130407860531767031895)
          ·
            refine ⟨1069695611790797650547843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713130407860531767031895 1069695611790797650547843)
            ·
              refine ⟨1604543417686196475821765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069695611790797650547843 1604543417686196475821765)
              ·
                refine ⟨300851890816161839216581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1604543417686196475821765 300851890816161839216581)
                ·
                  refine ⟨56409729528030344853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300851890816161839216581 56409729528030344853109)
                  ·
                    rfl

theorem cell22_494359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 4].length) (baseStart_494359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494359 prefixEnd_494359 := by exact prefixLift 494359
  have htrace : WordTrace (prefixWord ++ tailWord_494359) baseStart_494359 baseEnd_494359 := by
    simpa [prefixWord, tailWord_494359, baseEnd_494359] using wordTrace_append hprefix tailTrace_494359
  have hstable : (prefixWord ++ tailWord_494359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494359).length < 2 ^ (prefixWord ++ tailWord_494359).sum := by decide
  have hdescent : baseEnd_494359 < baseStart_494359 := by decide
  rcases family_descends (prefixWord ++ tailWord_494359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494387 : List Nat := [1, 1, 1, 2, 6, 2, 3, 6]
def baseStart_494387 : Nat := 118140960795 + 494387 * 2 ^ 59
def prefixEnd_494387 : Nat := 4983230072969 + 3 ^ 40 * 494387 * 2
def baseEnd_494387 : Nat := 18804308172923143873249

theorem tailTrace_494387 : CollatzResearch.WordTrace tailWord_494387 prefixEnd_494387 18804308172923143873249 := by
  unfold tailWord_494387
  simp only [CollatzResearch.WordTrace]
  refine ⟨18031775259927808422529415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12021183506618538948352943 18031775259927808422529415)
  ·
    refine ⟨27047662889891712633794123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18031775259927808422529415 27047662889891712633794123)
    ·
      refine ⟨40571494334837568950691185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27047662889891712633794123 40571494334837568950691185)
      ·
        refine ⟨30428620751128176713018389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40571494334837568950691185 30428620751128176713018389)
        ·
          refine ⟨1426341597709133283422737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30428620751128176713018389 1426341597709133283422737)
          ·
            refine ⟨1069756198281849962567053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426341597709133283422737 1069756198281849962567053)
            ·
              refine ⟨401158574355693735962645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1069756198281849962567053 401158574355693735962645)
              ·
                refine ⟨18804308172923143873249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401158574355693735962645 18804308172923143873249)
                ·
                  rfl

theorem cell22_494387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 6].length) (baseStart_494387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494387 prefixEnd_494387 := by exact prefixLift 494387
  have htrace : WordTrace (prefixWord ++ tailWord_494387) baseStart_494387 baseEnd_494387 := by
    simpa [prefixWord, tailWord_494387, baseEnd_494387] using wordTrace_append hprefix tailTrace_494387
  have hstable : (prefixWord ++ tailWord_494387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494387).length < 2 ^ (prefixWord ++ tailWord_494387).sum := by decide
  have hdescent : baseEnd_494387 < baseStart_494387 := by decide
  rcases family_descends (prefixWord ++ tailWord_494387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494389 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_494389 : Nat := 118140960795 + 494389 * 2 ^ 59
def prefixEnd_494389 : Nat := 4983230072969 + 3 ^ 40 * 494389 * 2
def baseEnd_494389 : Nat := 169239458197180956309235

theorem tailTrace_494389 : CollatzResearch.WordTrace tailWord_494389 prefixEnd_494389 169239458197180956309235 := by
  unfold tailWord_494389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18031848205920562764102221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12021232137280375176068147 18031848205920562764102221)
  ·
    refine ⟨6761943077220211036538333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18031848205920562764102221 6761943077220211036538333)
    ·
      refine ⟨2535728653957579138701875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6761943077220211036538333 2535728653957579138701875)
      ·
        refine ⟨3803592980936368708052813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535728653957579138701875 3803592980936368708052813)
        ·
          refine ⟨1426347367851138265519805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3803592980936368708052813 1426347367851138265519805)
          ·
            refine ⟨534880262944176849569927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1426347367851138265519805 534880262944176849569927)
            ·
              refine ⟨802320394416265274354891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534880262944176849569927 802320394416265274354891)
              ·
                refine ⟨1203480591624397911532337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802320394416265274354891 1203480591624397911532337)
                ·
                  refine ⟨902610443718298433649253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203480591624397911532337 902610443718298433649253)
                  ·
                    refine ⟨169239458197180956309235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902610443718298433649253 169239458197180956309235)
                    ·
                      rfl

theorem cell22_494389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_494389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494389 prefixEnd_494389 := by exact prefixLift 494389
  have htrace : WordTrace (prefixWord ++ tailWord_494389) baseStart_494389 baseEnd_494389 := by
    simpa [prefixWord, tailWord_494389, baseEnd_494389] using wordTrace_append hprefix tailTrace_494389
  have hstable : (prefixWord ++ tailWord_494389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494389).length < 2 ^ (prefixWord ++ tailWord_494389).sum := by decide
  have hdescent : baseEnd_494389 < baseStart_494389 := by decide
  rcases family_descends (prefixWord ++ tailWord_494389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494404 : List Nat := [2, 3, 4, 2, 1, 1, 9]
def baseStart_494404 : Nat := 118140960795 + 494404 * 2 ^ 59
def prefixEnd_494404 : Nat := 4983230072969 + 3 ^ 40 * 494404 * 2
def baseEnd_494404 : Nat := 6268318259397256192007

theorem tailTrace_494404 : CollatzResearch.WordTrace tailWord_494404 prefixEnd_494404 6268318259397256192007 := by
  unfold tailWord_494404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016197650433110162949133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12021596867244146883932177 9016197650433110162949133)
  ·
    refine ⟨3381074118912416311105925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9016197650433110162949133 3381074118912416311105925)
    ·
      refine ⟨633951397296078058332361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3381074118912416311105925 633951397296078058332361)
      ·
        refine ⟨475463547972058543749271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633951397296078058332361 475463547972058543749271)
        ·
          refine ⟨713195321958087815623907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475463547972058543749271 713195321958087815623907)
          ·
            refine ⟨1069792982937131723435861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713195321958087815623907 1069792982937131723435861)
            ·
              refine ⟨6268318259397256192007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1069792982937131723435861 6268318259397256192007)
              ·
                rfl

theorem cell22_494404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 9].length) (baseStart_494404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494404 prefixEnd_494404 := by exact prefixLift 494404
  have htrace : WordTrace (prefixWord ++ tailWord_494404) baseStart_494404 baseEnd_494404 := by
    simpa [prefixWord, tailWord_494404, baseEnd_494404] using wordTrace_append hprefix tailTrace_494404
  have hstable : (prefixWord ++ tailWord_494404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494404).length < 2 ^ (prefixWord ++ tailWord_494404).sum := by decide
  have hdescent : baseEnd_494404 < baseStart_494404 := by decide
  rcases family_descends (prefixWord ++ tailWord_494404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494453 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_494453 : Nat := 118140960795 + 494453 * 2 ^ 59
def prefixEnd_494453 : Nat := 4983230072969 + 3 ^ 40 * 494453 * 2
def baseEnd_494453 : Nat := 169261366705106122709039

theorem tailTrace_494453 : CollatzResearch.WordTrace tailWord_494453 prefixEnd_494453 169261366705106122709039 := by
  unfold tailWord_494453
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034182477688701694432013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12022788318459134462954675 18034182477688701694432013)
  ·
    refine ⟨6762818429133263135412005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18034182477688701694432013 6762818429133263135412005)
    ·
      refine ⟨1268028455462486837889751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6762818429133263135412005 1268028455462486837889751)
      ·
        refine ⟨1902042683193730256834627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268028455462486837889751 1902042683193730256834627)
        ·
          refine ⟨2853064024790595385251941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902042683193730256834627 2853064024790595385251941)
          ·
            refine ⟨534949504648236634734739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2853064024790595385251941 534949504648236634734739)
            ·
              refine ⟨802424256972354952102109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534949504648236634734739 802424256972354952102109)
              ·
                refine ⟨300909096364633107038291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802424256972354952102109 300909096364633107038291)
                ·
                  refine ⟨451363644546949660557437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300909096364633107038291 451363644546949660557437)
                  ·
                    refine ⟨169261366705106122709039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451363644546949660557437 169261366705106122709039)
                    ·
                      rfl

theorem cell22_494453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_494453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494453 prefixEnd_494453 := by exact prefixLift 494453
  have htrace : WordTrace (prefixWord ++ tailWord_494453) baseStart_494453 baseEnd_494453 := by
    simpa [prefixWord, tailWord_494453, baseEnd_494453] using wordTrace_append hprefix tailTrace_494453
  have hstable : (prefixWord ++ tailWord_494453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494453).length < 2 ^ (prefixWord ++ tailWord_494453).sum := by decide
  have hdescent : baseEnd_494453 < baseStart_494453 := by decide
  rcases family_descends (prefixWord ++ tailWord_494453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494460 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_494460 : Nat := 118140960795 + 494460 * 2 ^ 59
def prefixEnd_494460 : Nat := 4983230072969 + 3 ^ 40 * 494460 * 2
def baseEnd_494460 : Nat := 56421254316053479261339

theorem tailTrace_494460 : CollatzResearch.WordTrace tailWord_494460 prefixEnd_494460 56421254316053479261339 := by
  unfold tailWord_494460
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017218894331670944968417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12022958525775561259957889 9017218894331670944968417)
  ·
    refine ⟨6762914170748753208726313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9017218894331670944968417 6762914170748753208726313)
    ·
      refine ⟨5072185628061564906544735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6762914170748753208726313 5072185628061564906544735)
      ·
        refine ⟨7608278442092347359817103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072185628061564906544735 7608278442092347359817103)
        ·
          refine ⟨11412417663138521039725655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608278442092347359817103 11412417663138521039725655)
          ·
            refine ⟨17118626494707781559588483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412417663138521039725655 17118626494707781559588483)
            ·
              refine ⟨25677939742061672339382725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17118626494707781559588483 25677939742061672339382725)
              ·
                refine ⟨4814613701636563563634261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25677939742061672339382725 4814613701636563563634261)
                ·
                  refine ⟨56421254316053479261339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4814613701636563563634261 56421254316053479261339)
                  ·
                    rfl

theorem cell22_494460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_494460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494460 prefixEnd_494460 := by exact prefixLift 494460
  have htrace : WordTrace (prefixWord ++ tailWord_494460) baseStart_494460 baseEnd_494460 := by
    simpa [prefixWord, tailWord_494460, baseEnd_494460] using wordTrace_append hprefix tailTrace_494460
  have hstable : (prefixWord ++ tailWord_494460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494460).length < 2 ^ (prefixWord ++ tailWord_494460).sum := by decide
  have hdescent : baseEnd_494460 < baseStart_494460 := by decide
  rcases family_descends (prefixWord ++ tailWord_494460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494505 : List Nat := [1, 2, 1, 1, 1, 1, 5, 10]
def baseStart_494505 : Nat := 118140960795 + 494505 * 2 ^ 59
def prefixEnd_494505 : Nat := 4983230072969 + 3 ^ 40 * 494505 * 2
def baseEnd_494505 : Nat := 18808796374199480045431

theorem tailTrace_494505 : CollatzResearch.WordTrace tailWord_494505 prefixEnd_494505 18808796374199480045431 := by
  unfold tailWord_494505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18036079073500314575324969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12024052715666876383549979 18036079073500314575324969)
  ·
    refine ⟨13527059305125235931493727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18036079073500314575324969 13527059305125235931493727)
    ·
      refine ⟨20290588957687853897240591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13527059305125235931493727 20290588957687853897240591)
      ·
        refine ⟨30435883436531780845860887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290588957687853897240591 30435883436531780845860887)
        ·
          refine ⟨45653825154797671268791331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30435883436531780845860887 45653825154797671268791331)
          ·
            refine ⟨68480737732196506903186997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45653825154797671268791331 68480737732196506903186997)
            ·
              refine ⟨6420069162393422522173781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68480737732196506903186997 6420069162393422522173781)
              ·
                refine ⟨18808796374199480045431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6420069162393422522173781 18808796374199480045431)
                ·
                  rfl

theorem cell22_494505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 10].length) (baseStart_494505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494505 prefixEnd_494505 := by exact prefixLift 494505
  have htrace : WordTrace (prefixWord ++ tailWord_494505) baseStart_494505 baseEnd_494505 := by
    simpa [prefixWord, tailWord_494505, baseEnd_494505] using wordTrace_append hprefix tailTrace_494505
  have hstable : (prefixWord ++ tailWord_494505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494505).length < 2 ^ (prefixWord ++ tailWord_494505).sum := by decide
  have hdescent : baseEnd_494505 < baseStart_494505 := by decide
  rcases family_descends (prefixWord ++ tailWord_494505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494526 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_494526 : Nat := 118140960795 + 494526 * 2 ^ 59
def prefixEnd_494526 : Nat := 4983230072969 + 3 ^ 40 * 494526 * 2
def baseEnd_494526 : Nat := 169286356096958265633815

theorem tailTrace_494526 : CollatzResearch.WordTrace tailWord_494526 prefixEnd_494526 169286356096958265633815 := by
  unfold tailWord_494526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254605625803029395229929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12024563337616156774559621 2254605625803029395229929)
  ·
    refine ⟨1690954219352272046422447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2254605625803029395229929 1690954219352272046422447)
    ·
      refine ⟨2536431329028408069633671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690954219352272046422447 2536431329028408069633671)
      ·
        refine ⟨3804646993542612104450507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536431329028408069633671 3804646993542612104450507)
        ·
          refine ⟨5706970490313918156675761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804646993542612104450507 5706970490313918156675761)
          ·
            refine ⟨4280227867735438617506821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5706970490313918156675761 4280227867735438617506821)
            ·
              refine ⟨802542725200394740782529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4280227867735438617506821 802542725200394740782529)
              ·
                refine ⟨601907043900296055586897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802542725200394740782529 601907043900296055586897)
                ·
                  refine ⟨451430282925222041690173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601907043900296055586897 451430282925222041690173)
                  ·
                    refine ⟨169286356096958265633815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451430282925222041690173 169286356096958265633815)
                    ·
                      rfl

theorem cell22_494526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_494526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494526 prefixEnd_494526 := by exact prefixLift 494526
  have htrace : WordTrace (prefixWord ++ tailWord_494526) baseStart_494526 baseEnd_494526 := by
    simpa [prefixWord, tailWord_494526, baseEnd_494526] using wordTrace_append hprefix tailTrace_494526
  have hstable : (prefixWord ++ tailWord_494526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494526).length < 2 ^ (prefixWord ++ tailWord_494526).sum := by decide
  have hdescent : baseEnd_494526 < baseStart_494526 := by decide
  rcases family_descends (prefixWord ++ tailWord_494526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494554 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_494554 : Nat := 118140960795 + 494554 * 2 ^ 59
def prefixEnd_494554 : Nat := 4983230072969 + 3 ^ 40 * 494554 * 2
def baseEnd_494554 : Nat := 169295941069175525933729

theorem tailTrace_494554 : CollatzResearch.WordTrace tailWord_494554 prefixEnd_494554 169295941069175525933729 := by
  unfold tailWord_494554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509466562580698985964679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12025244166881863962572477 4509466562580698985964679)
  ·
    refine ⟨6764199843871048478947019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4509466562580698985964679 6764199843871048478947019)
    ·
      refine ⟨10146299765806572718420529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764199843871048478947019 10146299765806572718420529)
      ·
        refine ⟨7609724824354929538815397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10146299765806572718420529 7609724824354929538815397)
        ·
          refine ⟨1426823404566549288527887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7609724824354929538815397 1426823404566549288527887)
          ·
            refine ⟨2140235106849823932791831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426823404566549288527887 2140235106849823932791831)
            ·
              refine ⟨3210352660274735899187747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140235106849823932791831 3210352660274735899187747)
              ·
                refine ⟨4815528990412103848781621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210352660274735899187747 4815528990412103848781621)
                ·
                  refine ⟨451455842851134735823277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815528990412103848781621 451455842851134735823277)
                  ·
                    refine ⟨169295941069175525933729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451455842851134735823277 169295941069175525933729)
                    ·
                      rfl

theorem cell22_494554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_494554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494554 prefixEnd_494554 := by exact prefixLift 494554
  have htrace : WordTrace (prefixWord ++ tailWord_494554) baseStart_494554 baseEnd_494554 := by
    simpa [prefixWord, tailWord_494554, baseEnd_494554] using wordTrace_append hprefix tailTrace_494554
  have hstable : (prefixWord ++ tailWord_494554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494554).length < 2 ^ (prefixWord ++ tailWord_494554).sum := by decide
  have hdescent : baseEnd_494554 < baseStart_494554 := by decide
  rcases family_descends (prefixWord ++ tailWord_494554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494646 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_494646 : Nat := 118140960795 + 494646 * 2 ^ 59
def prefixEnd_494646 : Nat := 4983230072969 + 3 ^ 40 * 494646 * 2
def baseEnd_494646 : Nat := 56442478183105984211149

theorem tailTrace_494646 : CollatzResearch.WordTrace tailWord_494646 prefixEnd_494646 56442478183105984211149 := by
  unfold tailWord_494646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127576360374343478512987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12027481177326330437471861 1127576360374343478512987)
  ·
    refine ⟨1691364540561515217769481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127576360374343478512987 1691364540561515217769481)
    ·
      refine ⟨1268523405421136413327111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691364540561515217769481 1268523405421136413327111)
      ·
        refine ⟨1902785108131704619990667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268523405421136413327111 1902785108131704619990667)
        ·
          refine ⟨2854177662197556929986001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902785108131704619990667 2854177662197556929986001)
          ·
            refine ⟨2140633246648167697489501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854177662197556929986001 2140633246648167697489501)
            ·
              refine ⟨802737467493062886558563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140633246648167697489501 802737467493062886558563)
              ·
                refine ⟨1204106201239594329837845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802737467493062886558563 1204106201239594329837845)
                ·
                  refine ⟨56442478183105984211149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1204106201239594329837845 56442478183105984211149)
                  ·
                    rfl

theorem cell22_494646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_494646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494646 prefixEnd_494646 := by exact prefixLift 494646
  have htrace : WordTrace (prefixWord ++ tailWord_494646) baseStart_494646 baseEnd_494646 := by
    simpa [prefixWord, tailWord_494646, baseEnd_494646] using wordTrace_append hprefix tailTrace_494646
  have hstable : (prefixWord ++ tailWord_494646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494646).length < 2 ^ (prefixWord ++ tailWord_494646).sum := by decide
  have hdescent : baseEnd_494646 < baseStart_494646 := by decide
  rcases family_descends (prefixWord ++ tailWord_494646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494672 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_494672 : Nat := 118140960795 + 494672 * 2 ^ 59
def prefixEnd_494672 : Nat := 4983230072969 + 3 ^ 40 * 494672 * 2
def baseEnd_494672 : Nat := 169336334880662551483367

theorem tailTrace_494672 : CollatzResearch.WordTrace tailWord_494672 prefixEnd_494672 169336334880662551483367 := by
  unfold tailWord_494672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021085031947651048327135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12028113375930201397769513 9021085031947651048327135)
  ·
    refine ⟨13531627547921476572490703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9021085031947651048327135 13531627547921476572490703)
    ·
      refine ⟨20297441321882214858736055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13531627547921476572490703 20297441321882214858736055)
      ·
        refine ⟨30446161982823322288104083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20297441321882214858736055 30446161982823322288104083)
        ·
          refine ⟨45669242974234983432156125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30446161982823322288104083 45669242974234983432156125)
          ·
            refine ⟨17125966115338118787058547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45669242974234983432156125 17125966115338118787058547)
            ·
              refine ⟨25688949173007178180587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17125966115338118787058547 25688949173007178180587821)
              ·
                refine ⟨9633355939877691817720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25688949173007178180587821 9633355939877691817720433)
                ·
                  refine ⟨7225016954908268863290325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633355939877691817720433 7225016954908268863290325)
                  ·
                    refine ⟨169336334880662551483367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7225016954908268863290325 169336334880662551483367)
                    ·
                      rfl

theorem cell22_494672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_494672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494672 prefixEnd_494672 := by exact prefixLift 494672
  have htrace : WordTrace (prefixWord ++ tailWord_494672) baseStart_494672 baseEnd_494672 := by
    simpa [prefixWord, tailWord_494672, baseEnd_494672] using wordTrace_append hprefix tailTrace_494672
  have hstable : (prefixWord ++ tailWord_494672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494672).length < 2 ^ (prefixWord ++ tailWord_494672).sum := by decide
  have hdescent : baseEnd_494672 < baseStart_494672 := by decide
  rcases family_descends (prefixWord ++ tailWord_494672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494674 : List Nat := [3, 2, 2, 1, 3, 1, 2, 8]
def baseStart_494674 : Nat := 118140960795 + 494674 * 2 ^ 59
def prefixEnd_494674 : Nat := 4983230072969 + 3 ^ 40 * 494674 * 2
def baseEnd_494674 : Nat := 18815224391281690325929

theorem tailTrace_494674 : CollatzResearch.WordTrace tailWord_494674 prefixEnd_494674 18815224391281690325929 := by
  unfold tailWord_494674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510560752472014109556769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12028162006592037625484717 4510560752472014109556769)
  ·
    refine ⟨3382920564354010582167577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4510560752472014109556769 3382920564354010582167577)
    ·
      refine ⟨2537190423265507936625683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3382920564354010582167577 2537190423265507936625683)
      ·
        refine ⟨3805785634898261904938525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537190423265507936625683 3805785634898261904938525)
        ·
          refine ⟨1427169613086848214351947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805785634898261904938525 1427169613086848214351947)
          ·
            refine ⟨2140754419630272321527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427169613086848214351947 2140754419630272321527921)
            ·
              refine ⟨1605565814722704241145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140754419630272321527921 1605565814722704241145941)
              ·
                refine ⟨18815224391281690325929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1605565814722704241145941 18815224391281690325929)
                ·
                  rfl

theorem cell22_494674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_494674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494674 prefixEnd_494674 := by exact prefixLift 494674
  have htrace : WordTrace (prefixWord ++ tailWord_494674) baseStart_494674 baseEnd_494674 := by
    simpa [prefixWord, tailWord_494674, baseEnd_494674] using wordTrace_append hprefix tailTrace_494674
  have hstable : (prefixWord ++ tailWord_494674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494674).length < 2 ^ (prefixWord ++ tailWord_494674).sum := by decide
  have hdescent : baseEnd_494674 < baseStart_494674 := by decide
  rcases family_descends (prefixWord ++ tailWord_494674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494706 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_494706 : Nat := 118140960795 + 494706 * 2 ^ 59
def prefixEnd_494706 : Nat := 4983230072969 + 3 ^ 40 * 494706 * 2
def baseEnd_494706 : Nat := 169347973775497796133263

theorem tailTrace_494706 : CollatzResearch.WordTrace tailWord_494706 prefixEnd_494706 169347973775497796133263 := by
  unfold tailWord_494706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510852536443031475847993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12028940097181417268927981 4510852536443031475847993)
  ·
    refine ⟨3383139402332273606885995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4510852536443031475847993 3383139402332273606885995)
    ·
      refine ⟨5074709103498410410328993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383139402332273606885995 5074709103498410410328993)
      ·
        refine ⟨3806031827623807807746745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5074709103498410410328993 3806031827623807807746745)
        ·
          refine ⟨2854523870717855855810059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806031827623807807746745 2854523870717855855810059)
          ·
            refine ⟨4281785806076783783715089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854523870717855855810059 4281785806076783783715089)
            ·
              refine ⟨3211339354557587837786317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281785806076783783715089 3211339354557587837786317)
              ·
                refine ⟨1204252257959095439169869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3211339354557587837786317 1204252257959095439169869)
                ·
                  refine ⟨451594596734660789688701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204252257959095439169869 451594596734660789688701)
                  ·
                    refine ⟨169347973775497796133263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451594596734660789688701 169347973775497796133263)
                    ·
                      rfl

theorem cell22_494706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_494706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494706 prefixEnd_494706 := by exact prefixLift 494706
  have htrace : WordTrace (prefixWord ++ tailWord_494706) baseStart_494706 baseEnd_494706 := by
    simpa [prefixWord, tailWord_494706, baseEnd_494706] using wordTrace_append hprefix tailTrace_494706
  have hstable : (prefixWord ++ tailWord_494706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494706).length < 2 ^ (prefixWord ++ tailWord_494706).sum := by decide
  have hdescent : baseEnd_494706 < baseStart_494706 := by decide
  rcases family_descends (prefixWord ++ tailWord_494706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494779 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_494779 : Nat := 118140960795 + 494779 * 2 ^ 59
def prefixEnd_494779 : Nat := 4983230072969 + 3 ^ 40 * 494779 * 2
def baseEnd_494779 : Nat := 169372963167349939058039

theorem tailTrace_494779 : CollatzResearch.WordTrace tailWord_494779 prefixEnd_494779 169372963167349939058039 := by
  unfold tailWord_494779
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046072674507659370799391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030715116338439580532927 18046072674507659370799391)
  ·
    refine ⟨27069109011761489056199087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18046072674507659370799391 27069109011761489056199087)
    ·
      refine ⟨40603663517642233584298631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27069109011761489056199087 40603663517642233584298631)
      ·
        refine ⟨60905495276463350376447947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603663517642233584298631 60905495276463350376447947)
        ·
          refine ⟨91358242914695025564671921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60905495276463350376447947 91358242914695025564671921)
          ·
            refine ⟨68518682186021269173503941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91358242914695025564671921 68518682186021269173503941)
            ·
              refine ⟨12847252909878987970031989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68518682186021269173503941 12847252909878987970031989)
              ·
                refine ⟨1204429960301155122190499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12847252909878987970031989 1204429960301155122190499)
                ·
                  refine ⟨1806644940451732683285749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204429960301155122190499 1806644940451732683285749)
                  ·
                    refine ⟨169372963167349939058039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1806644940451732683285749 169372963167349939058039)
                    ·
                      rfl

theorem cell22_494779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_494779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494779 prefixEnd_494779 := by exact prefixLift 494779
  have htrace : WordTrace (prefixWord ++ tailWord_494779) baseStart_494779 baseEnd_494779 := by
    simpa [prefixWord, tailWord_494779, baseEnd_494779] using wordTrace_append hprefix tailTrace_494779
  have hstable : (prefixWord ++ tailWord_494779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494779).length < 2 ^ (prefixWord ++ tailWord_494779).sum := by decide
  have hdescent : baseEnd_494779 < baseStart_494779 := by decide
  rcases family_descends (prefixWord ++ tailWord_494779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494826 : List Nat := [3, 1, 3, 1, 1, 4, 2, 7]
def baseStart_494826 : Nat := 118140960795 + 494826 * 2 ^ 59
def prefixEnd_494826 : Nat := 4983230072969 + 3 ^ 40 * 494826 * 2
def baseEnd_494826 : Nat := 18821005803095275903655

theorem tailTrace_494826 : CollatzResearch.WordTrace tailWord_494826 prefixEnd_494826 18821005803095275903655 := by
  unfold tailWord_494826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511946726334346599440083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12031857936891590931840221 4511946726334346599440083)
  ·
    refine ⟨6767920089501519899160125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4511946726334346599440083 6767920089501519899160125)
    ·
      refine ⟨2537970033563069962185047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6767920089501519899160125 2537970033563069962185047)
      ·
        refine ⟨3806955050344604943277571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537970033563069962185047 3806955050344604943277571)
        ·
          refine ⟨5710432575516907414916357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806955050344604943277571 5710432575516907414916357)
          ·
            refine ⟨1070706107909420140296817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5710432575516907414916357 1070706107909420140296817)
            ·
              refine ⟨803029580932065105222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070706107909420140296817 803029580932065105222613)
              ·
                refine ⟨18821005803095275903655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 803029580932065105222613 18821005803095275903655)
                ·
                  rfl

theorem cell22_494826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_494826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494826 prefixEnd_494826 := by exact prefixLift 494826
  have htrace : WordTrace (prefixWord ++ tailWord_494826) baseStart_494826 baseEnd_494826 := by
    simpa [prefixWord, tailWord_494826, baseEnd_494826] using wordTrace_append hprefix tailTrace_494826
  have hstable : (prefixWord ++ tailWord_494826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494826).length < 2 ^ (prefixWord ++ tailWord_494826).sum := by decide
  have hdescent : baseEnd_494826 < baseStart_494826 := by decide
  rcases family_descends (prefixWord ++ tailWord_494826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494830 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_494830 : Nat := 118140960795 + 494830 * 2 ^ 59
def prefixEnd_494830 : Nat := 4983230072969 + 3 ^ 40 * 494830 * 2
def baseEnd_494830 : Nat := 169390421509602806032883

theorem tailTrace_494830 : CollatzResearch.WordTrace tailWord_494830 prefixEnd_494830 169390421509602806032883 := by
  unfold tailWord_494830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255991599665361885113243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12031955198215263387270629 2255991599665361885113243)
  ·
    refine ⟨3383987399498042827669865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2255991599665361885113243 3383987399498042827669865)
    ·
      refine ⟨2537990549623532120752399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3383987399498042827669865 2537990549623532120752399)
      ·
        refine ⟨3806985824435298181128599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537990549623532120752399 3806985824435298181128599)
        ·
          refine ⟨5710478736652947271692899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806985824435298181128599 5710478736652947271692899)
          ·
            refine ⟨8565718104979420907539349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710478736652947271692899 8565718104979420907539349)
            ·
              refine ⟨401518036170910355040907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8565718104979420907539349 401518036170910355040907)
              ·
                refine ⟨602277054256365532561361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401518036170910355040907 602277054256365532561361)
                ·
                  refine ⟨451707790692274149421021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602277054256365532561361 451707790692274149421021)
                  ·
                    refine ⟨169390421509602806032883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451707790692274149421021 169390421509602806032883)
                    ·
                      rfl

theorem cell22_494830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_494830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494830 prefixEnd_494830 := by exact prefixLift 494830
  have htrace : WordTrace (prefixWord ++ tailWord_494830) baseStart_494830 baseEnd_494830 := by
    simpa [prefixWord, tailWord_494830, baseEnd_494830] using wordTrace_append hprefix tailTrace_494830
  have hstable : (prefixWord ++ tailWord_494830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494830).length < 2 ^ (prefixWord ++ tailWord_494830).sum := by decide
  have hdescent : baseEnd_494830 < baseStart_494830 := by decide
  rcases family_descends (prefixWord ++ tailWord_494830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494839 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_494839 : Nat := 118140960795 + 494839 * 2 ^ 59
def prefixEnd_494839 : Nat := 4983230072969 + 3 ^ 40 * 494839 * 2
def baseEnd_494839 : Nat := 169393502393529782557855

theorem tailTrace_494839 : CollatzResearch.WordTrace tailWord_494839 prefixEnd_494839 169393502393529782557855 := by
  unfold tailWord_494839
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048261054290289617983571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12032174036193526411989047 18048261054290289617983571)
  ·
    refine ⟨27072391581435434426975357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048261054290289617983571 27072391581435434426975357)
    ·
      refine ⟨10152146843038287910115759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27072391581435434426975357 10152146843038287910115759)
      ·
        refine ⟨15228220264557431865173639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152146843038287910115759 15228220264557431865173639)
        ·
          refine ⟨22842330396836147797760459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228220264557431865173639 22842330396836147797760459)
          ·
            refine ⟨34263495595254221696640689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22842330396836147797760459 34263495595254221696640689)
            ·
              refine ⟨25697621696440666272480517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34263495595254221696640689 25697621696440666272480517)
              ·
                refine ⟨4818304068082624926090097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25697621696440666272480517 4818304068082624926090097)
                ·
                  refine ⟨3613728051061968694567573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818304068082624926090097 3613728051061968694567573)
                  ·
                    refine ⟨169393502393529782557855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3613728051061968694567573 169393502393529782557855)
                    ·
                      rfl

theorem cell22_494839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_494839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494839 prefixEnd_494839 := by exact prefixLift 494839
  have htrace : WordTrace (prefixWord ++ tailWord_494839) baseStart_494839 baseEnd_494839 := by
    simpa [prefixWord, tailWord_494839, baseEnd_494839] using wordTrace_append hprefix tailTrace_494839
  have hstable : (prefixWord ++ tailWord_494839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494839).length < 2 ^ (prefixWord ++ tailWord_494839).sum := by decide
  have hdescent : baseEnd_494839 < baseStart_494839 := by decide
  rcases family_descends (prefixWord ++ tailWord_494839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494841 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_494841 : Nat := 118140960795 + 494841 * 2 ^ 59
def prefixEnd_494841 : Nat := 4983230072969 + 3 ^ 40 * 494841 * 2
def baseEnd_494841 : Nat := 169394187034402444007849

theorem tailTrace_494841 : CollatzResearch.WordTrace tailWord_494841 prefixEnd_494841 169394187034402444007849 := by
  unfold tailWord_494841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048334000283043959556377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12032222666855362639704251 18048334000283043959556377)
  ·
    refine ⟨13536250500212282969667283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18048334000283043959556377 13536250500212282969667283)
    ·
      refine ⟨20304375750318424454500925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13536250500212282969667283 20304375750318424454500925)
      ·
        refine ⟨7614140906369409170437847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20304375750318424454500925 7614140906369409170437847)
        ·
          refine ⟨11421211359554113755656771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614140906369409170437847 11421211359554113755656771)
          ·
            refine ⟨17131817039331170633485157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421211359554113755656771 17131817039331170633485157)
            ·
              refine ⟨3212215694874594493778467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17131817039331170633485157 3212215694874594493778467)
              ·
                refine ⟨4818323542311891740667701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212215694874594493778467 4818323542311891740667701)
                ·
                  refine ⟨451717832091739850687597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4818323542311891740667701 451717832091739850687597)
                  ·
                    refine ⟨169394187034402444007849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451717832091739850687597 169394187034402444007849)
                    ·
                      rfl

theorem cell22_494841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_494841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494841 prefixEnd_494841 := by exact prefixLift 494841
  have htrace : WordTrace (prefixWord ++ tailWord_494841) baseStart_494841 baseEnd_494841 := by
    simpa [prefixWord, tailWord_494841, baseEnd_494841] using wordTrace_append hprefix tailTrace_494841
  have hstable : (prefixWord ++ tailWord_494841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494841).length < 2 ^ (prefixWord ++ tailWord_494841).sum := by decide
  have hdescent : baseEnd_494841 < baseStart_494841 := by decide
  rcases family_descends (prefixWord ++ tailWord_494841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494866 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_494866 : Nat := 118140960795 + 494866 * 2 ^ 59
def prefixEnd_494866 : Nat := 4983230072969 + 3 ^ 40 * 494866 * 2
def baseEnd_494866 : Nat := 56467581681770237377591

theorem tailTrace_494866 : CollatzResearch.WordTrace tailWord_494866 prefixEnd_494866 56467581681770237377591 := by
  unfold tailWord_494866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512311456298118307304113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12032830550128315486144301 4512311456298118307304113)
  ·
    refine ⟨3384233592223588730478085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512311456298118307304113 3384233592223588730478085)
    ·
      refine ⟨634543798541922886964641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3384233592223588730478085 634543798541922886964641)
      ·
        refine ⟨475907848906442165223481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634543798541922886964641 475907848906442165223481)
        ·
          refine ⟨356930886679831623917611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475907848906442165223481 356930886679831623917611)
          ·
            refine ⟨535396330019747435876417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356930886679831623917611 535396330019747435876417)
            ·
              refine ⟨401547247514810576907313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535396330019747435876417 401547247514810576907313)
              ·
                refine ⟨301160435636107932680485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401547247514810576907313 301160435636107932680485)
                ·
                  refine ⟨56467581681770237377591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301160435636107932680485 56467581681770237377591)
                  ·
                    rfl

theorem cell22_494866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_494866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494866 prefixEnd_494866 := by exact prefixLift 494866
  have htrace : WordTrace (prefixWord ++ tailWord_494866) baseStart_494866 baseEnd_494866 := by
    simpa [prefixWord, tailWord_494866, baseEnd_494866] using wordTrace_append hprefix tailTrace_494866
  have hstable : (prefixWord ++ tailWord_494866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494866).length < 2 ^ (prefixWord ++ tailWord_494866).sum := by decide
  have hdescent : baseEnd_494866 < baseStart_494866 := by decide
  rcases family_descends (prefixWord ++ tailWord_494866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494888 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_494888 : Nat := 118140960795 + 494888 * 2 ^ 59
def prefixEnd_494888 : Nat := 4983230072969 + 3 ^ 40 * 494888 * 2
def baseEnd_494888 : Nat := 56470092031636662694235

theorem tailTrace_494888 : CollatzResearch.WordTrace tailWord_494888 prefixEnd_494888 56470092031636662694235 := by
  unfold tailWord_494888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025024115556385493258659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12033365487408513991011545 9025024115556385493258659)
  ·
    refine ⟨13537536173334578239887989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025024115556385493258659 13537536173334578239887989)
    ·
      refine ⟨1269144016250116709989499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13537536173334578239887989 1269144016250116709989499)
      ·
        refine ⟨1903716024375175064984249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269144016250116709989499 1903716024375175064984249)
        ·
          refine ⟨1427787018281381298738187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903716024375175064984249 1427787018281381298738187)
          ·
            refine ⟨2141680527422071948107281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427787018281381298738187 2141680527422071948107281)
            ·
              refine ⟨1606260395566553961080461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141680527422071948107281 1606260395566553961080461)
              ·
                refine ⟨602347648337457735405173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606260395566553961080461 602347648337457735405173)
                ·
                  refine ⟨56470092031636662694235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602347648337457735405173 56470092031636662694235)
                  ·
                    rfl

theorem cell22_494888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_494888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494888 prefixEnd_494888 := by exact prefixLift 494888
  have htrace : WordTrace (prefixWord ++ tailWord_494888) baseStart_494888 baseEnd_494888 := by
    simpa [prefixWord, tailWord_494888, baseEnd_494888] using wordTrace_append hprefix tailTrace_494888
  have hstable : (prefixWord ++ tailWord_494888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494888).length < 2 ^ (prefixWord ++ tailWord_494888).sum := by decide
  have hdescent : baseEnd_494888 < baseStart_494888 := by decide
  rcases family_descends (prefixWord ++ tailWord_494888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494909 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_494909 : Nat := 118140960795 + 494909 * 2 ^ 59
def prefixEnd_494909 : Nat := 4983230072969 + 3 ^ 40 * 494909 * 2
def baseEnd_494909 : Nat := 169417464824072933307641

theorem tailTrace_494909 : CollatzResearch.WordTrace tailWord_494909 prefixEnd_494909 169417464824072933307641 := by
  unfold tailWord_494909
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050814164036691573031781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033876109357794382021187 18050814164036691573031781)
  ·
    refine ⟨3384527655756879669943459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18050814164036691573031781 3384527655756879669943459)
    ·
      refine ⟨5076791483635319504915189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384527655756879669943459 5076791483635319504915189)
      ·
        refine ⟨475949201590811203585799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5076791483635319504915189 475949201590811203585799)
        ·
          refine ⟨713923802386216805378699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475949201590811203585799 713923802386216805378699)
          ·
            refine ⟨1070885703579325208068049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713923802386216805378699 1070885703579325208068049)
            ·
              refine ⟨803164277684493906051037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070885703579325208068049 803164277684493906051037)
              ·
                refine ⟨301186604131685214769139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803164277684493906051037 301186604131685214769139)
                ·
                  refine ⟨451779906197527822153709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301186604131685214769139 451779906197527822153709)
                  ·
                    refine ⟨169417464824072933307641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451779906197527822153709 169417464824072933307641)
                    ·
                      rfl

theorem cell22_494909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_494909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494909 prefixEnd_494909 := by exact prefixLift 494909
  have htrace : WordTrace (prefixWord ++ tailWord_494909) baseStart_494909 baseEnd_494909 := by
    simpa [prefixWord, tailWord_494909, baseEnd_494909] using wordTrace_append hprefix tailTrace_494909
  have hstable : (prefixWord ++ tailWord_494909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494909).length < 2 ^ (prefixWord ++ tailWord_494909).sum := by decide
  have hdescent : baseEnd_494909 < baseStart_494909 := by decide
  rcases family_descends (prefixWord ++ tailWord_494909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494933 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 6]
def baseStart_494933 : Nat := 118140960795 + 494933 * 2 ^ 59
def prefixEnd_494933 : Nat := 4983230072969 + 3 ^ 40 * 494933 * 2
def baseEnd_494933 : Nat := 56475226838181623569189

theorem tailTrace_494933 : CollatzResearch.WordTrace tailWord_494933 prefixEnd_494933 56475226838181623569189 := by
  unfold tailWord_494933
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051689515949743671905453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12034459677299829114603635 18051689515949743671905453)
  ·
    refine ⟨6769383568481153876964545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18051689515949743671905453 6769383568481153876964545)
    ·
      refine ⟨5077037676360865407723409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6769383568481153876964545 5077037676360865407723409)
      ·
        refine ⟨3807778257270649055792557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077037676360865407723409 3807778257270649055792557)
        ·
          refine ⟨1427916846476493395922209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3807778257270649055792557 1427916846476493395922209)
          ·
            refine ⟨1070937634857370046941657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427916846476493395922209 1070937634857370046941657)
            ·
              refine ⟨803203226143027535206243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070937634857370046941657 803203226143027535206243)
              ·
                refine ⟨1204804839214541302809365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803203226143027535206243 1204804839214541302809365)
                ·
                  refine ⟨56475226838181623569189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1204804839214541302809365 56475226838181623569189)
                  ·
                    rfl

theorem cell22_494933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_494933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494933 prefixEnd_494933 := by exact prefixLift 494933
  have htrace : WordTrace (prefixWord ++ tailWord_494933) baseStart_494933 baseEnd_494933 := by
    simpa [prefixWord, tailWord_494933, baseEnd_494933] using wordTrace_append hprefix tailTrace_494933
  have hstable : (prefixWord ++ tailWord_494933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494933).length < 2 ^ (prefixWord ++ tailWord_494933).sum := by decide
  have hdescent : baseEnd_494933 < baseStart_494933 := by decide
  rcases family_descends (prefixWord ++ tailWord_494933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494948 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_494948 : Nat := 118140960795 + 494948 * 2 ^ 59
def prefixEnd_494948 : Nat := 4983230072969 + 3 ^ 40 * 494948 * 2
def baseEnd_494948 : Nat := 169430815321089831582521

theorem tailTrace_494948 : CollatzResearch.WordTrace tailWord_494948 prefixEnd_494948 169430815321089831582521 := by
  unfold tailWord_494948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026118305447700616850749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12034824407263600822467665 9026118305447700616850749)
  ·
    refine ⟨3384794364542887731319031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9026118305447700616850749 3384794364542887731319031)
    ·
      refine ⟨5077191546814331596978547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384794364542887731319031 5077191546814331596978547)
      ·
        refine ⟨7615787320221497395467821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077191546814331596978547 7615787320221497395467821)
        ·
          refine ⟨2855920245083061523300433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7615787320221497395467821 2855920245083061523300433)
          ·
            refine ⟨2141940183812296142475325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855920245083061523300433 2141940183812296142475325)
            ·
              refine ⟨803227568929611053428247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2141940183812296142475325 803227568929611053428247)
              ·
                refine ⟨1204841353394416580142371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803227568929611053428247 1204841353394416580142371)
                ·
                  refine ⟨1807262030091624870213557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204841353394416580142371 1807262030091624870213557)
                  ·
                    refine ⟨169430815321089831582521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1807262030091624870213557 169430815321089831582521)
                    ·
                      rfl

theorem cell22_494948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_494948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_494948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_494948 prefixEnd_494948 := by exact prefixLift 494948
  have htrace : WordTrace (prefixWord ++ tailWord_494948) baseStart_494948 baseEnd_494948 := by
    simpa [prefixWord, tailWord_494948, baseEnd_494948] using wordTrace_append hprefix tailTrace_494948
  have hstable : (prefixWord ++ tailWord_494948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494948).length < 2 ^ (prefixWord ++ tailWord_494948).sum := by decide
  have hdescent : baseEnd_494948 < baseStart_494948 := by decide
  rcases family_descends (prefixWord ++ tailWord_494948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495038 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_495038 : Nat := 118140960795 + 495038 * 2 ^ 59
def prefixEnd_495038 : Nat := 4983230072969 + 3 ^ 40 * 495038 * 2
def baseEnd_495038 : Nat := 169461624160359596832245

theorem tailTrace_495038 : CollatzResearch.WordTrace tailWord_495038 prefixEnd_495038 169461624160359596832245 := by
  unfold tailWord_495038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256939897571168325559721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12037012787046231069651845 2256939897571168325559721)
  ·
    refine ⟨1692704923178376244169791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2256939897571168325559721 1692704923178376244169791)
    ·
      refine ⟨2539057384767564366254687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692704923178376244169791 2539057384767564366254687)
      ·
        refine ⟨3808586077151346549382031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539057384767564366254687 3808586077151346549382031)
        ·
          refine ⟨5712879115727019824073047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808586077151346549382031 5712879115727019824073047)
          ·
            refine ⟨8569318673590529736109571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712879115727019824073047 8569318673590529736109571)
            ·
              refine ⟨12853978010385794604164357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569318673590529736109571 12853978010385794604164357)
              ·
                refine ⟨2410120876947336488280817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12853978010385794604164357 2410120876947336488280817)
                ·
                  refine ⟨1807590657710502366210613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410120876947336488280817 1807590657710502366210613)
                  ·
                    refine ⟨169461624160359596832245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1807590657710502366210613 169461624160359596832245)
                    ·
                      rfl

theorem cell22_495038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_495038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495038 prefixEnd_495038 := by exact prefixLift 495038
  have htrace : WordTrace (prefixWord ++ tailWord_495038) baseStart_495038 baseEnd_495038 := by
    simpa [prefixWord, tailWord_495038, baseEnd_495038] using wordTrace_append hprefix tailTrace_495038
  have hstable : (prefixWord ++ tailWord_495038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495038).length < 2 ^ (prefixWord ++ tailWord_495038).sum := by decide
  have hdescent : baseEnd_495038 < baseStart_495038 := by decide
  rcases family_descends (prefixWord ++ tailWord_495038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495044 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_495044 : Nat := 118140960795 + 495044 * 2 ^ 59
def prefixEnd_495044 : Nat := 4983230072969 + 3 ^ 40 * 495044 * 2
def baseEnd_495044 : Nat := 169463678082977581182227

theorem tailTrace_495044 : CollatzResearch.WordTrace tailWord_495044 prefixEnd_495044 169463678082977581182227 := by
  unfold tailWord_495044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027869009273804814598093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12037158679031739752797457 9027869009273804814598093)
  ·
    refine ⟨3385450878477676805474285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9027869009273804814598093 3385450878477676805474285)
    ·
      refine ⟨1269544079429128802052857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3385450878477676805474285 1269544079429128802052857)
      ·
        refine ⟨952158059571846601539643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269544079429128802052857 952158059571846601539643)
        ·
          refine ⟨1428237089357769902309465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952158059571846601539643 1428237089357769902309465)
          ·
            refine ⟨1071177817018327426732099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428237089357769902309465 1071177817018327426732099)
            ·
              refine ⟨1606766725527491140098149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071177817018327426732099 1606766725527491140098149)
              ·
                refine ⟨301268761036404588768403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1606766725527491140098149 301268761036404588768403)
                ·
                  refine ⟨451903141554606883152605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301268761036404588768403 451903141554606883152605)
                  ·
                    refine ⟨169463678082977581182227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 451903141554606883152605 169463678082977581182227)
                    ·
                      rfl

theorem cell22_495044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_495044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495044 prefixEnd_495044 := by exact prefixLift 495044
  have htrace : WordTrace (prefixWord ++ tailWord_495044) baseStart_495044 baseEnd_495044 := by
    simpa [prefixWord, tailWord_495044, baseEnd_495044] using wordTrace_append hprefix tailTrace_495044
  have hstable : (prefixWord ++ tailWord_495044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495044).length < 2 ^ (prefixWord ++ tailWord_495044).sum := by decide
  have hdescent : baseEnd_495044 < baseStart_495044 := by decide
  rcases family_descends (prefixWord ++ tailWord_495044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495098 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_495098 : Nat := 118140960795 + 495098 * 2 ^ 59
def prefixEnd_495098 : Nat := 4983230072969 + 3 ^ 40 * 495098 * 2
def baseEnd_495098 : Nat := 169482163386539440332061

theorem tailTrace_495098 : CollatzResearch.WordTrace tailWord_495098 prefixEnd_495098 169482163386539440332061 := by
  unfold tailWord_495098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514426890087994212915487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12038471706901317901107965 4514426890087994212915487)
  ·
    refine ⟨6771640335131991319373231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4514426890087994212915487 6771640335131991319373231)
    ·
      refine ⟨10157460502697986979059847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771640335131991319373231 10157460502697986979059847)
      ·
        refine ⟨15236190754046980468589771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157460502697986979059847 15236190754046980468589771)
        ·
          refine ⟨22854286131070470702884657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236190754046980468589771 22854286131070470702884657)
          ·
            refine ⟨17140714598302853027163493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22854286131070470702884657 17140714598302853027163493)
            ·
              refine ⟨3213883987181784942593155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17140714598302853027163493 3213883987181784942593155)
              ·
                refine ⟨4820825980772677413889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213883987181784942593155 4820825980772677413889733)
                ·
                  refine ⟨903904871394877015104325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4820825980772677413889733 903904871394877015104325)
                  ·
                    refine ⟨169482163386539440332061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903904871394877015104325 169482163386539440332061)
                    ·
                      rfl

theorem cell22_495098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_495098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495098 prefixEnd_495098 := by exact prefixLift 495098
  have htrace : WordTrace (prefixWord ++ tailWord_495098) baseStart_495098 baseEnd_495098 := by
    simpa [prefixWord, tailWord_495098, baseEnd_495098] using wordTrace_append hprefix tailTrace_495098
  have hstable : (prefixWord ++ tailWord_495098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495098).length < 2 ^ (prefixWord ++ tailWord_495098).sum := by decide
  have hdescent : baseEnd_495098 < baseStart_495098 := by decide
  rcases family_descends (prefixWord ++ tailWord_495098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495173 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_495173 : Nat := 118140960795 + 495173 * 2 ^ 59
def prefixEnd_495173 : Nat := 4983230072969 + 3 ^ 40 * 495173 * 2
def baseEnd_495173 : Nat := 169507837419264244706831

theorem tailTrace_495173 : CollatzResearch.WordTrace tailWord_495173 prefixEnd_495173 169507837419264244706831 := by
  unfold tailWord_495173
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060443035080264660642173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12040295356720176440428115 18060443035080264660642173)
  ·
    refine ⟨6772666138155099247740815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18060443035080264660642173 6772666138155099247740815)
    ·
      refine ⟨10158999207232648871611223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772666138155099247740815 10158999207232648871611223)
      ·
        refine ⟨15238498810848973307416835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158999207232648871611223 15238498810848973307416835)
        ·
          refine ⟨22857748216273459961125253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238498810848973307416835 22857748216273459961125253)
          ·
            refine ⟨4285827790551273742710985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22857748216273459961125253 4285827790551273742710985)
            ·
              refine ⟨3214370842913455307033239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285827790551273742710985 3214370842913455307033239)
              ·
                refine ⟨4821556264370182960549859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214370842913455307033239 4821556264370182960549859)
                ·
                  refine ⟨7232334396555274440824789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4821556264370182960549859 7232334396555274440824789)
                  ·
                    refine ⟨169507837419264244706831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7232334396555274440824789 169507837419264244706831)
                    ·
                      rfl

theorem cell22_495173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_495173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495173 prefixEnd_495173 := by exact prefixLift 495173
  have htrace : WordTrace (prefixWord ++ tailWord_495173) baseStart_495173 baseEnd_495173 := by
    simpa [prefixWord, tailWord_495173, baseEnd_495173] using wordTrace_append hprefix tailTrace_495173
  have hstable : (prefixWord ++ tailWord_495173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495173).length < 2 ^ (prefixWord ++ tailWord_495173).sum := by decide
  have hdescent : baseEnd_495173 < baseStart_495173 := by decide
  rcases family_descends (prefixWord ++ tailWord_495173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495213 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_495213 : Nat := 118140960795 + 495213 * 2 ^ 59
def prefixEnd_495213 : Nat := 4983230072969 + 3 ^ 40 * 495213 * 2
def baseEnd_495213 : Nat := 169521530236717473706709

theorem tailTrace_495213 : CollatzResearch.WordTrace tailWord_495213 prefixEnd_495213 169521530236717473706709 := by
  unfold tailWord_495213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061901954935351492098293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041267969956900994732195 18061901954935351492098293)
  ·
    refine ⟨1693303308275189202384215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18061901954935351492098293 1693303308275189202384215)
    ·
      refine ⟨2539954962412783803576323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693303308275189202384215 2539954962412783803576323)
      ·
        refine ⟨3809932443619175705364485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539954962412783803576323 3809932443619175705364485)
        ·
          refine ⟨714362333178595444755841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3809932443619175705364485 714362333178595444755841)
          ·
            refine ⟨535771749883946583566881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714362333178595444755841 535771749883946583566881)
            ·
              refine ⟨401828812412959937675161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535771749883946583566881 401828812412959937675161)
              ·
                refine ⟨301371609309719953256371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401828812412959937675161 301371609309719953256371)
                ·
                  refine ⟨452057413964579929884557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301371609309719953256371 452057413964579929884557)
                  ·
                    refine ⟨169521530236717473706709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452057413964579929884557 169521530236717473706709)
                    ·
                      rfl

theorem cell22_495213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_495213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495213 prefixEnd_495213 := by exact prefixLift 495213
  have htrace : WordTrace (prefixWord ++ tailWord_495213) baseStart_495213 baseEnd_495213 := by
    simpa [prefixWord, tailWord_495213, baseEnd_495213] using wordTrace_append hprefix tailTrace_495213
  have hstable : (prefixWord ++ tailWord_495213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495213).length < 2 ^ (prefixWord ++ tailWord_495213).sum := by decide
  have hdescent : baseEnd_495213 < baseStart_495213 := by decide
  rcases family_descends (prefixWord ++ tailWord_495213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495222 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_495222 : Nat := 118140960795 + 495222 * 2 ^ 59
def prefixEnd_495222 : Nat := 4983230072969 + 3 ^ 40 * 495222 * 2
def baseEnd_495222 : Nat := 169524611120644450231681

theorem tailTrace_495222 : CollatzResearch.WordTrace tailWord_495222 prefixEnd_495222 169524611120644450231681 := by
  unfold tailWord_495222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128889388243921626823495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12041486807935164019450613 1128889388243921626823495)
  ·
    refine ⟨1693334082365882440235243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128889388243921626823495 1693334082365882440235243)
    ·
      refine ⟨2540001123548823660352865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693334082365882440235243 2540001123548823660352865)
      ·
        refine ⟨1905000842661617745264649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540001123548823660352865 1905000842661617745264649)
        ·
          refine ⟨1428750631996213308948487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905000842661617745264649 1428750631996213308948487)
          ·
            refine ⟨2143125947994319963422731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428750631996213308948487 2143125947994319963422731)
            ·
              refine ⟨3214688921991479945134097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143125947994319963422731 3214688921991479945134097)
              ·
                refine ⟨2411016691493609958850573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214688921991479945134097 2411016691493609958850573)
                ·
                  refine ⟨904131259310103734568965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2411016691493609958850573 904131259310103734568965)
                  ·
                    refine ⟨169524611120644450231681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904131259310103734568965 169524611120644450231681)
                    ·
                      rfl

theorem cell22_495222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_495222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495222 prefixEnd_495222 := by exact prefixLift 495222
  have htrace : WordTrace (prefixWord ++ tailWord_495222) baseStart_495222 baseEnd_495222 := by
    simpa [prefixWord, tailWord_495222, baseEnd_495222] using wordTrace_append hprefix tailTrace_495222
  have hstable : (prefixWord ++ tailWord_495222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495222).length < 2 ^ (prefixWord ++ tailWord_495222).sum := by decide
  have hdescent : baseEnd_495222 < baseStart_495222 := by decide
  rcases family_descends (prefixWord ++ tailWord_495222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495235 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 6, 3]
def baseStart_495235 : Nat := 118140960795 + 495235 * 2 ^ 59
def prefixEnd_495235 : Nat := 4983230072969 + 3 ^ 40 * 495235 * 2
def baseEnd_495235 : Nat := 169529061286316749656641

theorem tailTrace_495235 : CollatzResearch.WordTrace tailWord_495235 prefixEnd_495235 169529061286316749656641 := by
  unfold tailWord_495235
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062704360855649249399159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041802907237099499599439 18062704360855649249399159)
  ·
    refine ⟨27094056541283473874098739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062704360855649249399159 27094056541283473874098739)
    ·
      refine ⟨40641084811925210811148109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27094056541283473874098739 40641084811925210811148109)
      ·
        refine ⟨15240406804471954054180541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40641084811925210811148109 15240406804471954054180541)
        ·
          refine ⟨5715152551676982770317703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15240406804471954054180541 5715152551676982770317703)
          ·
            refine ⟨8572728827515474155476555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715152551676982770317703 8572728827515474155476555)
            ·
              refine ⟨12859093241273211233214833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572728827515474155476555 12859093241273211233214833)
              ·
                refine ⟨9644319930954908424911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859093241273211233214833 9644319930954908424911125)
                ·
                  refine ⟨452077496763511332417709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9644319930954908424911125 452077496763511332417709)
                  ·
                    refine ⟨169529061286316749656641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452077496763511332417709 169529061286316749656641)
                    ·
                      rfl

theorem cell22_495235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].length) (baseStart_495235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495235 prefixEnd_495235 := by exact prefixLift 495235
  have htrace : WordTrace (prefixWord ++ tailWord_495235) baseStart_495235 baseEnd_495235 := by
    simpa [prefixWord, tailWord_495235, baseEnd_495235] using wordTrace_append hprefix tailTrace_495235
  have hstable : (prefixWord ++ tailWord_495235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495235).length < 2 ^ (prefixWord ++ tailWord_495235).sum := by decide
  have hdescent : baseEnd_495235 < baseStart_495235 := by decide
  rcases family_descends (prefixWord ++ tailWord_495235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495248 : List Nat := [2, 1, 1, 1, 1, 1, 3, 12]
def baseStart_495248 : Nat := 118140960795 + 495248 * 2 ^ 59
def prefixEnd_495248 : Nat := 4983230072969 + 3 ^ 40 * 495248 * 2
def baseEnd_495248 : Nat := 18837056827998783231289

theorem tailTrace_495248 : CollatzResearch.WordTrace tailWord_495248 prefixEnd_495248 18837056827998783231289 := by
  unfold tailWord_495248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031589254904276234811199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12042119006539034979748265 9031589254904276234811199)
  ·
    refine ⟨13547383882356414352216799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9031589254904276234811199 13547383882356414352216799)
    ·
      refine ⟨20321075823534621528325199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547383882356414352216799 20321075823534621528325199)
      ·
        refine ⟨30481613735301932292487799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20321075823534621528325199 30481613735301932292487799)
        ·
          refine ⟨45722420602952898438731699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30481613735301932292487799 45722420602952898438731699)
          ·
            refine ⟨68583630904429347658097549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45722420602952898438731699 68583630904429347658097549)
            ·
              refine ⟨25718861589161005371786581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68583630904429347658097549 25718861589161005371786581)
              ·
                refine ⟨18837056827998783231289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 25718861589161005371786581 18837056827998783231289)
                ·
                  rfl

theorem cell22_495248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_495248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495248 prefixEnd_495248 := by exact prefixLift 495248
  have htrace : WordTrace (prefixWord ++ tailWord_495248) baseStart_495248 baseEnd_495248 := by
    simpa [prefixWord, tailWord_495248, baseEnd_495248] using wordTrace_append hprefix tailTrace_495248
  have hstable : (prefixWord ++ tailWord_495248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495248).length < 2 ^ (prefixWord ++ tailWord_495248).sum := by decide
  have hdescent : baseEnd_495248 < baseStart_495248 := by decide
  rcases family_descends (prefixWord ++ tailWord_495248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495265 : List Nat := [1, 2, 3, 3, 2, 2, 9]
def baseStart_495265 : Nat := 118140960795 + 495265 * 2 ^ 59
def prefixEnd_495265 : Nat := 4983230072969 + 3 ^ 40 * 495265 * 2
def baseEnd_495265 : Nat := 6279234477755802644687

theorem tailTrace_495265 : CollatzResearch.WordTrace tailWord_495265 prefixEnd_495265 6279234477755802644687 := by
  unfold tailWord_495265
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063798550746964372991249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12042532367164642915327499 18063798550746964372991249)
  ·
    refine ⟨13547848913060223279743437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18063798550746964372991249 13547848913060223279743437)
    ·
      refine ⟨5080443342397583729903789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13547848913060223279743437 5080443342397583729903789)
      ·
        refine ⟨1905166253399093898713921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5080443342397583729903789 1905166253399093898713921)
        ·
          refine ⟨1428874690049320424035441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905166253399093898713921 1428874690049320424035441)
          ·
            refine ⟨1071656017536990318026581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428874690049320424035441 1071656017536990318026581)
            ·
              refine ⟨6279234477755802644687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1071656017536990318026581 6279234477755802644687)
              ·
                rfl

theorem cell22_495265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 9].length) (baseStart_495265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495265 prefixEnd_495265 := by exact prefixLift 495265
  have htrace : WordTrace (prefixWord ++ tailWord_495265) baseStart_495265 baseEnd_495265 := by
    simpa [prefixWord, tailWord_495265, baseEnd_495265] using wordTrace_append hprefix tailTrace_495265
  have hstable : (prefixWord ++ tailWord_495265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495265).length < 2 ^ (prefixWord ++ tailWord_495265).sum := by decide
  have hdescent : baseEnd_495265 < baseStart_495265 := by decide
  rcases family_descends (prefixWord ++ tailWord_495265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495286 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_495286 : Nat := 118140960795 + 495286 * 2 ^ 59
def prefixEnd_495286 : Nat := 4983230072969 + 3 ^ 40 * 495286 * 2
def baseEnd_495286 : Nat := 169546519628569616631485

theorem tailTrace_495286 : CollatzResearch.WordTrace tailWord_495286 prefixEnd_495286 169546519628569616631485 := by
  unfold tailWord_495286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129035280229430309969107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12043042989113923306337141 1129035280229430309969107)
  ·
    refine ⟨1693552920344145464953661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129035280229430309969107 1693552920344145464953661)
    ·
      refine ⟨635082345129054549357623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1693552920344145464953661 635082345129054549357623)
      ·
        refine ⟨952623517693581824036435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635082345129054549357623 952623517693581824036435)
        ·
          refine ⟨1428935276540372736054653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952623517693581824036435 1428935276540372736054653)
          ·
            refine ⟨535850728702639776020495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1428935276540372736054653 535850728702639776020495)
            ·
              refine ⟨803776093053959664030743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535850728702639776020495 803776093053959664030743)
              ·
                refine ⟨1205664139580939496046115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803776093053959664030743 1205664139580939496046115)
                ·
                  refine ⟨1808496209371409244069173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205664139580939496046115 1808496209371409244069173)
                  ·
                    refine ⟨169546519628569616631485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1808496209371409244069173 169546519628569616631485)
                    ·
                      rfl

theorem cell22_495286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_495286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495286 prefixEnd_495286 := by exact prefixLift 495286
  have htrace : WordTrace (prefixWord ++ tailWord_495286) baseStart_495286 baseEnd_495286 := by
    simpa [prefixWord, tailWord_495286, baseEnd_495286] using wordTrace_append hprefix tailTrace_495286
  have hstable : (prefixWord ++ tailWord_495286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495286).length < 2 ^ (prefixWord ++ tailWord_495286).sum := by decide
  have hdescent : baseEnd_495286 < baseStart_495286 := by decide
  rcases family_descends (prefixWord ++ tailWord_495286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495310 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_495310 : Nat := 118140960795 + 495310 * 2 ^ 59
def prefixEnd_495310 : Nat := 4983230072969 + 3 ^ 40 * 495310 * 2
def baseEnd_495310 : Nat := 56518245106347184677137

theorem tailTrace_495310 : CollatzResearch.WordTrace tailWord_495310 prefixEnd_495310 56518245106347184677137 := by
  unfold tailWord_495310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258179979447992132297423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12043626557055958038919589 2258179979447992132297423)
  ·
    refine ⟨3387269969171988198446135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2258179979447992132297423 3387269969171988198446135)
    ·
      refine ⟨5080904953757982297669203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387269969171988198446135 5080904953757982297669203)
      ·
        refine ⟨7621357430636973446503805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080904953757982297669203 7621357430636973446503805)
        ·
          refine ⟨2858009036488865042438927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7621357430636973446503805 2858009036488865042438927)
          ·
            refine ⟨4287013554733297563658391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858009036488865042438927 4287013554733297563658391)
            ·
              refine ⟨6430520332099946345487587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287013554733297563658391 6430520332099946345487587)
              ·
                refine ⟨9645780498149919518231381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430520332099946345487587 9645780498149919518231381)
                ·
                  refine ⟨56518245106347184677137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9645780498149919518231381 56518245106347184677137)
                  ·
                    rfl

theorem cell22_495310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_495310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495310 prefixEnd_495310 := by exact prefixLift 495310
  have htrace : WordTrace (prefixWord ++ tailWord_495310) baseStart_495310 baseEnd_495310 := by
    simpa [prefixWord, tailWord_495310, baseEnd_495310] using wordTrace_append hprefix tailTrace_495310
  have hstable : (prefixWord ++ tailWord_495310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495310).length < 2 ^ (prefixWord ++ tailWord_495310).sum := by decide
  have hdescent : baseEnd_495310 < baseStart_495310 := by decide
  rcases family_descends (prefixWord ++ tailWord_495310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495331 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 3, 3]
def baseStart_495331 : Nat := 118140960795 + 495331 * 2 ^ 59
def prefixEnd_495331 : Nat := 4983230072969 + 3 ^ 40 * 495331 * 2
def baseEnd_495331 : Nat := 169561924048204499256347

theorem tailTrace_495331 : CollatzResearch.WordTrace tailWord_495331 prefixEnd_495331 169561924048204499256347 := by
  unfold tailWord_495331
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066205768507857644893847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12044137179005238429929231 18066205768507857644893847)
  ·
    refine ⟨27099308652761786467340771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18066205768507857644893847 27099308652761786467340771)
    ·
      refine ⟨40648962979142679701011157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27099308652761786467340771 40648962979142679701011157)
      ·
        refine ⟨952710069823656555492449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 40648962979142679701011157 952710069823656555492449)
        ·
          refine ⟨714532552367742416619337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952710069823656555492449 714532552367742416619337)
          ·
            refine ⟨535899414275806812464503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714532552367742416619337 535899414275806812464503)
            ·
              refine ⟨803849121413710218696755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535899414275806812464503 803849121413710218696755)
              ·
                refine ⟨1205773682120565328045133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803849121413710218696755 1205773682120565328045133)
                ·
                  refine ⟨452165130795211998016925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205773682120565328045133 452165130795211998016925)
                  ·
                    refine ⟨169561924048204499256347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452165130795211998016925 169561924048204499256347)
                    ·
                      rfl

theorem cell22_495331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].length) (baseStart_495331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495331 prefixEnd_495331 := by exact prefixLift 495331
  have htrace : WordTrace (prefixWord ++ tailWord_495331) baseStart_495331 baseEnd_495331 := by
    simpa [prefixWord, tailWord_495331, baseEnd_495331] using wordTrace_append hprefix tailTrace_495331
  have hstable : (prefixWord ++ tailWord_495331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495331).length < 2 ^ (prefixWord ++ tailWord_495331).sum := by decide
  have hdescent : baseEnd_495331 < baseStart_495331 := by decide
  rcases family_descends (prefixWord ++ tailWord_495331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495357 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_495357 : Nat := 118140960795 + 495357 * 2 ^ 59
def prefixEnd_495357 : Nat := 4983230072969 + 3 ^ 40 * 495357 * 2
def baseEnd_495357 : Nat := 169570824379549098106267

theorem tailTrace_495357 : CollatzResearch.WordTrace tailWord_495357 prefixEnd_495357 169570824379549098106267 := by
  unfold tailWord_495357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067154066413664085340325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12044769377609109390226883 18067154066413664085340325)
  ·
    refine ⟨3387591387452562016001311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18067154066413664085340325 3387591387452562016001311)
    ·
      refine ⟨5081387081178843024001967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387591387452562016001311 5081387081178843024001967)
      ·
        refine ⟨7622080621768264536002951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081387081178843024001967 7622080621768264536002951)
        ·
          refine ⟨11433120932652396804004427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622080621768264536002951 11433120932652396804004427)
          ·
            refine ⟨17149681398978595206006641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433120932652396804004427 17149681398978595206006641)
            ·
              refine ⟨12862261049233946404504981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17149681398978595206006641 12862261049233946404504981)
              ·
                refine ⟨602918486682841237711171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12862261049233946404504981 602918486682841237711171)
                ·
                  refine ⟨904377730024261856566757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602918486682841237711171 904377730024261856566757)
                  ·
                    refine ⟨169570824379549098106267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904377730024261856566757 169570824379549098106267)
                    ·
                      rfl

theorem cell22_495357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_495357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495357 prefixEnd_495357 := by exact prefixLift 495357
  have htrace : WordTrace (prefixWord ++ tailWord_495357) baseStart_495357 baseEnd_495357 := by
    simpa [prefixWord, tailWord_495357, baseEnd_495357] using wordTrace_append hprefix tailTrace_495357
  have hstable : (prefixWord ++ tailWord_495357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495357).length < 2 ^ (prefixWord ++ tailWord_495357).sum := by decide
  have hdescent : baseEnd_495357 < baseStart_495357 := by decide
  rcases family_descends (prefixWord ++ tailWord_495357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495404 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_495404 : Nat := 118140960795 + 495404 * 2 ^ 59
def prefixEnd_495404 : Nat := 4983230072969 + 3 ^ 40 * 495404 * 2
def baseEnd_495404 : Nat := 169586913440056642181123

theorem tailTrace_495404 : CollatzResearch.WordTrace tailWord_495404 prefixEnd_495404 169586913440056642181123 := by
  unfold tailWord_495404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034434148621695556150633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12045912198162260741534177 9034434148621695556150633)
  ·
    refine ⟨6775825611466271667112975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9034434148621695556150633 6775825611466271667112975)
    ·
      refine ⟨10163738417199407500669463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775825611466271667112975 10163738417199407500669463)
      ·
        refine ⟨15245607625799111251004195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163738417199407500669463 15245607625799111251004195)
        ·
          refine ⟨22868411438698666876506293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15245607625799111251004195 22868411438698666876506293)
          ·
            refine ⟨2143913572378000019672465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22868411438698666876506293 2143913572378000019672465)
            ·
              refine ⟨1607935179283500014754349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143913572378000019672465 1607935179283500014754349)
              ·
                refine ⟨602975692231312505532881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607935179283500014754349 602975692231312505532881)
                ·
                  refine ⟨452231769173484379149661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602975692231312505532881 452231769173484379149661)
                  ·
                    refine ⟨169586913440056642181123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452231769173484379149661 169586913440056642181123)
                    ·
                      rfl

theorem cell22_495404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_495404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495404 prefixEnd_495404 := by exact prefixLift 495404
  have htrace : WordTrace (prefixWord ++ tailWord_495404) baseStart_495404 baseEnd_495404 := by
    simpa [prefixWord, tailWord_495404, baseEnd_495404] using wordTrace_append hprefix tailTrace_495404
  have hstable : (prefixWord ++ tailWord_495404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495404).length < 2 ^ (prefixWord ++ tailWord_495404).sum := by decide
  have hdescent : baseEnd_495404 < baseStart_495404 := by decide
  rcases family_descends (prefixWord ++ tailWord_495404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495415 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_495415 : Nat := 118140960795 + 495415 * 2 ^ 59
def prefixEnd_495415 : Nat := 4983230072969 + 3 ^ 40 * 495415 * 2
def baseEnd_495415 : Nat := 169590678964856280156089

theorem tailTrace_495415 : CollatzResearch.WordTrace tailWord_495415 prefixEnd_495415 169590678964856280156089 := by
  unfold tailWord_495415
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069269500203539990951699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046179666802359993967799 18069269500203539990951699)
  ·
    refine ⟨27103904250305309986427549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18069269500203539990951699 27103904250305309986427549)
    ·
      refine ⟨10163964093864491244910331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27103904250305309986427549 10163964093864491244910331)
      ·
        refine ⟨15245946140796736867365497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163964093864491244910331 15245946140796736867365497)
        ·
          refine ⟨11434459605597552650524123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15245946140796736867365497 11434459605597552650524123)
          ·
            refine ⟨17151689408396328975786185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11434459605597552650524123 17151689408396328975786185)
            ·
              refine ⟨12863767056297246731839639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17151689408396328975786185 12863767056297246731839639)
              ·
                refine ⟨19295650584445870097759459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12863767056297246731839639 19295650584445870097759459)
                ·
                  refine ⟨28943475876668805146639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19295650584445870097759459 28943475876668805146639189)
                  ·
                    refine ⟨169590678964856280156089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 28943475876668805146639189 169590678964856280156089)
                    ·
                      rfl

theorem cell22_495415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_495415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495415 prefixEnd_495415 := by exact prefixLift 495415
  have htrace : WordTrace (prefixWord ++ tailWord_495415) baseStart_495415 baseEnd_495415 := by
    simpa [prefixWord, tailWord_495415, baseEnd_495415] using wordTrace_append hprefix tailTrace_495415
  have hstable : (prefixWord ++ tailWord_495415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495415).length < 2 ^ (prefixWord ++ tailWord_495415).sum := by decide
  have hdescent : baseEnd_495415 < baseStart_495415 := by decide
  rcases family_descends (prefixWord ++ tailWord_495415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495449 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_495449 : Nat := 118140960795 + 495449 * 2 ^ 59
def prefixEnd_495449 : Nat := 4983230072969 + 3 ^ 40 * 495449 * 2
def baseEnd_495449 : Nat := 169602317859691524805985

theorem tailTrace_495449 : CollatzResearch.WordTrace tailWord_495449 prefixEnd_495449 169602317859691524805985 := by
  unfold tailWord_495449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070509582080363797689401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12047006388053575865126267 18070509582080363797689401)
  ·
    refine ⟨13552882186560272848267051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18070509582080363797689401 13552882186560272848267051)
    ·
      refine ⟨20329323279840409272400577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13552882186560272848267051 20329323279840409272400577)
      ·
        refine ⟨15246992459880306954300433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20329323279840409272400577 15246992459880306954300433)
        ·
          refine ⟨11435244344910230215725325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15246992459880306954300433 11435244344910230215725325)
          ·
            refine ⟨4288216629341336330896997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11435244344910230215725325 4288216629341336330896997)
            ·
              refine ⟨804040618001500562043187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4288216629341336330896997 804040618001500562043187)
              ·
                refine ⟨1206060927002250843064781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804040618001500562043187 1206060927002250843064781)
                ·
                  refine ⟨452272847625844066149293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206060927002250843064781 452272847625844066149293)
                  ·
                    refine ⟨169602317859691524805985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452272847625844066149293 169602317859691524805985)
                    ·
                      rfl

theorem cell22_495449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_495449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495449 prefixEnd_495449 := by exact prefixLift 495449
  have htrace : WordTrace (prefixWord ++ tailWord_495449) baseStart_495449 baseEnd_495449 := by
    simpa [prefixWord, tailWord_495449, baseEnd_495449] using wordTrace_append hprefix tailTrace_495449
  have hstable : (prefixWord ++ tailWord_495449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495449).length < 2 ^ (prefixWord ++ tailWord_495449).sum := by decide
  have hdescent : baseEnd_495449 < baseStart_495449 := by decide
  rcases family_descends (prefixWord ++ tailWord_495449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495652 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_495652 : Nat := 118140960795 + 495652 * 2 ^ 59
def prefixEnd_495652 : Nat := 4983230072969 + 3 ^ 40 * 495652 * 2
def baseEnd_495652 : Nat := 169671808908266661980363

theorem tailTrace_495652 : CollatzResearch.WordTrace tailWord_495652 prefixEnd_495652 169671808908266661980363 := by
  unfold tailWord_495652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038956800172464733664605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12051942400229952978219473 9038956800172464733664605)
  ·
    refine ⟨3389608800064674275124227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9038956800172464733664605 3389608800064674275124227)
    ·
      refine ⟨5084413200097011412686341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389608800064674275124227 5084413200097011412686341)
      ·
        refine ⟨953327475018189639878689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5084413200097011412686341 953327475018189639878689)
        ·
          refine ⟨714995606263642229909017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953327475018189639878689 714995606263642229909017)
          ·
            refine ⟨536246704697731672431763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714995606263642229909017 536246704697731672431763)
            ·
              refine ⟨804370057046597508647645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536246704697731672431763 804370057046597508647645)
              ·
                refine ⟨301638771392474065742867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804370057046597508647645 301638771392474065742867)
                ·
                  refine ⟨452458157088711098614301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301638771392474065742867 452458157088711098614301)
                  ·
                    refine ⟨169671808908266661980363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452458157088711098614301 169671808908266661980363)
                    ·
                      rfl

theorem cell22_495652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_495652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495652 prefixEnd_495652 := by exact prefixLift 495652
  have htrace : WordTrace (prefixWord ++ tailWord_495652) baseStart_495652 baseEnd_495652 := by
    simpa [prefixWord, tailWord_495652, baseEnd_495652] using wordTrace_append hprefix tailTrace_495652
  have hstable : (prefixWord ++ tailWord_495652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495652).length < 2 ^ (prefixWord ++ tailWord_495652).sum := by decide
  have hdescent : baseEnd_495652 < baseStart_495652 := by decide
  rcases family_descends (prefixWord ++ tailWord_495652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495689 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_495689 : Nat := 118140960795 + 495689 * 2 ^ 59
def prefixEnd_495689 : Nat := 4983230072969 + 3 ^ 40 * 495689 * 2
def baseEnd_495689 : Nat := 169684474764410898805249

theorem tailTrace_495689 : CollatzResearch.WordTrace tailWord_495689 prefixEnd_495689 169684474764410898805249 := by
  unfold tailWord_495689
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079263101210884786426121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12052842067473923190950747 18079263101210884786426121)
  ·
    refine ⟨13559447325908163589819591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18079263101210884786426121 13559447325908163589819591)
    ·
      refine ⟨20339170988862245384729387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559447325908163589819591 20339170988862245384729387)
      ·
        refine ⟨30508756483293368077094081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20339170988862245384729387 30508756483293368077094081)
        ·
          refine ⟨22881567362470026057820561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30508756483293368077094081 22881567362470026057820561)
          ·
            refine ⟨17161175521852519543365421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22881567362470026057820561 17161175521852519543365421)
            ·
              refine ⟨6435440820694694828762033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17161175521852519543365421 6435440820694694828762033)
              ·
                refine ⟨4826580615521021121571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6435440820694694828762033 4826580615521021121571525)
                ·
                  refine ⟨904983865410191460294661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4826580615521021121571525 904983865410191460294661)
                  ·
                    refine ⟨169684474764410898805249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904983865410191460294661 169684474764410898805249)
                    ·
                      rfl

theorem cell22_495689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_495689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495689 prefixEnd_495689 := by exact prefixLift 495689
  have htrace : WordTrace (prefixWord ++ tailWord_495689) baseStart_495689 baseEnd_495689 := by
    simpa [prefixWord, tailWord_495689, baseEnd_495689] using wordTrace_append hprefix tailTrace_495689
  have hstable : (prefixWord ++ tailWord_495689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495689).length < 2 ^ (prefixWord ++ tailWord_495689).sum := by decide
  have hdescent : baseEnd_495689 < baseStart_495689 := by decide
  rcases family_descends (prefixWord ++ tailWord_495689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495691 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 2, 3]
def baseStart_495691 : Nat := 118140960795 + 495691 * 2 ^ 59
def prefixEnd_495691 : Nat := 4983230072969 + 3 ^ 40 * 495691 * 2
def baseEnd_495691 : Nat := 169685159405283560255243

theorem tailTrace_495691 : CollatzResearch.WordTrace tailWord_495691 prefixEnd_495691 169685159405283560255243 := by
  unfold tailWord_495691
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079336047203639127998927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12052890698135759418665951 18079336047203639127998927)
  ·
    refine ⟨27119004070805458691998391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18079336047203639127998927 27119004070805458691998391)
    ·
      refine ⟨40678506106208188037997587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27119004070805458691998391 40678506106208188037997587)
      ·
        refine ⟨61017759159312282056996381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40678506106208188037997587 61017759159312282056996381)
        ·
          refine ⟨22881659684742105771373643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61017759159312282056996381 22881659684742105771373643)
          ·
            refine ⟨34322489527113158657060465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22881659684742105771373643 34322489527113158657060465)
            ·
              refine ⟨25741867145334868992795349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34322489527113158657060465 25741867145334868992795349)
              ·
                refine ⟨603325011218785992018641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25741867145334868992795349 603325011218785992018641)
                ·
                  refine ⟨452493758414089494013981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603325011218785992018641 452493758414089494013981)
                  ·
                    refine ⟨169685159405283560255243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452493758414089494013981 169685159405283560255243)
                    ·
                      rfl

theorem cell22_495691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].length) (baseStart_495691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495691 prefixEnd_495691 := by exact prefixLift 495691
  have htrace : WordTrace (prefixWord ++ tailWord_495691) baseStart_495691 baseEnd_495691 := by
    simpa [prefixWord, tailWord_495691, baseEnd_495691] using wordTrace_append hprefix tailTrace_495691
  have hstable : (prefixWord ++ tailWord_495691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495691).length < 2 ^ (prefixWord ++ tailWord_495691).sum := by decide
  have hdescent : baseEnd_495691 < baseStart_495691 := by decide
  rcases family_descends (prefixWord ++ tailWord_495691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495704 : List Nat := [2, 1, 2, 2, 1, 4, 2, 8]
def baseStart_495704 : Nat := 118140960795 + 495704 * 2 ^ 59
def prefixEnd_495704 : Nat := 4983230072969 + 3 ^ 40 * 495704 * 2
def baseEnd_495704 : Nat := 18854401063439539964467

theorem tailTrace_495704 : CollatzResearch.WordTrace tailWord_495704 prefixEnd_495704 18854401063439539964467 := by
  unfold tailWord_495704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039905098078271174111083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12053206797437694898814777 9039905098078271174111083)
  ·
    refine ⟨13559857647117406761166625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039905098078271174111083 13559857647117406761166625)
    ·
      refine ⟨10169893235338055070874969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13559857647117406761166625 10169893235338055070874969)
      ·
        refine ⟨7627419926503541303156227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10169893235338055070874969 7627419926503541303156227)
        ·
          refine ⟨11441129889755311954734341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627419926503541303156227 11441129889755311954734341)
          ·
            refine ⟨2145211854329120991512689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11441129889755311954734341 2145211854329120991512689)
            ·
              refine ⟨1608908890746840743634517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145211854329120991512689 1608908890746840743634517)
              ·
                refine ⟨18854401063439539964467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1608908890746840743634517 18854401063439539964467)
                ·
                  rfl

theorem cell22_495704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_495704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495704 prefixEnd_495704 := by exact prefixLift 495704
  have htrace : WordTrace (prefixWord ++ tailWord_495704) baseStart_495704 baseEnd_495704 := by
    simpa [prefixWord, tailWord_495704, baseEnd_495704] using wordTrace_append hprefix tailTrace_495704
  have hstable : (prefixWord ++ tailWord_495704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495704).length < 2 ^ (prefixWord ++ tailWord_495704).sum := by decide
  have hdescent : baseEnd_495704 < baseStart_495704 := by decide
  rcases family_descends (prefixWord ++ tailWord_495704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495706 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_495706 : Nat := 118140960795 + 495706 * 2 ^ 59
def prefixEnd_495706 : Nat := 4983230072969 + 3 ^ 40 * 495706 * 2
def baseEnd_495706 : Nat := 169690294211828521130197

theorem tailTrace_495706 : CollatzResearch.WordTrace tailWord_495706 prefixEnd_495706 169690294211828521130197 := by
  unfold tailWord_495706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519970785537324172448743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12053255428099531126529981 4519970785537324172448743)
  ·
    refine ⟨6779956178305986258673115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4519970785537324172448743 6779956178305986258673115)
    ·
      refine ⟨10169934267458979388009673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6779956178305986258673115 10169934267458979388009673)
      ·
        refine ⟨7627450700594234541007255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10169934267458979388009673 7627450700594234541007255)
        ·
          refine ⟨11441176050891351811510883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627450700594234541007255 11441176050891351811510883)
          ·
            refine ⟨17161764076337027717266325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11441176050891351811510883 17161764076337027717266325)
            ·
              refine ⟨804457691078298174246859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17161764076337027717266325 804457691078298174246859)
              ·
                refine ⟨1206686536617447261370289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804457691078298174246859 1206686536617447261370289)
                ·
                  refine ⟨905014902463085446027717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206686536617447261370289 905014902463085446027717)
                  ·
                    refine ⟨169690294211828521130197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 905014902463085446027717 169690294211828521130197)
                    ·
                      rfl

theorem cell22_495706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_495706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495706 prefixEnd_495706 := by exact prefixLift 495706
  have htrace : WordTrace (prefixWord ++ tailWord_495706) baseStart_495706 baseEnd_495706 := by
    simpa [prefixWord, tailWord_495706, baseEnd_495706] using wordTrace_append hprefix tailTrace_495706
  have hstable : (prefixWord ++ tailWord_495706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495706).length < 2 ^ (prefixWord ++ tailWord_495706).sum := by decide
  have hdescent : baseEnd_495706 < baseStart_495706 := by decide
  rcases family_descends (prefixWord ++ tailWord_495706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495736 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_495736 : Nat := 118140960795 + 495736 * 2 ^ 59
def prefixEnd_495736 : Nat := 4983230072969 + 3 ^ 40 * 495736 * 2
def baseEnd_495736 : Nat := 169700563824918442880105

theorem tailTrace_495736 : CollatzResearch.WordTrace tailWord_495736 prefixEnd_495736 169700563824918442880105 := by
  unfold tailWord_495736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040488666020305906693531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12053984888027074542258041 9040488666020305906693531)
  ·
    refine ⟨13560732999030458860040297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9040488666020305906693531 13560732999030458860040297)
    ·
      refine ⟨10170549749272844145030223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13560732999030458860040297 10170549749272844145030223)
      ·
        refine ⟨15255824623909266217545335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170549749272844145030223 15255824623909266217545335)
        ·
          refine ⟨22883736935863899326318003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15255824623909266217545335 22883736935863899326318003)
          ·
            refine ⟨34325605403795848989477005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883736935863899326318003 34325605403795848989477005)
            ·
              refine ⟨12872102026423443371053877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34325605403795848989477005 12872102026423443371053877)
              ·
                refine ⟨1206759564977197816036301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12872102026423443371053877 1206759564977197816036301)
                ·
                  refine ⟨452534836866449181013613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206759564977197816036301 452534836866449181013613)
                  ·
                    refine ⟨169700563824918442880105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452534836866449181013613 169700563824918442880105)
                    ·
                      rfl

theorem cell22_495736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_495736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495736 prefixEnd_495736 := by exact prefixLift 495736
  have htrace : WordTrace (prefixWord ++ tailWord_495736) baseStart_495736 baseEnd_495736 := by
    simpa [prefixWord, tailWord_495736, baseEnd_495736] using wordTrace_append hprefix tailTrace_495736
  have hstable : (prefixWord ++ tailWord_495736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495736).length < 2 ^ (prefixWord ++ tailWord_495736).sum := by decide
  have hdescent : baseEnd_495736 < baseStart_495736 := by decide
  rcases family_descends (prefixWord ++ tailWord_495736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495783 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 7]
def baseStart_495783 : Nat := 118140960795 + 495783 * 2 ^ 59
def prefixEnd_495783 : Nat := 4983230072969 + 3 ^ 40 * 495783 * 2
def baseEnd_495783 : Nat := 56572217628475328984987

theorem tailTrace_495783 : CollatzResearch.WordTrace tailWord_495783 prefixEnd_495783 56572217628475328984987 := by
  unfold tailWord_495783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082691562870338840348003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12055127708580225893565335 18082691562870338840348003)
  ·
    refine ⟨27124037344305508260522005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18082691562870338840348003 27124037344305508260522005)
    ·
      refine ⟨1271439250514320699711969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27124037344305508260522005 1271439250514320699711969)
      ·
        refine ⟨953579437885740524783977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271439250514320699711969 953579437885740524783977)
        ·
          refine ⟨715184578414305393587983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953579437885740524783977 715184578414305393587983)
          ·
            refine ⟨1072776867621458090381975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715184578414305393587983 1072776867621458090381975)
            ·
              refine ⟨1609165301432187135572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072776867621458090381975 1609165301432187135572963)
              ·
                refine ⟨2413747952148280703359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609165301432187135572963 2413747952148280703359445)
                ·
                  refine ⟨56572217628475328984987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2413747952148280703359445 56572217628475328984987)
                  ·
                    rfl

theorem cell22_495783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_495783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495783 prefixEnd_495783 := by exact prefixLift 495783
  have htrace : WordTrace (prefixWord ++ tailWord_495783) baseStart_495783 baseEnd_495783 := by
    simpa [prefixWord, tailWord_495783, baseEnd_495783] using wordTrace_append hprefix tailTrace_495783
  have hstable : (prefixWord ++ tailWord_495783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495783).length < 2 ^ (prefixWord ++ tailWord_495783).sum := by decide
  have hdescent : baseEnd_495783 < baseStart_495783 := by decide
  rcases family_descends (prefixWord ++ tailWord_495783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495916 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_495916 : Nat := 118140960795 + 495916 * 2 ^ 59
def prefixEnd_495916 : Nat := 4983230072969 + 3 ^ 40 * 495916 * 2
def baseEnd_495916 : Nat := 169762181503457973379553

theorem tailTrace_495916 : CollatzResearch.WordTrace tailWord_495916 prefixEnd_495916 169762181503457973379553 := by
  unfold tailWord_495916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043771235694251277469801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12058361647592335036626401 9043771235694251277469801)
  ·
    refine ⟨6782828426770688458102351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9043771235694251277469801 6782828426770688458102351)
    ·
      refine ⟨10174242640156032687153527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782828426770688458102351 10174242640156032687153527)
      ·
        refine ⟨15261363960234049030730291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174242640156032687153527 15261363960234049030730291)
        ·
          refine ⟨22892045940351073546095437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261363960234049030730291 22892045940351073546095437)
          ·
            refine ⟨8584517227631652579785789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22892045940351073546095437 8584517227631652579785789)
            ·
              refine ⟨3219193960361869717419671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8584517227631652579785789 3219193960361869717419671)
              ·
                refine ⟨4828790940542804576129507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219193960361869717419671 4828790940542804576129507)
                ·
                  refine ⟨7243186410814206864194261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828790940542804576129507 7243186410814206864194261)
                  ·
                    refine ⟨169762181503457973379553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7243186410814206864194261 169762181503457973379553)
                    ·
                      rfl

theorem cell22_495916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_495916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495916 prefixEnd_495916 := by exact prefixLift 495916
  have htrace : WordTrace (prefixWord ++ tailWord_495916) baseStart_495916 baseEnd_495916 := by
    simpa [prefixWord, tailWord_495916, baseEnd_495916] using wordTrace_append hprefix tailTrace_495916
  have hstable : (prefixWord ++ tailWord_495916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495916).length < 2 ^ (prefixWord ++ tailWord_495916).sum := by decide
  have hdescent : baseEnd_495916 < baseStart_495916 := by decide
  rcases family_descends (prefixWord ++ tailWord_495916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495993 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_495993 : Nat := 118140960795 + 495993 * 2 ^ 59
def prefixEnd_495993 : Nat := 4983230072969 + 3 ^ 40 * 495993 * 2
def baseEnd_495993 : Nat := 169788540177055439204317

theorem tailTrace_495993 : CollatzResearch.WordTrace tailWord_495993 prefixEnd_495993 169788540177055439204317 := by
  unfold tailWord_495993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090350892109544705492633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12060233928073029803661755 18090350892109544705492633)
  ·
    refine ⟨13567763169082158529119475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18090350892109544705492633 13567763169082158529119475)
    ·
      refine ⟨20351644753623237793679213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567763169082158529119475 20351644753623237793679213)
      ·
        refine ⟨7631866782608714172629705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20351644753623237793679213 7631866782608714172629705)
        ·
          refine ⟨5723900086956535629472279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631866782608714172629705 5723900086956535629472279)
          ·
            refine ⟨8585850130434803444208419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723900086956535629472279 8585850130434803444208419)
            ·
              refine ⟨12878775195652205166312629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585850130434803444208419 12878775195652205166312629)
              ·
                refine ⟨1207385174592394234341809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12878775195652205166312629 1207385174592394234341809)
                ·
                  refine ⟨905538880944295675756357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207385174592394234341809 905538880944295675756357)
                  ·
                    refine ⟨169788540177055439204317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 905538880944295675756357 169788540177055439204317)
                    ·
                      rfl

theorem cell22_495993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_495993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495993 prefixEnd_495993 := by exact prefixLift 495993
  have htrace : WordTrace (prefixWord ++ tailWord_495993) baseStart_495993 baseEnd_495993 := by
    simpa [prefixWord, tailWord_495993, baseEnd_495993] using wordTrace_append hprefix tailTrace_495993
  have hstable : (prefixWord ++ tailWord_495993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495993).length < 2 ^ (prefixWord ++ tailWord_495993).sum := by decide
  have hdescent : baseEnd_495993 < baseStart_495993 := by decide
  rcases family_descends (prefixWord ++ tailWord_495993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495997 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 4]
def baseStart_495997 : Nat := 118140960795 + 495997 * 2 ^ 59
def prefixEnd_495997 : Nat := 4983230072969 + 3 ^ 40 * 495997 * 2
def baseEnd_495997 : Nat := 56596636486266920701435

theorem tailTrace_495997 : CollatzResearch.WordTrace tailWord_495997 prefixEnd_495997 56596636486266920701435 := by
  unfold tailWord_495997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090496784095053388638245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12060331189396702259092163 18090496784095053388638245)
  ·
    refine ⟨3391968147017822510369671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18090496784095053388638245 3391968147017822510369671)
    ·
      refine ⟨5087952220526733765554507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391968147017822510369671 5087952220526733765554507)
      ·
        refine ⟨7631928330790100648331761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087952220526733765554507 7631928330790100648331761)
        ·
          refine ⟨5723946248092575486248821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631928330790100648331761 5723946248092575486248821)
          ·
            refine ⟨536619960758678951835827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5723946248092575486248821 536619960758678951835827)
            ·
              refine ⟨804929941138018427753741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536619960758678951835827 804929941138018427753741)
              ·
                refine ⟨301848727926756910407653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804929941138018427753741 301848727926756910407653)
                ·
                  refine ⟨56596636486266920701435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301848727926756910407653 56596636486266920701435)
                  ·
                    rfl

theorem cell22_495997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_495997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_495997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_495997 prefixEnd_495997 := by exact prefixLift 495997
  have htrace : WordTrace (prefixWord ++ tailWord_495997) baseStart_495997 baseEnd_495997 := by
    simpa [prefixWord, tailWord_495997, baseEnd_495997] using wordTrace_append hprefix tailTrace_495997
  have hstable : (prefixWord ++ tailWord_495997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495997).length < 2 ^ (prefixWord ++ tailWord_495997).sum := by decide
  have hdescent : baseEnd_495997 < baseStart_495997 := by decide
  rcases family_descends (prefixWord ++ tailWord_495997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496014 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_496014 : Nat := 118140960795 + 496014 * 2 ^ 59
def prefixEnd_496014 : Nat := 4983230072969 + 3 ^ 40 * 496014 * 2
def baseEnd_496014 : Nat := 56598576302072794809751

theorem tailTrace_496014 : CollatzResearch.WordTrace tailWord_496014 prefixEnd_496014 56598576302072794809751 := by
  unfold tailWord_496014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261389603129183161500887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12060744550022310194671397 2261389603129183161500887)
  ·
    refine ⟨3392084404693774742251331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261389603129183161500887 3392084404693774742251331)
    ·
      refine ⟨5088126607040662113376997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392084404693774742251331 5088126607040662113376997)
      ·
        refine ⟨954023738820124146258187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5088126607040662113376997 954023738820124146258187)
        ·
          refine ⟨1431035608230186219387281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954023738820124146258187 1431035608230186219387281)
          ·
            refine ⟨1073276706172639664540461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431035608230186219387281 1073276706172639664540461)
            ·
              refine ⟨402478764814739874202673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073276706172639664540461 402478764814739874202673)
              ·
                refine ⟨301859073611054905652005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402478764814739874202673 301859073611054905652005)
                ·
                  refine ⟨56598576302072794809751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301859073611054905652005 56598576302072794809751)
                  ·
                    rfl

theorem cell22_496014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_496014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496014 prefixEnd_496014 := by exact prefixLift 496014
  have htrace : WordTrace (prefixWord ++ tailWord_496014) baseStart_496014 baseEnd_496014 := by
    simpa [prefixWord, tailWord_496014, baseEnd_496014] using wordTrace_append hprefix tailTrace_496014
  have hstable : (prefixWord ++ tailWord_496014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496014).length < 2 ^ (prefixWord ++ tailWord_496014).sum := by decide
  have hdescent : baseEnd_496014 < baseStart_496014 := by decide
  rcases family_descends (prefixWord ++ tailWord_496014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496065 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 4]
def baseStart_496065 : Nat := 118140960795 + 496065 * 2 ^ 59
def prefixEnd_496065 : Nat := 4983230072969 + 3 ^ 40 * 496065 * 2
def baseEnd_496065 : Nat := 56604395749490417134699

theorem tailTrace_496065 : CollatzResearch.WordTrace tailWord_496065 prefixEnd_496065 56604395749490417134699 := by
  unfold tailWord_496065
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092976947848701002113649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12061984631899134001409099 18092976947848701002113649)
  ·
    refine ⟨13569732710886525751585237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18092976947848701002113649 13569732710886525751585237)
    ·
      refine ⟨318040610411402947302779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13569732710886525751585237 318040610411402947302779)
      ·
        refine ⟨477060915617104420954169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318040610411402947302779 477060915617104420954169)
        ·
          refine ⟨357795686712828315715627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477060915617104420954169 357795686712828315715627)
          ·
            refine ⟨536693530069242473573441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357795686712828315715627 536693530069242473573441)
            ·
              refine ⟨402520147551931855180081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536693530069242473573441 402520147551931855180081)
              ·
                refine ⟨301890110663948891385061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402520147551931855180081 301890110663948891385061)
                ·
                  refine ⟨56604395749490417134699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301890110663948891385061 56604395749490417134699)
                  ·
                    rfl

theorem cell22_496065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_496065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496065 prefixEnd_496065 := by exact prefixLift 496065
  have htrace : WordTrace (prefixWord ++ tailWord_496065) baseStart_496065 baseEnd_496065 := by
    simpa [prefixWord, tailWord_496065, baseEnd_496065] using wordTrace_append hprefix tailTrace_496065
  have hstable : (prefixWord ++ tailWord_496065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496065).length < 2 ^ (prefixWord ++ tailWord_496065).sum := by decide
  have hdescent : baseEnd_496065 < baseStart_496065 := by decide
  rcases family_descends (prefixWord ++ tailWord_496065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496085 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_496085 : Nat := 118140960795 + 496085 * 2 ^ 59
def prefixEnd_496085 : Nat := 4983230072969 + 3 ^ 40 * 496085 * 2
def baseEnd_496085 : Nat := 169820033657197865904035

theorem tailTrace_496085 : CollatzResearch.WordTrace tailWord_496085 prefixEnd_496085 169820033657197865904035 := by
  unfold tailWord_496085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093706407776244417841709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12062470938517496278561139 18093706407776244417841709)
  ·
    refine ⟨6785139902916091656690641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18093706407776244417841709 6785139902916091656690641)
    ·
      refine ⟨5088854927187068742517981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6785139902916091656690641 5088854927187068742517981)
      ·
        refine ⟨1908320597695150778444243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5088854927187068742517981 1908320597695150778444243)
        ·
          refine ⟨2862480896542726167666365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908320597695150778444243 2862480896542726167666365)
          ·
            refine ⟨1073430336203522312874887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2862480896542726167666365 1073430336203522312874887)
            ·
              refine ⟨1610145504305283469312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073430336203522312874887 1610145504305283469312331)
              ·
                refine ⟨2415218256457925203968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610145504305283469312331 2415218256457925203968497)
                ·
                  refine ⟨1811413692343443902976373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415218256457925203968497 1811413692343443902976373)
                  ·
                    refine ⟨169820033657197865904035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1811413692343443902976373 169820033657197865904035)
                    ·
                      rfl

theorem cell22_496085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_496085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496085 prefixEnd_496085 := by exact prefixLift 496085
  have htrace : WordTrace (prefixWord ++ tailWord_496085) baseStart_496085 baseEnd_496085 := by
    simpa [prefixWord, tailWord_496085, baseEnd_496085] using wordTrace_append hprefix tailTrace_496085
  have hstable : (prefixWord ++ tailWord_496085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496085).length < 2 ^ (prefixWord ++ tailWord_496085).sum := by decide
  have hdescent : baseEnd_496085 < baseStart_496085 := by decide
  rcases family_descends (prefixWord ++ tailWord_496085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496132 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_496132 : Nat := 118140960795 + 496132 * 2 ^ 59
def prefixEnd_496132 : Nat := 4983230072969 + 3 ^ 40 * 496132 * 2
def baseEnd_496132 : Nat := 56612040905901803326297

theorem tailTrace_496132 : CollatzResearch.WordTrace tailWord_496132 prefixEnd_496132 56612040905901803326297 := by
  unfold tailWord_496132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047710319302985722401325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12063613759070647629868433 9047710319302985722401325)
  ·
    refine ⟨3392891369738619645900497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9047710319302985722401325 3392891369738619645900497)
    ·
      refine ⟨2544668527303964734425373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3392891369738619645900497 2544668527303964734425373)
      ·
        refine ⟨954250697738986775409515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2544668527303964734425373 954250697738986775409515)
        ·
          refine ⟨1431376046608480163114273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954250697738986775409515 1431376046608480163114273)
          ·
            refine ⟨1073532034956360122335705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431376046608480163114273 1073532034956360122335705)
            ·
              refine ⟨805149026217270091751779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073532034956360122335705 805149026217270091751779)
              ·
                refine ⟨1207723539325905137627669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805149026217270091751779 1207723539325905137627669)
                ·
                  refine ⟨56612040905901803326297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1207723539325905137627669 56612040905901803326297)
                  ·
                    rfl

theorem cell22_496132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_496132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496132 prefixEnd_496132 := by exact prefixLift 496132
  have htrace : WordTrace (prefixWord ++ tailWord_496132) baseStart_496132 baseEnd_496132 := by
    simpa [prefixWord, tailWord_496132, baseEnd_496132] using wordTrace_append hprefix tailTrace_496132
  have hstable : (prefixWord ++ tailWord_496132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496132).length < 2 ^ (prefixWord ++ tailWord_496132).sum := by decide
  have hdescent : baseEnd_496132 < baseStart_496132 := by decide
  rcases family_descends (prefixWord ++ tailWord_496132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496192 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_496192 : Nat := 118140960795 + 496192 * 2 ^ 59
def prefixEnd_496192 : Nat := 4983230072969 + 3 ^ 40 * 496192 * 2
def baseEnd_496192 : Nat := 169856661943885253478707

theorem tailTrace_496192 : CollatzResearch.WordTrace tailWord_496192 prefixEnd_496192 169856661943885253478707 := by
  unfold tailWord_496192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048804509194300845993415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12065072678925734461324553 9048804509194300845993415)
  ·
    refine ⟨13573206763791451268990123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048804509194300845993415 13573206763791451268990123)
    ·
      refine ⟨20359810145687176903485185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573206763791451268990123 20359810145687176903485185)
      ·
        refine ⟨15269857609265382677613889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20359810145687176903485185 15269857609265382677613889)
        ·
          refine ⟨11452393206949037008210417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15269857609265382677613889 11452393206949037008210417)
          ·
            refine ⟨8589294905211777756157813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452393206949037008210417 8589294905211777756157813)
            ·
              refine ⟨805246397363604164639795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8589294905211777756157813 805246397363604164639795)
              ·
                refine ⟨1207869596045406246959693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805246397363604164639795 1207869596045406246959693)
                ·
                  refine ⟨452951098517027342609885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207869596045406246959693 452951098517027342609885)
                  ·
                    refine ⟨169856661943885253478707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452951098517027342609885 169856661943885253478707)
                    ·
                      rfl

theorem cell22_496192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_496192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496192 prefixEnd_496192 := by exact prefixLift 496192
  have htrace : WordTrace (prefixWord ++ tailWord_496192) baseStart_496192 baseEnd_496192 := by
    simpa [prefixWord, tailWord_496192, baseEnd_496192] using wordTrace_append hprefix tailTrace_496192
  have hstable : (prefixWord ++ tailWord_496192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496192).length < 2 ^ (prefixWord ++ tailWord_496192).sum := by decide
  have hdescent : baseEnd_496192 < baseStart_496192 := by decide
  rcases family_descends (prefixWord ++ tailWord_496192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496198 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_496198 : Nat := 118140960795 + 496198 * 2 ^ 59
def prefixEnd_496198 : Nat := 4983230072969 + 3 ^ 40 * 496198 * 2
def baseEnd_496198 : Nat := 169858715866503237828689

theorem tailTrace_496198 : CollatzResearch.WordTrace tailWord_496198 prefixEnd_496198 169858715866503237828689 := by
  unfold tailWord_496198
  simp only [CollatzResearch.WordTrace]
  refine ⟨565557120511464522397039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12065218570911243144470165 565557120511464522397039)
  ·
    refine ⟨848335680767196783595559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565557120511464522397039 848335680767196783595559)
    ·
      refine ⟨1272503521150795175393339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848335680767196783595559 1272503521150795175393339)
      ·
        refine ⟨1908755281726192763090009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272503521150795175393339 1908755281726192763090009)
        ·
          refine ⟨1431566461294644572317507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908755281726192763090009 1431566461294644572317507)
          ·
            refine ⟨2147349691941966858476261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431566461294644572317507 2147349691941966858476261)
            ·
              refine ⟨402628067239118785964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2147349691941966858476261 402628067239118785964299)
              ·
                refine ⟨603942100858678178946449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402628067239118785964299 603942100858678178946449)
                ·
                  refine ⟨452956575644008634209837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603942100858678178946449 452956575644008634209837)
                  ·
                    refine ⟨169858715866503237828689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452956575644008634209837 169858715866503237828689)
                    ·
                      rfl

theorem cell22_496198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_496198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496198 prefixEnd_496198 := by exact prefixLift 496198
  have htrace : WordTrace (prefixWord ++ tailWord_496198) baseStart_496198 baseEnd_496198 := by
    simpa [prefixWord, tailWord_496198, baseEnd_496198] using wordTrace_append hprefix tailTrace_496198
  have hstable : (prefixWord ++ tailWord_496198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496198).length < 2 ^ (prefixWord ++ tailWord_496198).sum := by decide
  have hdescent : baseEnd_496198 < baseStart_496198 := by decide
  rcases family_descends (prefixWord ++ tailWord_496198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496284 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_496284 : Nat := 118140960795 + 496284 * 2 ^ 59
def prefixEnd_496284 : Nat := 4983230072969 + 3 ^ 40 * 496284 * 2
def baseEnd_496284 : Nat := 56629385141342560059475

theorem tailTrace_496284 : CollatzResearch.WordTrace tailWord_496284 prefixEnd_496284 56629385141342560059475 := by
  unfold tailWord_496284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050482267027650702167953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12067309689370200936223937 9050482267027650702167953)
  ·
    refine ⟨6787861700270738026625965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9050482267027650702167953 6787861700270738026625965)
    ·
      refine ⟨2545448137601526759984737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6787861700270738026625965 2545448137601526759984737)
      ·
        refine ⟨1909086103201145069988553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545448137601526759984737 1909086103201145069988553)
        ·
          refine ⟨1431814577400858802491415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909086103201145069988553 1431814577400858802491415)
          ·
            refine ⟨2147721866101288203737123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431814577400858802491415 2147721866101288203737123)
            ·
              refine ⟨3221582799151932305605685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147721866101288203737123 3221582799151932305605685)
              ·
                refine ⟨302023387420493653650533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3221582799151932305605685 302023387420493653650533)
                ·
                  refine ⟨56629385141342560059475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302023387420493653650533 56629385141342560059475)
                  ·
                    rfl

theorem cell22_496284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_496284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496284 prefixEnd_496284 := by exact prefixLift 496284
  have htrace : WordTrace (prefixWord ++ tailWord_496284) baseStart_496284 baseEnd_496284 := by
    simpa [prefixWord, tailWord_496284, baseEnd_496284] using wordTrace_append hprefix tailTrace_496284
  have hstable : (prefixWord ++ tailWord_496284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496284).length < 2 ^ (prefixWord ++ tailWord_496284).sum := by decide
  have hdescent : baseEnd_496284 < baseStart_496284 := by decide
  rcases family_descends (prefixWord ++ tailWord_496284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496316 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_496316 : Nat := 118140960795 + 496316 * 2 ^ 59
def prefixEnd_496316 : Nat := 4983230072969 + 3 ^ 40 * 496316 * 2
def baseEnd_496316 : Nat := 169899109677990263378327

theorem tailTrace_496316 : CollatzResearch.WordTrace tailWord_496316 prefixEnd_496316 169899109677990263378327 := by
  unfold tailWord_496316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051065834969685434750401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12068087779959580579667201 9051065834969685434750401)
  ·
    refine ⟨6788299376227264076062801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9051065834969685434750401 6788299376227264076062801)
    ·
      refine ⟨5091224532170448057047101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6788299376227264076062801 5091224532170448057047101)
      ·
        refine ⟨1909209199563918021392663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5091224532170448057047101 1909209199563918021392663)
        ·
          refine ⟨2863813799345877032088995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909209199563918021392663 2863813799345877032088995)
          ·
            refine ⟨4295720699018815548133493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863813799345877032088995 4295720699018815548133493)
            ·
              refine ⟨402723815533013957637515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4295720699018815548133493 402723815533013957637515)
              ·
                refine ⟨604085723299520936456273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402723815533013957637515 604085723299520936456273)
                ·
                  refine ⟨453064292474640702342205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604085723299520936456273 453064292474640702342205)
                  ·
                    refine ⟨169899109677990263378327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453064292474640702342205 169899109677990263378327)
                    ·
                      rfl

theorem cell22_496316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_496316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496316 prefixEnd_496316 := by exact prefixLift 496316
  have htrace : WordTrace (prefixWord ++ tailWord_496316) baseStart_496316 baseEnd_496316 := by
    simpa [prefixWord, tailWord_496316, baseEnd_496316] using wordTrace_append hprefix tailTrace_496316
  have hstable : (prefixWord ++ tailWord_496316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496316).length < 2 ^ (prefixWord ++ tailWord_496316).sum := by decide
  have hdescent : baseEnd_496316 < baseStart_496316 := by decide
  rcases family_descends (prefixWord ++ tailWord_496316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496327 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 5, 3]
def baseStart_496327 : Nat := 118140960795 + 496327 * 2 ^ 59
def prefixEnd_496327 : Nat := 4983230072969 + 3 ^ 40 * 496327 * 2
def baseEnd_496327 : Nat := 169902875202789901353293

theorem tailTrace_496327 : CollatzResearch.WordTrace tailWord_496327 prefixEnd_496327 169902875202789901353293 := by
  unfold tailWord_496327
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102532872899519748151235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12068355248599679832100823 18102532872899519748151235)
  ·
    refine ⟨27153799309349279622226853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18102532872899519748151235 27153799309349279622226853)
    ·
      refine ⟨5091337370502989929167535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27153799309349279622226853 5091337370502989929167535)
      ·
        refine ⟨7637006055754484893751303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091337370502989929167535 7637006055754484893751303)
        ·
          refine ⟨11455509083631727340626955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637006055754484893751303 11455509083631727340626955)
          ·
            refine ⟨17183263625447591010940433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455509083631727340626955 17183263625447591010940433)
            ·
              refine ⟨12887447719085693258205325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183263625447591010940433 12887447719085693258205325)
              ·
                refine ⟨4832792894657134971826997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12887447719085693258205325 4832792894657134971826997)
                ·
                  refine ⟨453074333874106403608781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832792894657134971826997 453074333874106403608781)
                  ·
                    refine ⟨169902875202789901353293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453074333874106403608781 169902875202789901353293)
                    ·
                      rfl

theorem cell22_496327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_496327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496327 prefixEnd_496327 := by exact prefixLift 496327
  have htrace : WordTrace (prefixWord ++ tailWord_496327) baseStart_496327 baseEnd_496327 := by
    simpa [prefixWord, tailWord_496327, baseEnd_496327] using wordTrace_append hprefix tailTrace_496327
  have hstable : (prefixWord ++ tailWord_496327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496327).length < 2 ^ (prefixWord ++ tailWord_496327).sum := by decide
  have hdescent : baseEnd_496327 < baseStart_496327 := by decide
  rcases family_descends (prefixWord ++ tailWord_496327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496357 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 7]
def baseStart_496357 : Nat := 118140960795 + 496357 * 2 ^ 59
def prefixEnd_496357 : Nat := 4983230072969 + 3 ^ 40 * 496357 * 2
def baseEnd_496357 : Nat := 56637714938626607701067

theorem tailTrace_496357 : CollatzResearch.WordTrace tailWord_496357 prefixEnd_496357 56637714938626607701067 := by
  unfold tailWord_496357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103627062790834871743325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12069084708527223247828883 18103627062790834871743325)
  ·
    refine ⟨6788860148546563076903747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18103627062790834871743325 6788860148546563076903747)
    ·
      refine ⟨10183290222819844615355621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6788860148546563076903747 10183290222819844615355621)
      ·
        refine ⟨1909366916778720865379179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10183290222819844615355621 1909366916778720865379179)
        ·
          refine ⟨2864050375168081298068769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909366916778720865379179 2864050375168081298068769)
          ·
            refine ⟨2148037781376060973551577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864050375168081298068769 2148037781376060973551577)
            ·
              refine ⟨1611028336032045730163683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148037781376060973551577 1611028336032045730163683)
              ·
                refine ⟨2416542504048068595245525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611028336032045730163683 2416542504048068595245525)
                ·
                  refine ⟨56637714938626607701067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2416542504048068595245525 56637714938626607701067)
                  ·
                    rfl

theorem cell22_496357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_496357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496357 prefixEnd_496357 := by exact prefixLift 496357
  have htrace : WordTrace (prefixWord ++ tailWord_496357) baseStart_496357 baseEnd_496357 := by
    simpa [prefixWord, tailWord_496357, baseEnd_496357] using wordTrace_append hprefix tailTrace_496357
  have hstable : (prefixWord ++ tailWord_496357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496357).length < 2 ^ (prefixWord ++ tailWord_496357).sum := by decide
  have hdescent : baseEnd_496357 < baseStart_496357 := by decide
  rcases family_descends (prefixWord ++ tailWord_496357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496374 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_496374 : Nat := 118140960795 + 496374 * 2 ^ 59
def prefixEnd_496374 : Nat := 4983230072969 + 3 ^ 40 * 496374 * 2
def baseEnd_496374 : Nat := 56639654754432481809383

theorem tailTrace_496374 : CollatzResearch.WordTrace tailWord_496374 prefixEnd_496374 56639654754432481809383 := by
  unfold tailWord_496374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131515443983077923444511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12069498069152831183408117 1131515443983077923444511)
  ·
    refine ⟨1697273165974616885166767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131515443983077923444511 1697273165974616885166767)
    ·
      refine ⟨2545909748961925327750151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697273165974616885166767 2545909748961925327750151)
      ·
        refine ⟨3818864623442887991625227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545909748961925327750151 3818864623442887991625227)
        ·
          refine ⟨5728296935164331987437841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818864623442887991625227 5728296935164331987437841)
          ·
            refine ⟨4296222701373248990578381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728296935164331987437841 4296222701373248990578381)
            ·
              refine ⟨1611083513014968371466893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4296222701373248990578381 1611083513014968371466893)
              ·
                refine ⟨604156317380613139300085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1611083513014968371466893 604156317380613139300085)
                ·
                  refine ⟨56639654754432481809383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604156317380613139300085 56639654754432481809383)
                  ·
                    rfl

theorem cell22_496374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_496374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496374 prefixEnd_496374 := by exact prefixLift 496374
  have htrace : WordTrace (prefixWord ++ tailWord_496374) baseStart_496374 baseEnd_496374 := by
    simpa [prefixWord, tailWord_496374, baseEnd_496374] using wordTrace_append hprefix tailTrace_496374
  have hstable : (prefixWord ++ tailWord_496374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496374).length < 2 ^ (prefixWord ++ tailWord_496374).sum := by decide
  have hdescent : baseEnd_496374 < baseStart_496374 := by decide
  rcases family_descends (prefixWord ++ tailWord_496374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496417 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_496417 : Nat := 118140960795 + 496417 * 2 ^ 59
def prefixEnd_496417 : Nat := 4983230072969 + 3 ^ 40 * 496417 * 2
def baseEnd_496417 : Nat := 169933684042059666603017

theorem tailTrace_496417 : CollatzResearch.WordTrace tailWord_496417 prefixEnd_496417 169933684042059666603017 := by
  unfold tailWord_496417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105815442573465118927505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12070543628382310079285003 18105815442573465118927505)
  ·
    refine ⟨13579361581930098839195629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18105815442573465118927505 13579361581930098839195629)
    ·
      refine ⟨5092260593223787064698361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13579361581930098839195629 5092260593223787064698361)
      ·
        refine ⟨3819195444917840298523771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092260593223787064698361 3819195444917840298523771)
        ·
          refine ⟨5728793167376760447785657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819195444917840298523771 5728793167376760447785657)
          ·
            refine ⟨4296594875532570335839243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728793167376760447785657 4296594875532570335839243)
            ·
              refine ⟨6444892313298855503758865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296594875532570335839243 6444892313298855503758865)
              ·
                refine ⟨4833669234974141627819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444892313298855503758865 4833669234974141627819149)
                ·
                  refine ⟨1812625963115303110432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4833669234974141627819149 1812625963115303110432181)
                  ·
                    refine ⟨169933684042059666603017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1812625963115303110432181 169933684042059666603017)
                    ·
                      rfl

theorem cell22_496417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_496417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496417 prefixEnd_496417 := by exact prefixLift 496417
  have htrace : WordTrace (prefixWord ++ tailWord_496417) baseStart_496417 baseEnd_496417 := by
    simpa [prefixWord, tailWord_496417, baseEnd_496417] using wordTrace_append hprefix tailTrace_496417
  have hstable : (prefixWord ++ tailWord_496417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496417).length < 2 ^ (prefixWord ++ tailWord_496417).sum := by decide
  have hdescent : baseEnd_496417 < baseStart_496417 := by decide
  rcases family_descends (prefixWord ++ tailWord_496417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_496432 : Nat := 118140960795 + 496432 * 2 ^ 59
def prefixEnd_496432 : Nat := 4983230072969 + 3 ^ 40 * 496432 * 2
def baseEnd_496432 : Nat := 169938818848604627477971

theorem tailTrace_496432 : CollatzResearch.WordTrace tailWord_496432 prefixEnd_496432 169938818848604627477971 := by
  unfold tailWord_496432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053181268759561340361775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12070908358346081787149033 9053181268759561340361775)
  ·
    refine ⟨13579771903139342010542663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053181268759561340361775 13579771903139342010542663)
    ·
      refine ⟨20369657854709013015813995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579771903139342010542663 20369657854709013015813995)
      ·
        refine ⟨30554486782063519523720993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369657854709013015813995 30554486782063519523720993)
        ·
          refine ⟨22915865086547639642790745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30554486782063519523720993 22915865086547639642790745)
          ·
            refine ⟨17186898814910729732093059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22915865086547639642790745 17186898814910729732093059)
            ·
              refine ⟨25780348222366094598139589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17186898814910729732093059 25780348222366094598139589)
              ·
                refine ⟨4833815291693642737151173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25780348222366094598139589 4833815291693642737151173)
                ·
                  refine ⟨906340367192558013215845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4833815291693642737151173 906340367192558013215845)
                  ·
                    refine ⟨169938818848604627477971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906340367192558013215845 169938818848604627477971)
                    ·
                      rfl

theorem cell22_496432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_496432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496432 prefixEnd_496432 := by exact prefixLift 496432
  have htrace : WordTrace (prefixWord ++ tailWord_496432) baseStart_496432 baseEnd_496432 := by
    simpa [prefixWord, tailWord_496432, baseEnd_496432] using wordTrace_append hprefix tailTrace_496432
  have hstable : (prefixWord ++ tailWord_496432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496432).length < 2 ^ (prefixWord ++ tailWord_496432).sum := by decide
  have hdescent : baseEnd_496432 < baseStart_496432 := by decide
  rcases family_descends (prefixWord ++ tailWord_496432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496434 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_496434 : Nat := 118140960795 + 496434 * 2 ^ 59
def prefixEnd_496434 : Nat := 4983230072969 + 3 ^ 40 * 496434 * 2
def baseEnd_496434 : Nat := 169939503489477288927965

theorem tailTrace_496434 : CollatzResearch.WordTrace tailWord_496434 prefixEnd_496434 169939503489477288927965 := by
  unfold tailWord_496434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526608870877969255574089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12070956989007918014864237 4526608870877969255574089)
  ·
    refine ⟨3394956653158476941680567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4526608870877969255574089 3394956653158476941680567)
    ·
      refine ⟨5092434979737715412520851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394956653158476941680567 5092434979737715412520851)
      ·
        refine ⟨7638652469606573118781277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092434979737715412520851 7638652469606573118781277)
        ·
          refine ⟨2864494676102464919542979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7638652469606573118781277 2864494676102464919542979)
          ·
            refine ⟨4296742014153697379314469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864494676102464919542979 4296742014153697379314469)
            ·
              refine ⟨805639127653818258621463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4296742014153697379314469 805639127653818258621463)
              ·
                refine ⟨1208458691480727387932195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805639127653818258621463 1208458691480727387932195)
                ·
                  refine ⟨1812688037221091081898293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208458691480727387932195 1812688037221091081898293)
                  ·
                    refine ⟨169939503489477288927965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1812688037221091081898293 169939503489477288927965)
                    ·
                      rfl

theorem cell22_496434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_496434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496434 prefixEnd_496434 := by exact prefixLift 496434
  have htrace : WordTrace (prefixWord ++ tailWord_496434) baseStart_496434 baseEnd_496434 := by
    simpa [prefixWord, tailWord_496434, baseEnd_496434] using wordTrace_append hprefix tailTrace_496434
  have hstable : (prefixWord ++ tailWord_496434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496434).length < 2 ^ (prefixWord ++ tailWord_496434).sum := by decide
  have hdescent : baseEnd_496434 < baseStart_496434 := by decide
  rcases family_descends (prefixWord ++ tailWord_496434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496436 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_496436 : Nat := 118140960795 + 496436 * 2 ^ 59
def prefixEnd_496436 : Nat := 4983230072969 + 3 ^ 40 * 496436 * 2
def baseEnd_496436 : Nat := 56646729376783316792653

theorem tailTrace_496436 : CollatzResearch.WordTrace tailWord_496436 prefixEnd_496436 56646729376783316792653 := by
  unfold tailWord_496436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053254214752315681934581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12071005619669754242579441 9053254214752315681934581)
  ·
    refine ⟨848742582633029595181367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9053254214752315681934581 848742582633029595181367)
    ·
      refine ⟨1273113873949544392772051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848742582633029595181367 1273113873949544392772051)
      ·
        refine ⟨1909670810924316589158077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273113873949544392772051 1909670810924316589158077)
        ·
          refine ⟨716126554096618720934279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1909670810924316589158077 716126554096618720934279)
          ·
            refine ⟨1074189831144928081401419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716126554096618720934279 1074189831144928081401419)
            ·
              refine ⟨1611284746717392122102129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074189831144928081401419 1611284746717392122102129)
              ·
                refine ⟨1208463560038044091576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611284746717392122102129 1208463560038044091576597)
                ·
                  refine ⟨56646729376783316792653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1208463560038044091576597 56646729376783316792653)
                  ·
                    rfl

theorem cell22_496436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_496436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496436 prefixEnd_496436 := by exact prefixLift 496436
  have htrace : WordTrace (prefixWord ++ tailWord_496436) baseStart_496436 baseEnd_496436 := by
    simpa [prefixWord, tailWord_496436, baseEnd_496436] using wordTrace_append hprefix tailTrace_496436
  have hstable : (prefixWord ++ tailWord_496436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496436).length < 2 ^ (prefixWord ++ tailWord_496436).sum := by decide
  have hdescent : baseEnd_496436 < baseStart_496436 := by decide
  rcases family_descends (prefixWord ++ tailWord_496436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496462 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_496462 : Nat := 118140960795 + 496462 * 2 ^ 59
def prefixEnd_496462 : Nat := 4983230072969 + 3 ^ 40 * 496462 * 2
def baseEnd_496462 : Nat := 169949088461694549227879

theorem tailTrace_496462 : CollatzResearch.WordTrace tailWord_496462 prefixEnd_496462 169949088461694549227879 := by
  unfold tailWord_496462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263432090926304725539455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12071637818273625202877093 2263432090926304725539455)
  ·
    refine ⟨3395148136389457088309183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263432090926304725539455 3395148136389457088309183)
    ·
      refine ⟨5092722204584185632463775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395148136389457088309183 5092722204584185632463775)
      ·
        refine ⟨7639083306876278448695663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092722204584185632463775 7639083306876278448695663)
        ·
          refine ⟨11458624960314417673043495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639083306876278448695663 11458624960314417673043495)
          ·
            refine ⟨17187937440471626509565243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458624960314417673043495 17187937440471626509565243)
            ·
              refine ⟨25781906160707439764347865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17187937440471626509565243 25781906160707439764347865)
              ·
                refine ⟨19336429620530579823260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25781906160707439764347865 19336429620530579823260899)
                ·
                  refine ⟨29004644430795869734891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19336429620530579823260899 29004644430795869734891349)
                  ·
                    refine ⟨169949088461694549227879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29004644430795869734891349 169949088461694549227879)
                    ·
                      rfl

theorem cell22_496462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_496462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496462 prefixEnd_496462 := by exact prefixLift 496462
  have htrace : WordTrace (prefixWord ++ tailWord_496462) baseStart_496462 baseEnd_496462 := by
    simpa [prefixWord, tailWord_496462, baseEnd_496462] using wordTrace_append hprefix tailTrace_496462
  have hstable : (prefixWord ++ tailWord_496462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496462).length < 2 ^ (prefixWord ++ tailWord_496462).sum := by decide
  have hdescent : baseEnd_496462 < baseStart_496462 := by decide
  rcases family_descends (prefixWord ++ tailWord_496462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496507 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_496507 : Nat := 118140960795 + 496507 * 2 ^ 59
def prefixEnd_496507 : Nat := 4983230072969 + 3 ^ 40 * 496507 * 2
def baseEnd_496507 : Nat := 169964492881329431852741

theorem tailTrace_496507 : CollatzResearch.WordTrace tailWord_496507 prefixEnd_496507 169964492881329431852741 := by
  unfold tailWord_496507
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109098012247410489703775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12072732008164940326469183 18109098012247410489703775)
  ·
    refine ⟨27163647018371115734555663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18109098012247410489703775 27163647018371115734555663)
    ·
      refine ⟨40745470527556673601833495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27163647018371115734555663 40745470527556673601833495)
      ·
        refine ⟨61118205791335010402750243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40745470527556673601833495 61118205791335010402750243)
        ·
          refine ⟨91677308687002515604125365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61118205791335010402750243 91677308687002515604125365)
          ·
            refine ⟨8594747689406485837886753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91677308687002515604125365 8594747689406485837886753)
            ·
              refine ⟨6446060767054864378415065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594747689406485837886753 6446060767054864378415065)
              ·
                refine ⟨4834545575291148283811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446060767054864378415065 4834545575291148283811299)
                ·
                  refine ⟨7251818362936722425716949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834545575291148283811299 7251818362936722425716949)
                  ·
                    refine ⟨169964492881329431852741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7251818362936722425716949 169964492881329431852741)
                    ·
                      rfl

theorem cell22_496507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_496507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496507 prefixEnd_496507 := by exact prefixLift 496507
  have htrace : WordTrace (prefixWord ++ tailWord_496507) baseStart_496507 baseEnd_496507 := by
    simpa [prefixWord, tailWord_496507, baseEnd_496507] using wordTrace_append hprefix tailTrace_496507
  have hstable : (prefixWord ++ tailWord_496507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496507).length < 2 ^ (prefixWord ++ tailWord_496507).sum := by decide
  have hdescent : baseEnd_496507 < baseStart_496507 := by decide
  rcases family_descends (prefixWord ++ tailWord_496507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496530 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_496530 : Nat := 118140960795 + 496530 * 2 ^ 59
def prefixEnd_496530 : Nat := 4983230072969 + 3 ^ 40 * 496530 * 2
def baseEnd_496530 : Nat := 169972366251365038527671

theorem tailTrace_496530 : CollatzResearch.WordTrace tailWord_496530 prefixEnd_496530 169972366251365038527671 := by
  unfold tailWord_496530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527484222791021354447761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12073291260776056945194029 4527484222791021354447761)
  ·
    refine ⟨3395613167093266015835821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4527484222791021354447761 3395613167093266015835821)
    ·
      refine ⟨1273354937659974755938433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3395613167093266015835821 1273354937659974755938433)
      ·
        refine ⟨955016203244981066953825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273354937659974755938433 955016203244981066953825)
        ·
          refine ⟨716262152433735800215369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 955016203244981066953825 716262152433735800215369)
          ·
            refine ⟨537196614325301850161527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716262152433735800215369 537196614325301850161527)
            ·
              refine ⟨805794921487952775242291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537196614325301850161527 805794921487952775242291)
              ·
                refine ⟨1208692382231929162863437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805794921487952775242291 1208692382231929162863437)
                ·
                  refine ⟨453259643336973436073789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208692382231929162863437 453259643336973436073789)
                  ·
                    refine ⟨169972366251365038527671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453259643336973436073789 169972366251365038527671)
                    ·
                      rfl

theorem cell22_496530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_496530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496530 prefixEnd_496530 := by exact prefixLift 496530
  have htrace : WordTrace (prefixWord ++ tailWord_496530) baseStart_496530 baseEnd_496530 := by
    simpa [prefixWord, tailWord_496530, baseEnd_496530] using wordTrace_append hprefix tailTrace_496530
  have hstable : (prefixWord ++ tailWord_496530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496530).length < 2 ^ (prefixWord ++ tailWord_496530).sum := by decide
  have hdescent : baseEnd_496530 < baseStart_496530 := by decide
  rcases family_descends (prefixWord ++ tailWord_496530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496543 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 5]
def baseStart_496543 : Nat := 118140960795 + 496543 * 2 ^ 59
def prefixEnd_496543 : Nat := 4983230072969 + 3 ^ 40 * 496543 * 2
def baseEnd_496543 : Nat := 56658938805679112650877

theorem tailTrace_496543 : CollatzResearch.WordTrace tailWord_496543 prefixEnd_496543 56658938805679112650877 := by
  unfold tailWord_496543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110411040116988638014283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12073607360077992425342855 18110411040116988638014283)
  ·
    refine ⟨27165616560175482957021425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18110411040116988638014283 27165616560175482957021425)
    ·
      refine ⟨20374212420131612217766069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27165616560175482957021425 20374212420131612217766069)
      ·
        refine ⟨1910082414387338645415569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20374212420131612217766069 1910082414387338645415569)
        ·
          refine ⟨1432561810790503984061677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1910082414387338645415569 1432561810790503984061677)
          ·
            refine ⟨537210679046438994023129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1432561810790503984061677 537210679046438994023129)
            ·
              refine ⟨402908009284829245517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537210679046438994023129 402908009284829245517347)
              ·
                refine ⟨604362013927243868276021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402908009284829245517347 604362013927243868276021)
                ·
                  refine ⟨56658938805679112650877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604362013927243868276021 56658938805679112650877)
                  ·
                    rfl

theorem cell22_496543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 5].length) (baseStart_496543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496543 prefixEnd_496543 := by exact prefixLift 496543
  have htrace : WordTrace (prefixWord ++ tailWord_496543) baseStart_496543 baseEnd_496543 := by
    simpa [prefixWord, tailWord_496543, baseEnd_496543] using wordTrace_append hprefix tailTrace_496543
  have hstable : (prefixWord ++ tailWord_496543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496543).length < 2 ^ (prefixWord ++ tailWord_496543).sum := by decide
  have hdescent : baseEnd_496543 < baseStart_496543 := by decide
  rcases family_descends (prefixWord ++ tailWord_496543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496569 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_496569 : Nat := 118140960795 + 496569 * 2 ^ 59
def prefixEnd_496569 : Nat := 4983230072969 + 3 ^ 40 * 496569 * 2
def baseEnd_496569 : Nat := 169985716748381936802551

theorem tailTrace_496569 : CollatzResearch.WordTrace tailWord_496569 prefixEnd_496569 169985716748381936802551 := by
  unfold tailWord_496569
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111359338022795078460761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12074239558681863385640507 18111359338022795078460761)
  ·
    refine ⟨13583519503517096308845571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18111359338022795078460761 13583519503517096308845571)
    ·
      refine ⟨20375279255275644463268357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13583519503517096308845571 20375279255275644463268357)
      ·
        refine ⟨3820364860364183336862817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20375279255275644463268357 3820364860364183336862817)
        ·
          refine ⟨2865273645273137502647113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3820364860364183336862817 2865273645273137502647113)
          ·
            refine ⟨2148955233954853126985335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2865273645273137502647113 2148955233954853126985335)
            ·
              refine ⟨3223432850932279690478003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148955233954853126985335 3223432850932279690478003)
              ·
                refine ⟨4835149276398419535717005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223432850932279690478003 4835149276398419535717005)
                ·
                  refine ⟨1813180978649407325893877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4835149276398419535717005 1813180978649407325893877)
                  ·
                    refine ⟨169985716748381936802551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1813180978649407325893877 169985716748381936802551)
                    ·
                      rfl

theorem cell22_496569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_496569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496569 prefixEnd_496569 := by exact prefixLift 496569
  have htrace : WordTrace (prefixWord ++ tailWord_496569) baseStart_496569 baseEnd_496569 := by
    simpa [prefixWord, tailWord_496569, baseEnd_496569] using wordTrace_append hprefix tailTrace_496569
  have hstable : (prefixWord ++ tailWord_496569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496569).length < 2 ^ (prefixWord ++ tailWord_496569).sum := by decide
  have hdescent : baseEnd_496569 < baseStart_496569 := by decide
  rcases family_descends (prefixWord ++ tailWord_496569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496618 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_496618 : Nat := 118140960795 + 496618 * 2 ^ 59
def prefixEnd_496618 : Nat := 4983230072969 + 3 ^ 40 * 496618 * 2
def baseEnd_496618 : Nat := 170002490449762142327401

theorem tailTrace_496618 : CollatzResearch.WordTrace tailWord_496618 prefixEnd_496618 170002490449762142327401 := by
  unfold tailWord_496618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528286628711319111748627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12075431009896850964663005 4528286628711319111748627)
  ·
    refine ⟨6792429943066978667622941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4528286628711319111748627 6792429943066978667622941)
    ·
      refine ⟨2547161228650117000358603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6792429943066978667622941 2547161228650117000358603)
      ·
        refine ⟨3820741842975175500537905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547161228650117000358603 3820741842975175500537905)
        ·
          refine ⟨2865556382231381625403429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3820741842975175500537905 2865556382231381625403429)
          ·
            refine ⟨537291821668384054763143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2865556382231381625403429 537291821668384054763143)
            ·
              refine ⟨805937732502576082144715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537291821668384054763143 805937732502576082144715)
              ·
                refine ⟨1208906598753864123217073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805937732502576082144715 1208906598753864123217073)
                ·
                  refine ⟨906679949065398092412805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208906598753864123217073 906679949065398092412805)
                  ·
                    refine ⟨170002490449762142327401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906679949065398092412805 170002490449762142327401)
                    ·
                      rfl

theorem cell22_496618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_496618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496618 prefixEnd_496618 := by exact prefixLift 496618
  have htrace : WordTrace (prefixWord ++ tailWord_496618) baseStart_496618 baseEnd_496618 := by
    simpa [prefixWord, tailWord_496618, baseEnd_496618] using wordTrace_append hprefix tailTrace_496618
  have hstable : (prefixWord ++ tailWord_496618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496618).length < 2 ^ (prefixWord ++ tailWord_496618).sum := by decide
  have hdescent : baseEnd_496618 < baseStart_496618 := by decide
  rcases family_descends (prefixWord ++ tailWord_496618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496648 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_496648 : Nat := 118140960795 + 496648 * 2 ^ 59
def prefixEnd_496648 : Nat := 4983230072969 + 3 ^ 40 * 496648 * 2
def baseEnd_496648 : Nat := 170012760062852064077309

theorem tailTrace_496648 : CollatzResearch.WordTrace tailWord_496648 prefixEnd_496648 170012760062852064077309 := by
  unfold tailWord_496648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057120352368295785293299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12076160469824394380391065 9057120352368295785293299)
  ·
    refine ⟨13585680528552443677939949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9057120352368295785293299 13585680528552443677939949)
    ·
      refine ⟨5094630198207166379227481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13585680528552443677939949 5094630198207166379227481)
      ·
        refine ⟨3820972648655374784420611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094630198207166379227481 3820972648655374784420611)
        ·
          refine ⟨5731458972983062176630917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820972648655374784420611 5731458972983062176630917)
          ·
            refine ⟨1074648557434324158118297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5731458972983062176630917 1074648557434324158118297)
            ·
              refine ⟨805986418075743118588723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074648557434324158118297 805986418075743118588723)
              ·
                refine ⟨1208979627113614677883085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805986418075743118588723 1208979627113614677883085)
                ·
                  refine ⟨453367360167605504206157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208979627113614677883085 453367360167605504206157)
                  ·
                    refine ⟨170012760062852064077309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453367360167605504206157 170012760062852064077309)
                    ·
                      rfl

theorem cell22_496648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_496648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496648 prefixEnd_496648 := by exact prefixLift 496648
  have htrace : WordTrace (prefixWord ++ tailWord_496648) baseStart_496648 baseEnd_496648 := by
    simpa [prefixWord, tailWord_496648, baseEnd_496648] using wordTrace_append hprefix tailTrace_496648
  have hstable : (prefixWord ++ tailWord_496648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496648).length < 2 ^ (prefixWord ++ tailWord_496648).sum := by decide
  have hdescent : baseEnd_496648 < baseStart_496648 := by decide
  rcases family_descends (prefixWord ++ tailWord_496648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496738 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_496738 : Nat := 118140960795 + 496738 * 2 ^ 59
def prefixEnd_496738 : Nat := 4983230072969 + 3 ^ 40 * 496738 * 2
def baseEnd_496738 : Nat := 170043568902121829327033

theorem tailTrace_496738 : CollatzResearch.WordTrace tailWord_496738 prefixEnd_496738 170043568902121829327033 := by
  unfold tailWord_496738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529380818602634235340717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12078348849607024627575245 4529380818602634235340717)
  ·
    refine ⟨1698517806975987838252769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4529380818602634235340717 1698517806975987838252769)
    ·
      refine ⟨1273888355231990878689577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1698517806975987838252769 1273888355231990878689577)
      ·
        refine ⟨955416266423993159017183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273888355231990878689577 955416266423993159017183)
        ·
          refine ⟨1433124399635989738525775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955416266423993159017183 1433124399635989738525775)
          ·
            refine ⟨2149686599453984607788663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433124399635989738525775 2149686599453984607788663)
            ·
              refine ⟨3224529899180976911682995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149686599453984607788663 3224529899180976911682995)
              ·
                refine ⟨4836794848771465367524493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224529899180976911682995 4836794848771465367524493)
                ·
                  refine ⟨1813798068289299512821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4836794848771465367524493 1813798068289299512821685)
                  ·
                    refine ⟨170043568902121829327033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1813798068289299512821685 170043568902121829327033)
                    ·
                      rfl

theorem cell22_496738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_496738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496738 prefixEnd_496738 := by exact prefixLift 496738
  have htrace : WordTrace (prefixWord ++ tailWord_496738) baseStart_496738 baseEnd_496738 := by
    simpa [prefixWord, tailWord_496738, baseEnd_496738] using wordTrace_append hprefix tailTrace_496738
  have hstable : (prefixWord ++ tailWord_496738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496738).length < 2 ^ (prefixWord ++ tailWord_496738).sum := by decide
  have hdescent : baseEnd_496738 < baseStart_496738 := by decide
  rcases family_descends (prefixWord ++ tailWord_496738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496757 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 4]
def baseStart_496757 : Nat := 118140960795 + 496757 * 2 ^ 59
def prefixEnd_496757 : Nat := 4983230072969 + 3 ^ 40 * 496757 * 2
def baseEnd_496757 : Nat := 56683357663470704367325

theorem tailTrace_496757 : CollatzResearch.WordTrace tailWord_496757 prefixEnd_496757 56683357663470704367325 := by
  unfold tailWord_496757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18118216261341703186304525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12078810840894468790869683 18118216261341703186304525)
  ·
    refine ⟨6794331098003138694864197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18118216261341703186304525 6794331098003138694864197)
    ·
      refine ⟨1273937080875588505287037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6794331098003138694864197 1273937080875588505287037)
      ·
        refine ⟨477726405328345689482639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1273937080875588505287037 477726405328345689482639)
        ·
          refine ⟨716589607992518534223959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477726405328345689482639 716589607992518534223959)
          ·
            refine ⟨1074884411988777801335939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716589607992518534223959 1074884411988777801335939)
            ·
              refine ⟨1612326617983166702003909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074884411988777801335939 1612326617983166702003909)
              ·
                refine ⟨302311240871843756625733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612326617983166702003909 302311240871843756625733)
                ·
                  refine ⟨56683357663470704367325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302311240871843756625733 56683357663470704367325)
                  ·
                    rfl

theorem cell22_496757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_496757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496757 prefixEnd_496757 := by exact prefixLift 496757
  have htrace : WordTrace (prefixWord ++ tailWord_496757) baseStart_496757 baseEnd_496757 := by
    simpa [prefixWord, tailWord_496757, baseEnd_496757] using wordTrace_append hprefix tailTrace_496757
  have hstable : (prefixWord ++ tailWord_496757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496757).length < 2 ^ (prefixWord ++ tailWord_496757).sum := by decide
  have hdescent : baseEnd_496757 < baseStart_496757 := by decide
  rcases family_descends (prefixWord ++ tailWord_496757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496817 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_496817 : Nat := 118140960795 + 496817 * 2 ^ 59
def prefixEnd_496817 : Nat := 4983230072969 + 3 ^ 40 * 496817 * 2
def baseEnd_496817 : Nat := 170070612216591956601791

theorem tailTrace_496817 : CollatzResearch.WordTrace tailWord_496817 prefixEnd_496817 170070612216591956601791 := by
  unfold tailWord_496817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120404641124333433488705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12080269760749555622325803 18120404641124333433488705)
  ·
    refine ⟨13590303480843250075116529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18120404641124333433488705 13590303480843250075116529)
    ·
      refine ⟨10192727610632437556337397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13590303480843250075116529 10192727610632437556337397)
      ·
        refine ⟨955568213496791020906631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10192727610632437556337397 955568213496791020906631)
        ·
          refine ⟨1433352320245186531359947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955568213496791020906631 1433352320245186531359947)
          ·
            refine ⟨2150028480367779797039921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433352320245186531359947 2150028480367779797039921)
            ·
              refine ⟨1612521360275834847779941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150028480367779797039921 1612521360275834847779941)
              ·
                refine ⟨302347755051719033958739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612521360275834847779941 302347755051719033958739)
                ·
                  refine ⟨453521632577578550938109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302347755051719033958739 453521632577578550938109)
                  ·
                    refine ⟨170070612216591956601791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453521632577578550938109 170070612216591956601791)
                    ·
                      rfl

theorem cell22_496817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_496817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496817 prefixEnd_496817 := by exact prefixLift 496817
  have htrace : WordTrace (prefixWord ++ tailWord_496817) baseStart_496817 baseEnd_496817 := by
    simpa [prefixWord, tailWord_496817, baseEnd_496817] using wordTrace_append hprefix tailTrace_496817
  have hstable : (prefixWord ++ tailWord_496817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496817).length < 2 ^ (prefixWord ++ tailWord_496817).sum := by decide
  have hdescent : baseEnd_496817 < baseStart_496817 := by decide
  rcases family_descends (prefixWord ++ tailWord_496817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496828 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_496828 : Nat := 118140960795 + 496828 * 2 ^ 59
def prefixEnd_496828 : Nat := 4983230072969 + 3 ^ 40 * 496828 * 2
def baseEnd_496828 : Nat := 170074377741391594576757

theorem tailTrace_496828 : CollatzResearch.WordTrace tailWord_496828 prefixEnd_496828 170074377741391594576757 := by
  unfold tailWord_496828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9060402922042241156069569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12080537229389654874759425 9060402922042241156069569)
  ·
    refine ⟨6795302191531680867052177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9060402922042241156069569 6795302191531680867052177)
    ·
      refine ⟨5096476643648760650289133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6795302191531680867052177 5096476643648760650289133)
      ·
        refine ⟨1911178741368285243858425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5096476643648760650289133 1911178741368285243858425)
        ·
          refine ⟨1433384056026213932893819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911178741368285243858425 1433384056026213932893819)
          ·
            refine ⟨2150076084039320899340729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433384056026213932893819 2150076084039320899340729)
            ·
              refine ⟨1612557063029490674505547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150076084039320899340729 1612557063029490674505547)
              ·
                refine ⟨2418835594544236011758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612557063029490674505547 2418835594544236011758321)
                ·
                  refine ⟨1814126695908177008818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418835594544236011758321 1814126695908177008818741)
                  ·
                    refine ⟨170074377741391594576757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1814126695908177008818741 170074377741391594576757)
                    ·
                      rfl

theorem cell22_496828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_496828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496828 prefixEnd_496828 := by exact prefixLift 496828
  have htrace : WordTrace (prefixWord ++ tailWord_496828) baseStart_496828 baseEnd_496828 := by
    simpa [prefixWord, tailWord_496828, baseEnd_496828] using wordTrace_append hprefix tailTrace_496828
  have hstable : (prefixWord ++ tailWord_496828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496828).length < 2 ^ (prefixWord ++ tailWord_496828).sum := by decide
  have hdescent : baseEnd_496828 < baseStart_496828 := by decide
  rcases family_descends (prefixWord ++ tailWord_496828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496890 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_496890 : Nat := 118140960795 + 496890 * 2 ^ 59
def prefixEnd_496890 : Nat := 4983230072969 + 3 ^ 40 * 496890 * 2
def baseEnd_496890 : Nat := 170095601608444099526567

theorem tailTrace_496890 : CollatzResearch.WordTrace tailWord_496890 prefixEnd_496890 170095601608444099526567 := by
  unfold tailWord_496890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530766792464966725224031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12082044779906577933930749 4530766792464966725224031)
  ·
    refine ⟨6796150188697450087836047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4530766792464966725224031 6796150188697450087836047)
    ·
      refine ⟨10194225283046175131754071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796150188697450087836047 10194225283046175131754071)
      ·
        refine ⟨15291337924569262697631107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10194225283046175131754071 15291337924569262697631107)
        ·
          refine ⟨22937006886853894046446661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15291337924569262697631107 22937006886853894046446661)
          ·
            refine ⟨4300688791285105133708749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22937006886853894046446661 4300688791285105133708749)
            ·
              refine ⟨1612758296731914425140781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4300688791285105133708749 1612758296731914425140781)
              ·
                refine ⟨604784361274467909427793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612758296731914425140781 604784361274467909427793)
                ·
                  refine ⟨453588270955850932070845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604784361274467909427793 453588270955850932070845)
                  ·
                    refine ⟨170095601608444099526567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453588270955850932070845 170095601608444099526567)
                    ·
                      rfl

theorem cell22_496890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_496890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496890 prefixEnd_496890 := by exact prefixLift 496890
  have htrace : WordTrace (prefixWord ++ tailWord_496890) baseStart_496890 baseEnd_496890 := by
    simpa [prefixWord, tailWord_496890, baseEnd_496890] using wordTrace_append hprefix tailTrace_496890
  have hstable : (prefixWord ++ tailWord_496890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496890).length < 2 ^ (prefixWord ++ tailWord_496890).sum := by decide
  have hdescent : baseEnd_496890 < baseStart_496890 := by decide
  rcases family_descends (prefixWord ++ tailWord_496890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496933 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_496933 : Nat := 118140960795 + 496933 * 2 ^ 59
def prefixEnd_496933 : Nat := 4983230072969 + 3 ^ 40 * 496933 * 2
def baseEnd_496933 : Nat := 170110321387206320701435

theorem tailTrace_496933 : CollatzResearch.WordTrace tailWord_496933 prefixEnd_496933 170110321387206320701435 := by
  unfold tailWord_496933
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124635508704085244711453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12083090339136056829807635 18124635508704085244711453)
  ·
    refine ⟨6796738315764031966766795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18124635508704085244711453 6796738315764031966766795)
    ·
      refine ⟨10195107473646047950150193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796738315764031966766795 10195107473646047950150193)
      ·
        refine ⟨7646330605234535962612645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10195107473646047950150193 7646330605234535962612645)
        ·
          refine ⟨1433686988481475492989871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7646330605234535962612645 1433686988481475492989871)
          ·
            refine ⟨2150530482722213239484807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433686988481475492989871 2150530482722213239484807)
            ·
              refine ⟨3225795724083319859227211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150530482722213239484807 3225795724083319859227211)
              ·
                refine ⟨4838693586124979788840817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225795724083319859227211 4838693586124979788840817)
                ·
                  refine ⟨3629020189593734841630613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838693586124979788840817 3629020189593734841630613)
                  ·
                    refine ⟨170110321387206320701435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3629020189593734841630613 170110321387206320701435)
                    ·
                      rfl

theorem cell22_496933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_496933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_496933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_496933 prefixEnd_496933 := by exact prefixLift 496933
  have htrace : WordTrace (prefixWord ++ tailWord_496933) baseStart_496933 baseEnd_496933 := by
    simpa [prefixWord, tailWord_496933, baseEnd_496933] using wordTrace_append hprefix tailTrace_496933
  have hstable : (prefixWord ++ tailWord_496933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496933).length < 2 ^ (prefixWord ++ tailWord_496933).sum := by decide
  have hdescent : baseEnd_496933 < baseStart_496933 := by decide
  rcases family_descends (prefixWord ++ tailWord_496933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497027 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 4]
def baseStart_497027 : Nat := 118140960795 + 497027 * 2 ^ 59
def prefixEnd_497027 : Nat := 4983230072969 + 3 ^ 40 * 497027 * 2
def baseEnd_497027 : Nat := 56714166502740469617049

theorem tailTrace_497027 : CollatzResearch.WordTrace tailWord_497027 prefixEnd_497027 56714166502740469617049 := by
  unfold tailWord_497027
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128063970363539298633335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12085375980242359532422223 18128063970363539298633335)
  ·
    refine ⟨27192095955545308947950003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18128063970363539298633335 27192095955545308947950003)
    ·
      refine ⟨40788143933317963421925005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27192095955545308947950003 40788143933317963421925005)
      ·
        refine ⟨15295553974994236283221877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40788143933317963421925005 15295553974994236283221877)
        ·
          refine ⟨1433958185155709651552051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15295553974994236283221877 1433958185155709651552051)
          ·
            refine ⟨2150937277733564477328077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433958185155709651552051 2150937277733564477328077)
            ·
              refine ⟨806601479150086678998029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2150937277733564477328077 806601479150086678998029)
              ·
                refine ⟨302475554681282504624261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 806601479150086678998029 302475554681282504624261)
                ·
                  refine ⟨56714166502740469617049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302475554681282504624261 56714166502740469617049)
                  ·
                    rfl

theorem cell22_497027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 4].length) (baseStart_497027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497027 prefixEnd_497027 := by exact prefixLift 497027
  have htrace : WordTrace (prefixWord ++ tailWord_497027) baseStart_497027 baseEnd_497027 := by
    simpa [prefixWord, tailWord_497027, baseEnd_497027] using wordTrace_append hprefix tailTrace_497027
  have hstable : (prefixWord ++ tailWord_497027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497027).length < 2 ^ (prefixWord ++ tailWord_497027).sum := by decide
  have hdescent : baseEnd_497027 < baseStart_497027 := by decide
  rcases family_descends (prefixWord ++ tailWord_497027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497055 : List Nat := [1, 1, 2, 5, 1, 3, 2, 7]
def baseStart_497055 : Nat := 118140960795 + 497055 * 2 ^ 59
def prefixEnd_497055 : Nat := 4983230072969 + 3 ^ 40 * 497055 * 2
def baseEnd_497055 : Nat := 18905787164493185461229

theorem tailTrace_497055 : CollatzResearch.WordTrace tailWord_497055 prefixEnd_497055 18905787164493185461229 := by
  unfold tailWord_497055
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129085214262100080652619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12086056809508066720435079 18129085214262100080652619)
  ·
    refine ⟨27193627821393150120978929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129085214262100080652619 27193627821393150120978929)
    ·
      refine ⟨20395220866044862590734197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27193627821393150120978929 20395220866044862590734197)
      ·
        refine ⟨1912051956191705867881331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20395220866044862590734197 1912051956191705867881331)
        ·
          refine ⟨2868077934287558801821997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912051956191705867881331 2868077934287558801821997)
          ·
            refine ⟨1075529225357834550683249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2868077934287558801821997 1075529225357834550683249)
            ·
              refine ⟨806646919018375913012437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075529225357834550683249 806646919018375913012437)
              ·
                refine ⟨18905787164493185461229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 806646919018375913012437 18905787164493185461229)
                ·
                  rfl

theorem cell22_497055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 7].length) (baseStart_497055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497055 prefixEnd_497055 := by exact prefixLift 497055
  have htrace : WordTrace (prefixWord ++ tailWord_497055) baseStart_497055 baseEnd_497055 := by
    simpa [prefixWord, tailWord_497055, baseEnd_497055] using wordTrace_append hprefix tailTrace_497055
  have hstable : (prefixWord ++ tailWord_497055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497055).length < 2 ^ (prefixWord ++ tailWord_497055).sum := by decide
  have hdescent : baseEnd_497055 < baseStart_497055 := by decide
  rcases family_descends (prefixWord ++ tailWord_497055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497117 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 5]
def baseStart_497117 : Nat := 118140960795 + 497117 * 2 ^ 59
def prefixEnd_497117 : Nat := 4983230072969 + 3 ^ 40 * 497117 * 2
def baseEnd_497117 : Nat := 56724436115830391366957

theorem tailTrace_497117 : CollatzResearch.WordTrace tailWord_497117 prefixEnd_497117 56724436115830391366957 := by
  unfold tailWord_497117
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131346540037484669409605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12087564360024989779606403 18131346540037484669409605)
  ·
    refine ⟨3399627476257028375514301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18131346540037484669409605 3399627476257028375514301)
    ·
      refine ⟨1274860303596385640817863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3399627476257028375514301 1274860303596385640817863)
      ·
        refine ⟨1912290455394578461226795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274860303596385640817863 1912290455394578461226795)
        ·
          refine ⟨2868435683091867691840193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912290455394578461226795 2868435683091867691840193)
          ·
            refine ⟨2151326762318900768880145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868435683091867691840193 2151326762318900768880145)
            ·
              refine ⟨1613495071739175576660109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151326762318900768880145 1613495071739175576660109)
              ·
                refine ⟨605060651902190841247541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613495071739175576660109 605060651902190841247541)
                ·
                  refine ⟨56724436115830391366957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605060651902190841247541 56724436115830391366957)
                  ·
                    rfl

theorem cell22_497117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_497117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497117 prefixEnd_497117 := by exact prefixLift 497117
  have htrace : WordTrace (prefixWord ++ tailWord_497117) baseStart_497117 baseEnd_497117 := by
    simpa [prefixWord, tailWord_497117, baseEnd_497117] using wordTrace_append hprefix tailTrace_497117
  have hstable : (prefixWord ++ tailWord_497117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497117).length < 2 ^ (prefixWord ++ tailWord_497117).sum := by decide
  have hdescent : baseEnd_497117 < baseStart_497117 := by decide
  rcases family_descends (prefixWord ++ tailWord_497117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497160 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_497160 : Nat := 118140960795 + 497160 * 2 ^ 59
def prefixEnd_497160 : Nat := 4983230072969 + 3 ^ 40 * 497160 * 2
def baseEnd_497160 : Nat := 170188028126253395275739

theorem tailTrace_497160 : CollatzResearch.WordTrace tailWord_497160 prefixEnd_497160 170188028126253395275739 := by
  unfold tailWord_497160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066457439440851506612467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12088609919254468675483289 9066457439440851506612467)
  ·
    refine ⟨13599686159161277259918701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066457439440851506612467 13599686159161277259918701)
    ·
      refine ⟨5099882309685478972469513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13599686159161277259918701 5099882309685478972469513)
      ·
        refine ⟨3824911732264109229352135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5099882309685478972469513 3824911732264109229352135)
        ·
          refine ⟨5737367598396163844028203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824911732264109229352135 5737367598396163844028203)
          ·
            refine ⟨8606051397594245766042305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5737367598396163844028203 8606051397594245766042305)
            ·
              refine ⟨6454538548195684324531729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8606051397594245766042305 6454538548195684324531729)
              ·
                refine ⟨4840903911146763243398797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454538548195684324531729 4840903911146763243398797)
                ·
                  refine ⟨1815338966680036216274549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4840903911146763243398797 1815338966680036216274549)
                  ·
                    refine ⟨170188028126253395275739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1815338966680036216274549 170188028126253395275739)
                    ·
                      rfl

theorem cell22_497160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_497160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497160 prefixEnd_497160 := by exact prefixLift 497160
  have htrace : WordTrace (prefixWord ++ tailWord_497160) baseStart_497160 baseEnd_497160 := by
    simpa [prefixWord, tailWord_497160, baseEnd_497160] using wordTrace_append hprefix tailTrace_497160
  have hstable : (prefixWord ++ tailWord_497160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497160).length < 2 ^ (prefixWord ++ tailWord_497160).sum := by decide
  have hdescent : baseEnd_497160 < baseStart_497160 := by decide
  rcases family_descends (prefixWord ++ tailWord_497160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497162 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_497162 : Nat := 118140960795 + 497162 * 2 ^ 59
def prefixEnd_497162 : Nat := 4983230072969 + 3 ^ 40 * 497162 * 2
def baseEnd_497162 : Nat := 56729570922375352241911

theorem tailTrace_497162 : CollatzResearch.WordTrace tailWord_497162 prefixEnd_497162 56729570922375352241911 := by
  unfold tailWord_497162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533246956218614338699435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12088658549916304903198493 4533246956218614338699435)
  ·
    refine ⟨6799870434327921508049153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533246956218614338699435 6799870434327921508049153)
    ·
      refine ⟨5099902825745941131036865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6799870434327921508049153 5099902825745941131036865)
      ·
        refine ⟨3824927119309455848277649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5099902825745941131036865 3824927119309455848277649)
        ·
          refine ⟨2868695339482091886208237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3824927119309455848277649 2868695339482091886208237)
          ·
            refine ⟨1075760752305784457328089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2868695339482091886208237 1075760752305784457328089)
            ·
              refine ⟨806820564229338342996067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075760752305784457328089 806820564229338342996067)
              ·
                refine ⟨1210230846344007514494101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806820564229338342996067 1210230846344007514494101)
                ·
                  refine ⟨56729570922375352241911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1210230846344007514494101 56729570922375352241911)
                  ·
                    rfl

theorem cell22_497162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_497162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497162 prefixEnd_497162 := by exact prefixLift 497162
  have htrace : WordTrace (prefixWord ++ tailWord_497162) baseStart_497162 baseEnd_497162 := by
    simpa [prefixWord, tailWord_497162, baseEnd_497162] using wordTrace_append hprefix tailTrace_497162
  have hstable : (prefixWord ++ tailWord_497162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497162).length < 2 ^ (prefixWord ++ tailWord_497162).sum := by decide
  have hdescent : baseEnd_497162 < baseStart_497162 := by decide
  rcases family_descends (prefixWord ++ tailWord_497162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497269 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 5]
def baseStart_497269 : Nat := 118140960795 + 497269 * 2 ^ 59
def prefixEnd_497269 : Nat := 4983230072969 + 3 ^ 40 * 497269 * 2
def baseEnd_497269 : Nat := 56741780351271148100135

theorem tailTrace_497269 : CollatzResearch.WordTrace tailWord_497269 prefixEnd_497269 56741780351271148100135 := by
  unfold tailWord_497269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136890435486814628942861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12091260290324543085961907 18136890435486814628942861)
  ·
    refine ⟨6801333913307555485853573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18136890435486814628942861 6801333913307555485853573)
    ·
      refine ⟨1275250108745166653597545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6801333913307555485853573 1275250108745166653597545)
      ·
        refine ⟨956437581558874990198159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1275250108745166653597545 956437581558874990198159)
        ·
          refine ⟨1434656372338312485297239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956437581558874990198159 1434656372338312485297239)
          ·
            refine ⟨2151984558507468727945859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434656372338312485297239 2151984558507468727945859)
            ·
              refine ⟨3227976837761203091918789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151984558507468727945859 3227976837761203091918789)
              ·
                refine ⟨605245657080225579734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3227976837761203091918789 605245657080225579734773)
                ·
                  refine ⟨56741780351271148100135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605245657080225579734773 56741780351271148100135)
                  ·
                    rfl

theorem cell22_497269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_497269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497269 prefixEnd_497269 := by exact prefixLift 497269
  have htrace : WordTrace (prefixWord ++ tailWord_497269) baseStart_497269 baseEnd_497269 := by
    simpa [prefixWord, tailWord_497269, baseEnd_497269] using wordTrace_append hprefix tailTrace_497269
  have hstable : (prefixWord ++ tailWord_497269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497269).length < 2 ^ (prefixWord ++ tailWord_497269).sum := by decide
  have hdescent : baseEnd_497269 < baseStart_497269 := by decide
  rcases family_descends (prefixWord ++ tailWord_497269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497284 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_497284 : Nat := 118140960795 + 497284 * 2 ^ 59
def prefixEnd_497284 : Nat := 4983230072969 + 3 ^ 40 * 497284 * 2
def baseEnd_497284 : Nat := 170230475860358405175359

theorem tailTrace_497284 : CollatzResearch.WordTrace tailWord_497284 prefixEnd_497284 170230475860358405175359 := by
  unfold tailWord_497284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068718765216236095369453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12091625020288314793825937 9068718765216236095369453)
  ·
    refine ⟨3400769536956088535763545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9068718765216236095369453 3400769536956088535763545)
    ·
      refine ⟨2550577152717066401822659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3400769536956088535763545 2550577152717066401822659)
      ·
        refine ⟨3825865729075599602733989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550577152717066401822659 3825865729075599602733989)
        ·
          refine ⟨717349824201674925512623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3825865729075599602733989 717349824201674925512623)
          ·
            refine ⟨1076024736302512388268935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717349824201674925512623 1076024736302512388268935)
            ·
              refine ⟨1614037104453768582403403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076024736302512388268935 1614037104453768582403403)
              ·
                refine ⟨2421055656680652873605105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614037104453768582403403 2421055656680652873605105)
                ·
                  refine ⟨1815791742510489655203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421055656680652873605105 1815791742510489655203829)
                  ·
                    refine ⟨170230475860358405175359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1815791742510489655203829 170230475860358405175359)
                    ·
                      rfl

theorem cell22_497284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_497284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497284 prefixEnd_497284 := by exact prefixLift 497284
  have htrace : WordTrace (prefixWord ++ tailWord_497284) baseStart_497284 baseEnd_497284 := by
    simpa [prefixWord, tailWord_497284, baseEnd_497284] using wordTrace_append hprefix tailTrace_497284
  have hstable : (prefixWord ++ tailWord_497284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497284).length < 2 ^ (prefixWord ++ tailWord_497284).sum := by decide
  have hdescent : baseEnd_497284 < baseStart_497284 := by decide
  rcases family_descends (prefixWord ++ tailWord_497284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497316 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_497316 : Nat := 118140960795 + 497316 * 2 ^ 59
def prefixEnd_497316 : Nat := 4983230072969 + 3 ^ 40 * 497316 * 2
def baseEnd_497316 : Nat := 170241430114320988375261

theorem tailTrace_497316 : CollatzResearch.WordTrace tailWord_497316 prefixEnd_497316 170241430114320988375261 := by
  unfold tailWord_497316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069302333158270827951901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12092403110877694437269201 9069302333158270827951901)
  ·
    refine ⟨3400988374934351560481963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9069302333158270827951901 3400988374934351560481963)
    ·
      refine ⟨5101482562401527340722945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3400988374934351560481963 5101482562401527340722945)
      ·
        refine ⟨3826111921801145505542209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5101482562401527340722945 3826111921801145505542209)
        ·
          refine ⟨2869583941350859129156657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826111921801145505542209 2869583941350859129156657)
          ·
            refine ⟨2152187956013144346867493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2869583941350859129156657 2152187956013144346867493)
            ·
              refine ⟨403535241752464565037655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2152187956013144346867493 403535241752464565037655)
              ·
                refine ⟨605302862628696847556483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403535241752464565037655 605302862628696847556483)
                ·
                  refine ⟨907954293943045271334725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605302862628696847556483 907954293943045271334725)
                  ·
                    refine ⟨170241430114320988375261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907954293943045271334725 170241430114320988375261)
                    ·
                      rfl

theorem cell22_497316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_497316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497316 prefixEnd_497316 := by exact prefixLift 497316
  have htrace : WordTrace (prefixWord ++ tailWord_497316) baseStart_497316 baseEnd_497316 := by
    simpa [prefixWord, tailWord_497316, baseEnd_497316] using wordTrace_append hprefix tailTrace_497316
  have hstable : (prefixWord ++ tailWord_497316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497316).length < 2 ^ (prefixWord ++ tailWord_497316).sum := by decide
  have hdescent : baseEnd_497316 < baseStart_497316 := by decide
  rcases family_descends (prefixWord ++ tailWord_497316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497320 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_497320 : Nat := 118140960795 + 497320 * 2 ^ 59
def prefixEnd_497320 : Nat := 4983230072969 + 3 ^ 40 * 497320 * 2
def baseEnd_497320 : Nat := 56747599798688770425083

theorem tailTrace_497320 : CollatzResearch.WordTrace tailWord_497320 prefixEnd_497320 56747599798688770425083 := by
  unfold tailWord_497320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069375279151025169524707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12092500372201366892699609 9069375279151025169524707)
  ·
    refine ⟨13604062918726537754287061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069375279151025169524707 13604062918726537754287061)
    ·
      refine ⟨318845224657653228616103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13604062918726537754287061 318845224657653228616103)
      ·
        refine ⟨478267836986479842924155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318845224657653228616103 478267836986479842924155)
        ·
          refine ⟨717401755479719764386233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478267836986479842924155 717401755479719764386233)
          ·
            refine ⟨538051316609789823289675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717401755479719764386233 538051316609789823289675)
            ·
              refine ⟨807076974914684734934513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538051316609789823289675 807076974914684734934513)
              ·
                refine ⟨605307731186013551200885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807076974914684734934513 605307731186013551200885)
                ·
                  refine ⟨56747599798688770425083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605307731186013551200885 56747599798688770425083)
                  ·
                    rfl

theorem cell22_497320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_497320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497320 prefixEnd_497320 := by exact prefixLift 497320
  have htrace : WordTrace (prefixWord ++ tailWord_497320) baseStart_497320 baseEnd_497320 := by
    simpa [prefixWord, tailWord_497320, baseEnd_497320] using wordTrace_append hprefix tailTrace_497320
  have hstable : (prefixWord ++ tailWord_497320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497320).length < 2 ^ (prefixWord ++ tailWord_497320).sum := by decide
  have hdescent : baseEnd_497320 < baseStart_497320 := by decide
  rcases family_descends (prefixWord ++ tailWord_497320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497327 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_497327 : Nat := 118140960795 + 497327 * 2 ^ 59
def prefixEnd_497327 : Nat := 4983230072969 + 3 ^ 40 * 497327 * 2
def baseEnd_497327 : Nat := 170245195639120626350227

theorem tailTrace_497327 : CollatzResearch.WordTrace tailWord_497327 prefixEnd_497327 170245195639120626350227 := by
  unfold tailWord_497327
  simp only [CollatzResearch.WordTrace]
  refine ⟨18139005869276690534554235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12092670579517793689702823 18139005869276690534554235)
  ·
    refine ⟨27208508803915035801831353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18139005869276690534554235 27208508803915035801831353)
    ·
      refine ⟨20406381602936276851373515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27208508803915035801831353 20406381602936276851373515)
      ·
        refine ⟨30609572404404415277060273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20406381602936276851373515 30609572404404415277060273)
        ·
          refine ⟨22957179303303311457795205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30609572404404415277060273 22957179303303311457795205)
          ·
            refine ⟨4304471119369370898336601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22957179303303311457795205 4304471119369370898336601)
            ·
              refine ⟨3228353339527028173752451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304471119369370898336601 3228353339527028173752451)
              ·
                refine ⟨4842530009290542260628677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3228353339527028173752451 4842530009290542260628677)
                ·
                  refine ⟨907974376741976673867877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4842530009290542260628677 907974376741976673867877)
                  ·
                    refine ⟨170245195639120626350227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 907974376741976673867877 170245195639120626350227)
                    ·
                      rfl

theorem cell22_497327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_497327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497327 prefixEnd_497327 := by exact prefixLift 497327
  have htrace : WordTrace (prefixWord ++ tailWord_497327) baseStart_497327 baseEnd_497327 := by
    simpa [prefixWord, tailWord_497327, baseEnd_497327] using wordTrace_append hprefix tailTrace_497327
  have hstable : (prefixWord ++ tailWord_497327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497327).length < 2 ^ (prefixWord ++ tailWord_497327).sum := by decide
  have hdescent : baseEnd_497327 < baseStart_497327 := by decide
  rcases family_descends (prefixWord ++ tailWord_497327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497350 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_497350 : Nat := 118140960795 + 497350 * 2 ^ 59
def prefixEnd_497350 : Nat := 4983230072969 + 3 ^ 40 * 497350 * 2
def baseEnd_497350 : Nat := 170253069009156233025157

theorem tailTrace_497350 : CollatzResearch.WordTrace tailWord_497350 prefixEnd_497350 170253069009156233025157 := by
  unfold tailWord_497350
  simp only [CollatzResearch.WordTrace]
  refine ⟨566870148381042670707547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12093229832128910308427669 566870148381042670707547)
  ·
    refine ⟨850305222571564006061321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566870148381042670707547 850305222571564006061321)
    ·
      refine ⟨637728916928673004545991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850305222571564006061321 637728916928673004545991)
      ·
        refine ⟨956593375393009506818987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637728916928673004545991 956593375393009506818987)
        ·
          refine ⟨1434890063089514260228481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956593375393009506818987 1434890063089514260228481)
          ·
            refine ⟨1076167547317135695171361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434890063089514260228481 1076167547317135695171361)
            ·
              refine ⟨807125660487851771378521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076167547317135695171361 807125660487851771378521)
              ·
                refine ⟨605344245365888828533891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807125660487851771378521 605344245365888828533891)
                ·
                  refine ⟨908016368048833242800837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605344245365888828533891 908016368048833242800837)
                  ·
                    refine ⟨170253069009156233025157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908016368048833242800837 170253069009156233025157)
                    ·
                      rfl

theorem cell22_497350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_497350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497350 prefixEnd_497350 := by exact prefixLift 497350
  have htrace : WordTrace (prefixWord ++ tailWord_497350) baseStart_497350 baseEnd_497350 := by
    simpa [prefixWord, tailWord_497350, baseEnd_497350] using wordTrace_append hprefix tailTrace_497350
  have hstable : (prefixWord ++ tailWord_497350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497350).length < 2 ^ (prefixWord ++ tailWord_497350).sum := by decide
  have hdescent : baseEnd_497350 < baseStart_497350 := by decide
  rcases family_descends (prefixWord ++ tailWord_497350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497387 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 7]
def baseStart_497387 : Nat := 118140960795 + 497387 * 2 ^ 59
def prefixEnd_497387 : Nat := 4983230072969 + 3 ^ 40 * 497387 * 2
def baseEnd_497387 : Nat := 56755244955100156616681

theorem tailTrace_497387 : CollatzResearch.WordTrace tailWord_497387 prefixEnd_497387 56755244955100156616681 := by
  unfold tailWord_497387
  simp only [CollatzResearch.WordTrace]
  refine ⟨18141194249059320781738415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12094129499372880521158943 18141194249059320781738415)
  ·
    refine ⟨27211791373588981172607623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18141194249059320781738415 27211791373588981172607623)
    ·
      refine ⟨40817687060383471758911435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27211791373588981172607623 40817687060383471758911435)
      ·
        refine ⟨61226530590575207638367153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40817687060383471758911435 61226530590575207638367153)
        ·
          refine ⟨45919897942931405728775365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61226530590575207638367153 45919897942931405728775365)
          ·
            refine ⟨8609980864299638574145381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45919897942931405728775365 8609980864299638574145381)
            ·
              refine ⟨1614371412056182232652259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8609980864299638574145381 1614371412056182232652259)
              ·
                refine ⟨2421557118084273348978389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614371412056182232652259 2421557118084273348978389)
                ·
                  refine ⟨56755244955100156616681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2421557118084273348978389 56755244955100156616681)
                  ·
                    rfl

theorem cell22_497387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_497387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497387 prefixEnd_497387 := by exact prefixLift 497387
  have htrace : WordTrace (prefixWord ++ tailWord_497387) baseStart_497387 baseEnd_497387 := by
    simpa [prefixWord, tailWord_497387, baseEnd_497387] using wordTrace_append hprefix tailTrace_497387
  have hstable : (prefixWord ++ tailWord_497387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497387).length < 2 ^ (prefixWord ++ tailWord_497387).sum := by decide
  have hdescent : baseEnd_497387 < baseStart_497387 := by decide
  rcases family_descends (prefixWord ++ tailWord_497387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_497402 : Nat := 118140960795 + 497402 * 2 ^ 59
def prefixEnd_497402 : Nat := 4983230072969 + 3 ^ 40 * 497402 * 2
def baseEnd_497402 : Nat := 170270869671845430724997

theorem tailTrace_497402 : CollatzResearch.WordTrace tailWord_497402 prefixEnd_497402 170270869671845430724997 := by
  unfold tailWord_497402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535435336001244585883615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12094494229336652229022973 4535435336001244585883615)
  ·
    refine ⟨6803153004001866878825423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4535435336001244585883615 6803153004001866878825423)
    ·
      refine ⟨10204729506002800318238135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803153004001866878825423 10204729506002800318238135)
      ·
        refine ⟨15307094259004200477357203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204729506002800318238135 15307094259004200477357203)
        ·
          refine ⟨22960641388506300716035805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15307094259004200477357203 22960641388506300716035805)
          ·
            refine ⟨8610240520689862768513427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22960641388506300716035805 8610240520689862768513427)
            ·
              refine ⟨12915360781034794152770141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8610240520689862768513427 12915360781034794152770141)
              ·
                refine ⟨4843260292888047807288803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12915360781034794152770141 4843260292888047807288803)
                ·
                  refine ⟨7264890439332071710933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4843260292888047807288803 7264890439332071710933205)
                  ·
                    refine ⟨170270869671845430724997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7264890439332071710933205 170270869671845430724997)
                    ·
                      rfl

theorem cell22_497402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_497402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497402 prefixEnd_497402 := by exact prefixLift 497402
  have htrace : WordTrace (prefixWord ++ tailWord_497402) baseStart_497402 baseEnd_497402 := by
    simpa [prefixWord, tailWord_497402, baseEnd_497402] using wordTrace_append hprefix tailTrace_497402
  have hstable : (prefixWord ++ tailWord_497402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497402).length < 2 ^ (prefixWord ++ tailWord_497402).sum := by decide
  have hdescent : baseEnd_497402 < baseStart_497402 := by decide
  rcases family_descends (prefixWord ++ tailWord_497402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497404 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_497404 : Nat := 118140960795 + 497404 * 2 ^ 59
def prefixEnd_497404 : Nat := 4983230072969 + 3 ^ 40 * 497404 * 2
def baseEnd_497404 : Nat := 56757184770906030724997

theorem tailTrace_497404 : CollatzResearch.WordTrace tailWord_497404 prefixEnd_497404 56757184770906030724997 := by
  unfold tailWord_497404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070907144998866342553633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12094542859998488456738177 9070907144998866342553633)
  ·
    refine ⟨6803180358749149756915225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9070907144998866342553633 6803180358749149756915225)
    ·
      refine ⟨5102385269061862317686419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6803180358749149756915225 5102385269061862317686419)
      ·
        refine ⟨7653577903592793476529629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5102385269061862317686419 7653577903592793476529629)
        ·
          refine ⟨2870091713847297553698611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7653577903592793476529629 2870091713847297553698611)
          ·
            refine ⟨4305137570770946330547917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870091713847297553698611 4305137570770946330547917)
            ·
              refine ⟨1614426589039104873955469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4305137570770946330547917 1614426589039104873955469)
              ·
                refine ⟨605409970889664327733301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1614426589039104873955469 605409970889664327733301)
                ·
                  refine ⟨56757184770906030724997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 605409970889664327733301 56757184770906030724997)
                  ·
                    rfl

theorem cell22_497404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_497404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497404 prefixEnd_497404 := by exact prefixLift 497404
  have htrace : WordTrace (prefixWord ++ tailWord_497404) baseStart_497404 baseEnd_497404 := by
    simpa [prefixWord, tailWord_497404, baseEnd_497404] using wordTrace_append hprefix tailTrace_497404
  have hstable : (prefixWord ++ tailWord_497404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497404).length < 2 ^ (prefixWord ++ tailWord_497404).sum := by decide
  have hdescent : baseEnd_497404 < baseStart_497404 := by decide
  rcases family_descends (prefixWord ++ tailWord_497404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497464 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_497464 : Nat := 118140960795 + 497464 * 2 ^ 59
def prefixEnd_497464 : Nat := 4983230072969 + 3 ^ 40 * 497464 * 2
def baseEnd_497464 : Nat := 170292093538897935674807

theorem tailTrace_497464 : CollatzResearch.WordTrace tailWord_497464 prefixEnd_497464 170292093538897935674807 := by
  unfold tailWord_497464
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072001334890181466145723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12096001779853575288194297 9072001334890181466145723)
  ·
    refine ⟨13608002002335272199218585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9072001334890181466145723 13608002002335272199218585)
    ·
      refine ⟨10206001501751454149413939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13608002002335272199218585 10206001501751454149413939)
      ·
        refine ⟨15309002252627181224120909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206001501751454149413939 15309002252627181224120909)
        ·
          refine ⟨5740875844735192959045341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15309002252627181224120909 5740875844735192959045341)
          ·
            refine ⟨2152828441775697359642003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5740875844735192959045341 2152828441775697359642003)
            ·
              refine ⟨3229242662663546039463005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152828441775697359642003 3229242662663546039463005)
              ·
                refine ⟨1210965998498829764798627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3229242662663546039463005 1210965998498829764798627)
                ·
                  refine ⟨1816448997748244647197941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210965998498829764798627 1816448997748244647197941)
                  ·
                    refine ⟨170292093538897935674807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1816448997748244647197941 170292093538897935674807)
                    ·
                      rfl

theorem cell22_497464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_497464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497464 prefixEnd_497464 := by exact prefixLift 497464
  have htrace : WordTrace (prefixWord ++ tailWord_497464) baseStart_497464 baseEnd_497464 := by
    simpa [prefixWord, tailWord_497464, baseEnd_497464] using wordTrace_append hprefix tailTrace_497464
  have hstable : (prefixWord ++ tailWord_497464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497464).length < 2 ^ (prefixWord ++ tailWord_497464).sum := by decide
  have hdescent : baseEnd_497464 < baseStart_497464 := by decide
  rcases family_descends (prefixWord ++ tailWord_497464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497485 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_497485 : Nat := 118140960795 + 497485 * 2 ^ 59
def prefixEnd_497485 : Nat := 4983230072969 + 3 ^ 40 * 497485 * 2
def baseEnd_497485 : Nat := 170299282268060880899743

theorem tailTrace_497485 : CollatzResearch.WordTrace tailWord_497485 prefixEnd_497485 170299282268060880899743 := by
  unfold tailWord_497485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18144768602704283518805909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12096512401802855679203939 18144768602704283518805909)
  ·
    refine ⟨850536028251763289944027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18144768602704283518805909 850536028251763289944027)
    ·
      refine ⟨1275804042377644934916041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850536028251763289944027 1275804042377644934916041)
      ·
        refine ⟨956853031783233701187031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1275804042377644934916041 956853031783233701187031)
        ·
          refine ⟨1435279547674850551780547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956853031783233701187031 1435279547674850551780547)
          ·
            refine ⟨2152919321512275827670821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435279547674850551780547 2152919321512275827670821)
            ·
              refine ⟨403672372783551717688279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2152919321512275827670821 403672372783551717688279)
              ·
                refine ⟨605508559175327576532419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403672372783551717688279 605508559175327576532419)
                ·
                  refine ⟨908262838762991364798629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605508559175327576532419 908262838762991364798629)
                  ·
                    refine ⟨170299282268060880899743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908262838762991364798629 170299282268060880899743)
                    ·
                      rfl

theorem cell22_497485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_497485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497485 prefixEnd_497485 := by exact prefixLift 497485
  have htrace : WordTrace (prefixWord ++ tailWord_497485) baseStart_497485 baseEnd_497485 := by
    simpa [prefixWord, tailWord_497485, baseEnd_497485] using wordTrace_append hprefix tailTrace_497485
  have hstable : (prefixWord ++ tailWord_497485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497485).length < 2 ^ (prefixWord ++ tailWord_497485).sum := by decide
  have hdescent : baseEnd_497485 < baseStart_497485 := by decide
  rcases family_descends (prefixWord ++ tailWord_497485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497539 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 7]
def baseStart_497539 : Nat := 118140960795 + 497539 * 2 ^ 59
def prefixEnd_497539 : Nat := 4983230072969 + 3 ^ 40 * 497539 * 2
def baseEnd_497539 : Nat := 56772589190540913349859

theorem tailTrace_497539 : CollatzResearch.WordTrace tailWord_497539 prefixEnd_497539 56772589190540913349859 := by
  unfold tailWord_497539
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146738144508650741271671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12097825429672433827514447 18146738144508650741271671)
  ·
    refine ⟨27220107216762976111907507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18146738144508650741271671 27220107216762976111907507)
    ·
      refine ⟨40830160825144464167861261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27220107216762976111907507 40830160825144464167861261)
      ·
        refine ⟨15311310309429174062947973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40830160825144464167861261 15311310309429174062947973)
        ·
          refine ⟨2870870683017970136802745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15311310309429174062947973 2870870683017970136802745)
          ·
            refine ⟨2153153012263477602602059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870870683017970136802745 2153153012263477602602059)
            ·
              refine ⟨3229729518395216403903089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153153012263477602602059 3229729518395216403903089)
              ·
                refine ⟨2422297138796412302927317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229729518395216403903089 2422297138796412302927317)
                ·
                  refine ⟨56772589190540913349859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2422297138796412302927317 56772589190540913349859)
                  ·
                    rfl

theorem cell22_497539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_497539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497539 prefixEnd_497539 := by exact prefixLift 497539
  have htrace : WordTrace (prefixWord ++ tailWord_497539) baseStart_497539 baseEnd_497539 := by
    simpa [prefixWord, tailWord_497539, baseEnd_497539] using wordTrace_append hprefix tailTrace_497539
  have hstable : (prefixWord ++ tailWord_497539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497539).length < 2 ^ (prefixWord ++ tailWord_497539).sum := by decide
  have hdescent : baseEnd_497539 < baseStart_497539 := by decide
  rcases family_descends (prefixWord ++ tailWord_497539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497556 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_497556 : Nat := 118140960795 + 497556 * 2 ^ 59
def prefixEnd_497556 : Nat := 4983230072969 + 3 ^ 40 * 497556 * 2
def baseEnd_497556 : Nat := 56774529006346787458175

theorem tailTrace_497556 : CollatzResearch.WordTrace tailWord_497556 prefixEnd_497556 56774529006346787458175 := by
  unfold tailWord_497556
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073679092723531322320261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12098238790298041763093681 9073679092723531322320261)
  ·
    refine ⟨1701314829885662122935049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9073679092723531322320261 1701314829885662122935049)
    ·
      refine ⟨1275986122414246592201287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1701314829885662122935049 1275986122414246592201287)
      ·
        refine ⟨1913979183621369888301931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275986122414246592201287 1913979183621369888301931)
        ·
          refine ⟨2870968775432054832452897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913979183621369888301931 2870968775432054832452897)
          ·
            refine ⟨2153226581574041124339673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2870968775432054832452897 2153226581574041124339673)
            ·
              refine ⟨1614919936180530843254755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153226581574041124339673 1614919936180530843254755)
              ·
                refine ⟨2422379904270796264882133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614919936180530843254755 2422379904270796264882133)
                ·
                  refine ⟨56774529006346787458175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2422379904270796264882133 56774529006346787458175)
                  ·
                    rfl

theorem cell22_497556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_497556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497556 prefixEnd_497556 := by exact prefixLift 497556
  have htrace : WordTrace (prefixWord ++ tailWord_497556) baseStart_497556 baseEnd_497556 := by
    simpa [prefixWord, tailWord_497556, baseEnd_497556] using wordTrace_append hprefix tailTrace_497556
  have hstable : (prefixWord ++ tailWord_497556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497556).length < 2 ^ (prefixWord ++ tailWord_497556).sum := by decide
  have hdescent : baseEnd_497556 < baseStart_497556 := by decide
  rcases family_descends (prefixWord ++ tailWord_497556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497566 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_497566 : Nat := 118140960795 + 497566 * 2 ^ 59
def prefixEnd_497566 : Nat := 4983230072969 + 3 ^ 40 * 497566 * 2
def baseEnd_497566 : Nat := 170327010223403669624495

theorem tailTrace_497566 : CollatzResearch.WordTrace tailWord_497566 prefixEnd_497566 170327010223403669624495 := by
  unfold tailWord_497566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268465364426354294063069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12098481943607222901669701 2268465364426354294063069)
  ·
    refine ⟨850674511659882860273651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2268465364426354294063069 850674511659882860273651)
    ·
      refine ⟨1276011767489824290410477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850674511659882860273651 1276011767489824290410477)
      ·
        refine ⟨478504412808684108903929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1276011767489824290410477 478504412808684108903929)
        ·
          refine ⟨358878309606513081677947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478504412808684108903929 358878309606513081677947)
          ·
            refine ⟨538317464409769622516921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358878309606513081677947 538317464409769622516921)
            ·
              refine ⟨403738098307327216887691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538317464409769622516921 403738098307327216887691)
              ·
                refine ⟨605607147460990825331537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403738098307327216887691 605607147460990825331537)
                ·
                  refine ⟨454205360595743118998653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605607147460990825331537 454205360595743118998653)
                  ·
                    refine ⟨170327010223403669624495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454205360595743118998653 170327010223403669624495)
                    ·
                      rfl

theorem cell22_497566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_497566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497566 prefixEnd_497566 := by exact prefixLift 497566
  have htrace : WordTrace (prefixWord ++ tailWord_497566) baseStart_497566 baseEnd_497566 := by
    simpa [prefixWord, tailWord_497566, baseEnd_497566] using wordTrace_append hprefix tailTrace_497566
  have hstable : (prefixWord ++ tailWord_497566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497566).length < 2 ^ (prefixWord ++ tailWord_497566).sum := by decide
  have hdescent : baseEnd_497566 < baseStart_497566 := by decide
  rcases family_descends (prefixWord ++ tailWord_497566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497616 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_497616 : Nat := 118140960795 + 497616 * 2 ^ 59
def prefixEnd_497616 : Nat := 4983230072969 + 3 ^ 40 * 497616 * 2
def baseEnd_497616 : Nat := 170344126245220205874341

theorem tailTrace_497616 : CollatzResearch.WordTrace tailWord_497616 prefixEnd_497616 170344126245220205874341 := by
  unfold tailWord_497616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074773282614846445912351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12099697710153128594549801 9074773282614846445912351)
  ·
    refine ⟨13612159923922269668868527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9074773282614846445912351 13612159923922269668868527)
    ·
      refine ⟨20418239885883404503302791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13612159923922269668868527 20418239885883404503302791)
      ·
        refine ⟨30627359828825106754954187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20418239885883404503302791 30627359828825106754954187)
        ·
          refine ⟨45941039743237660132431281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30627359828825106754954187 45941039743237660132431281)
          ·
            refine ⟨34455779807428245099323461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45941039743237660132431281 34455779807428245099323461)
            ·
              refine ⟨6460458713892795956123149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34455779807428245099323461 6460458713892795956123149)
              ·
                refine ⟨2422672017709798483546181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6460458713892795956123149 2422672017709798483546181)
                ·
                  refine ⟨454251003320587215664909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422672017709798483546181 454251003320587215664909)
                  ·
                    refine ⟨170344126245220205874341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454251003320587215664909 170344126245220205874341)
                    ·
                      rfl

theorem cell22_497616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_497616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497616 prefixEnd_497616 := by exact prefixLift 497616
  have htrace : WordTrace (prefixWord ++ tailWord_497616) baseStart_497616 baseEnd_497616 := by
    simpa [prefixWord, tailWord_497616, baseEnd_497616] using wordTrace_append hprefix tailTrace_497616
  have hstable : (prefixWord ++ tailWord_497616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497616).length < 2 ^ (prefixWord ++ tailWord_497616).sum := by decide
  have hdescent : baseEnd_497616 < baseStart_497616 := by decide
  rcases family_descends (prefixWord ++ tailWord_497616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497633 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_497633 : Nat := 118140960795 + 497633 * 2 ^ 59
def prefixEnd_497633 : Nat := 4983230072969 + 3 ^ 40 * 497633 * 2
def baseEnd_497633 : Nat := 170349945692637828199289

theorem tailTrace_497633 : CollatzResearch.WordTrace tailWord_497633 prefixEnd_497633 170349945692637828199289 := by
  unfold tailWord_497633
  simp only [CollatzResearch.WordTrace]
  refine ⟨18150166606168104795193553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12100111070778736530129035 18150166606168104795193553)
  ·
    refine ⟨13612624954626078596395165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18150166606168104795193553 13612624954626078596395165)
    ·
      refine ⟨5104734357984779473648187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13612624954626078596395165 5104734357984779473648187)
      ·
        refine ⟨7657101536977169210472281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104734357984779473648187 7657101536977169210472281)
        ·
          refine ⟨5742826152732876907854211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7657101536977169210472281 5742826152732876907854211)
          ·
            refine ⟨8614239229099315361781317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742826152732876907854211 8614239229099315361781317)
            ·
              refine ⟨1615169855456121630333997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8614239229099315361781317 1615169855456121630333997)
              ·
                refine ⟨605688695796045611375249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1615169855456121630333997 605688695796045611375249)
                ·
                  refine ⟨454266521847034208531437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605688695796045611375249 454266521847034208531437)
                  ·
                    refine ⟨170349945692637828199289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454266521847034208531437 170349945692637828199289)
                    ·
                      rfl

theorem cell22_497633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_497633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497633 prefixEnd_497633 := by exact prefixLift 497633
  have htrace : WordTrace (prefixWord ++ tailWord_497633) baseStart_497633 baseEnd_497633 := by
    simpa [prefixWord, tailWord_497633, baseEnd_497633] using wordTrace_append hprefix tailTrace_497633
  have hstable : (prefixWord ++ tailWord_497633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497633).length < 2 ^ (prefixWord ++ tailWord_497633).sum := by decide
  have hdescent : baseEnd_497633 < baseStart_497633 := by decide
  rcases family_descends (prefixWord ++ tailWord_497633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497654 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_497654 : Nat := 118140960795 + 497654 * 2 ^ 59
def prefixEnd_497654 : Nat := 4983230072969 + 3 ^ 40 * 497654 * 2
def baseEnd_497654 : Nat := 170357134421800773424225

theorem tailTrace_497654 : CollatzResearch.WordTrace tailWord_497654 prefixEnd_497654 170357134421800773424225 := by
  unfold tailWord_497654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134433283693251586356751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12100621692728016921138677 1134433283693251586356751)
  ·
    refine ⟨1701649925539877379535127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134433283693251586356751 1701649925539877379535127)
    ·
      refine ⟨2552474888309816069302691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701649925539877379535127 2552474888309816069302691)
      ·
        refine ⟨3828712332464724103954037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552474888309816069302691 3828712332464724103954037)
        ·
          refine ⟨358941781168567884745691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3828712332464724103954037 358941781168567884745691)
          ·
            refine ⟨538412671752851827118537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358941781168567884745691 538412671752851827118537)
            ·
              refine ⟨403809503814638870338903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538412671752851827118537 403809503814638870338903)
              ·
                refine ⟨605714255721958305508355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403809503814638870338903 605714255721958305508355)
                ·
                  refine ⟨908571383582937458262533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605714255721958305508355 908571383582937458262533)
                  ·
                    refine ⟨170357134421800773424225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908571383582937458262533 170357134421800773424225)
                    ·
                      rfl

theorem cell22_497654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_497654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497654 prefixEnd_497654 := by exact prefixLift 497654
  have htrace : WordTrace (prefixWord ++ tailWord_497654) baseStart_497654 baseEnd_497654 := by
    simpa [prefixWord, tailWord_497654, baseEnd_497654] using wordTrace_append hprefix tailTrace_497654
  have hstable : (prefixWord ++ tailWord_497654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497654).length < 2 ^ (prefixWord ++ tailWord_497654).sum := by decide
  have hdescent : baseEnd_497654 < baseStart_497654 := by decide
  rcases family_descends (prefixWord ++ tailWord_497654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497684 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_497684 : Nat := 118140960795 + 497684 * 2 ^ 59
def prefixEnd_497684 : Nat := 4983230072969 + 3 ^ 40 * 497684 * 2
def baseEnd_497684 : Nat := 170367404034890695174133

theorem tailTrace_497684 : CollatzResearch.WordTrace tailWord_497684 prefixEnd_497684 170367404034890695174133 := by
  unfold tailWord_497684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076013364491670252650053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12101351152655560336866737 9076013364491670252650053)
  ·
    refine ⟨1701752505842188172371885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9076013364491670252650053 1701752505842188172371885)
    ·
      refine ⟨638157189690820564639457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1701752505842188172371885 638157189690820564639457)
      ·
        refine ⟨478617892268115423479593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638157189690820564639457 478617892268115423479593)
        ·
          refine ⟨358963419201086567609695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478617892268115423479593 358963419201086567609695)
          ·
            refine ⟨538445128801629851414543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358963419201086567609695 538445128801629851414543)
            ·
              refine ⟨807667693202444777121815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538445128801629851414543 807667693202444777121815)
              ·
                refine ⟨1211501539803667165682723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807667693202444777121815 1211501539803667165682723)
                ·
                  refine ⟨1817252309705500748524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211501539803667165682723 1817252309705500748524085)
                  ·
                    refine ⟨170367404034890695174133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1817252309705500748524085 170367404034890695174133)
                    ·
                      rfl

theorem cell22_497684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_497684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497684 prefixEnd_497684 := by exact prefixLift 497684
  have htrace : WordTrace (prefixWord ++ tailWord_497684) baseStart_497684 baseEnd_497684 := by
    simpa [prefixWord, tailWord_497684, baseEnd_497684] using wordTrace_append hprefix tailTrace_497684
  have hstable : (prefixWord ++ tailWord_497684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497684).length < 2 ^ (prefixWord ++ tailWord_497684).sum := by decide
  have hdescent : baseEnd_497684 < baseStart_497684 := by decide
  rcases family_descends (prefixWord ++ tailWord_497684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497712 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_497712 : Nat := 118140960795 + 497712 * 2 ^ 59
def prefixEnd_497712 : Nat := 4983230072969 + 3 ^ 40 * 497712 * 2
def baseEnd_497712 : Nat := 170376989007107955474047

theorem tailTrace_497712 : CollatzResearch.WordTrace tailWord_497712 prefixEnd_497712 170376989007107955474047 := by
  unfold tailWord_497712
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076523986440950643659695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12102031981921267524879593 9076523986440950643659695)
  ·
    refine ⟨13614785979661425965489543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076523986440950643659695 13614785979661425965489543)
    ·
      refine ⟨20422178969492138948234315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13614785979661425965489543 20422178969492138948234315)
      ·
        refine ⟨30633268454238208422351473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20422178969492138948234315 30633268454238208422351473)
        ·
          refine ⟨22974951340678656316763605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30633268454238208422351473 22974951340678656316763605)
          ·
            refine ⟨538475422047156007424147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22974951340678656316763605 538475422047156007424147)
            ·
              refine ⟨807713133070734011136221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538475422047156007424147 807713133070734011136221)
              ·
                refine ⟨302892424901525254176083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807713133070734011136221 302892424901525254176083)
                ·
                  refine ⟨454338637352287881264125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302892424901525254176083 454338637352287881264125)
                  ·
                    refine ⟨170376989007107955474047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454338637352287881264125 170376989007107955474047)
                    ·
                      rfl

theorem cell22_497712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_497712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497712 prefixEnd_497712 := by exact prefixLift 497712
  have htrace : WordTrace (prefixWord ++ tailWord_497712) baseStart_497712 baseEnd_497712 := by
    simpa [prefixWord, tailWord_497712, baseEnd_497712] using wordTrace_append hprefix tailTrace_497712
  have hstable : (prefixWord ++ tailWord_497712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497712).length < 2 ^ (prefixWord ++ tailWord_497712).sum := by decide
  have hdescent : baseEnd_497712 < baseStart_497712 := by decide
  rcases family_descends (prefixWord ++ tailWord_497712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497729 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_497729 : Nat := 118140960795 + 497729 * 2 ^ 59
def prefixEnd_497729 : Nat := 4983230072969 + 3 ^ 40 * 497729 * 2
def baseEnd_497729 : Nat := 170382808454525577798995

theorem tailTrace_497729 : CollatzResearch.WordTrace tailWord_497729 prefixEnd_497729 170382808454525577798995 := by
  unfold tailWord_497729
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153668013820313190688241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12102445342546875460458827 18153668013820313190688241)
  ·
    refine ⟨13615251010365234893016181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18153668013820313190688241 13615251010365234893016181)
    ·
      refine ⟨1276429782221740771220267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13615251010365234893016181 1276429782221740771220267)
      ·
        refine ⟨1914644673332611156830401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276429782221740771220267 1914644673332611156830401)
        ·
          refine ⟨1435983504999458367622801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914644673332611156830401 1435983504999458367622801)
          ·
            refine ⟨1076987628749593775717101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435983504999458367622801 1076987628749593775717101)
            ·
              refine ⟨403870360781097665893913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076987628749593775717101 403870360781097665893913)
              ·
                refine ⟨302902770585823249420435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403870360781097665893913 302902770585823249420435)
                ·
                  refine ⟨454354155878734874130653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302902770585823249420435 454354155878734874130653)
                  ·
                    refine ⟨170382808454525577798995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454354155878734874130653 170382808454525577798995)
                    ·
                      rfl

theorem cell22_497729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_497729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497729 prefixEnd_497729 := by exact prefixLift 497729
  have htrace : WordTrace (prefixWord ++ tailWord_497729) baseStart_497729 baseEnd_497729 := by
    simpa [prefixWord, tailWord_497729, baseEnd_497729] using wordTrace_append hprefix tailTrace_497729
  have hstable : (prefixWord ++ tailWord_497729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497729).length < 2 ^ (prefixWord ++ tailWord_497729).sum := by decide
  have hdescent : baseEnd_497729 < baseStart_497729 := by decide
  rcases family_descends (prefixWord ++ tailWord_497729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497736 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_497736 : Nat := 118140960795 + 497736 * 2 ^ 59
def prefixEnd_497736 : Nat := 4983230072969 + 3 ^ 40 * 497736 * 2
def baseEnd_497736 : Nat := 56795068232526630957991

theorem tailTrace_497736 : CollatzResearch.WordTrace tailWord_497736 prefixEnd_497736 56795068232526630957991 := by
  unfold tailWord_497736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076961662397476693096531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12102615549863302257462041 9076961662397476693096531)
  ·
    refine ⟨13615442493596215039644797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076961662397476693096531 13615442493596215039644797)
    ·
      refine ⟨5105790935098580639866799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13615442493596215039644797 5105790935098580639866799)
      ·
        refine ⟨7658686402647870959800199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105790935098580639866799 7658686402647870959800199)
        ·
          refine ⟨11488029603971806439700299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658686402647870959800199 11488029603971806439700299)
          ·
            refine ⟨17232044405957709659550449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11488029603971806439700299 17232044405957709659550449)
            ·
              refine ⟨12924033304468282244662837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17232044405957709659550449 12924033304468282244662837)
              ·
                refine ⟨1211628122293901460437141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12924033304468282244662837 1211628122293901460437141)
                ·
                  refine ⟨56795068232526630957991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1211628122293901460437141 56795068232526630957991)
                  ·
                    rfl

theorem cell22_497736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_497736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497736 prefixEnd_497736 := by exact prefixLift 497736
  have htrace : WordTrace (prefixWord ++ tailWord_497736) baseStart_497736 baseEnd_497736 := by
    simpa [prefixWord, tailWord_497736, baseEnd_497736] using wordTrace_append hprefix tailTrace_497736
  have hstable : (prefixWord ++ tailWord_497736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497736).length < 2 ^ (prefixWord ++ tailWord_497736).sum := by decide
  have hdescent : baseEnd_497736 < baseStart_497736 := by decide
  rcases family_descends (prefixWord ++ tailWord_497736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497781 : List Nat := [1, 3, 4, 14]
def baseStart_497781 : Nat := 118140960795 + 497781 * 2 ^ 59
def prefixEnd_497781 : Nat := 4983230072969 + 3 ^ 40 * 497781 * 2
def baseEnd_497781 : Nat := 233745691518813135115

theorem tailTrace_497781 : CollatzResearch.WordTrace tailWord_497781 prefixEnd_497781 233745691518813135115 := by
  unfold tailWord_497781
  simp only [CollatzResearch.WordTrace]
  refine ⟨18155564609631926071581197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12103709739754617381054131 18155564609631926071581197)
  ·
    refine ⟨6808336728611972276842949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18155564609631926071581197 6808336728611972276842949)
    ·
      refine ⟨1276563136614744801908053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6808336728611972276842949 1276563136614744801908053)
      ·
        refine ⟨233745691518813135115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1276563136614744801908053 233745691518813135115)
        ·
          rfl

theorem cell22_497781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 14].length) (baseStart_497781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497781 prefixEnd_497781 := by exact prefixLift 497781
  have htrace : WordTrace (prefixWord ++ tailWord_497781) baseStart_497781 baseEnd_497781 := by
    simpa [prefixWord, tailWord_497781, baseEnd_497781] using wordTrace_append hprefix tailTrace_497781
  have hstable : (prefixWord ++ tailWord_497781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497781).length < 2 ^ (prefixWord ++ tailWord_497781).sum := by decide
  have hdescent : baseEnd_497781 < baseStart_497781 := by decide
  rcases family_descends (prefixWord ++ tailWord_497781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497783 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_497783 : Nat := 118140960795 + 497783 * 2 ^ 59
def prefixEnd_497783 : Nat := 4983230072969 + 3 ^ 40 * 497783 * 2
def baseEnd_497783 : Nat := 170401293758087436948829

theorem tailTrace_497783 : CollatzResearch.WordTrace tailWord_497783 prefixEnd_497783 170401293758087436948829 := by
  unfold tailWord_497783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18155637555624680413154003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12103758370416453608769335 18155637555624680413154003)
  ·
    refine ⟨27233456333437020619731005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18155637555624680413154003 27233456333437020619731005)
    ·
      refine ⟨10212546125038882732399127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27233456333437020619731005 10212546125038882732399127)
      ·
        refine ⟨15318819187558324098598691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10212546125038882732399127 15318819187558324098598691)
        ·
          refine ⟨22978228781337486147898037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15318819187558324098598691 22978228781337486147898037)
          ·
            refine ⟨2154208948250389326365441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22978228781337486147898037 2154208948250389326365441)
            ·
              refine ⟨1615656711187791994774081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154208948250389326365441 1615656711187791994774081)
              ·
                refine ⟨1211742533390843996080561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615656711187791994774081 1211742533390843996080561)
                ·
                  refine ⟨908806900043132997060421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211742533390843996080561 908806900043132997060421)
                  ·
                    refine ⟨170401293758087436948829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908806900043132997060421 170401293758087436948829)
                    ·
                      rfl

theorem cell22_497783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_497783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497783 prefixEnd_497783 := by exact prefixLift 497783
  have htrace : WordTrace (prefixWord ++ tailWord_497783) baseStart_497783 baseEnd_497783 := by
    simpa [prefixWord, tailWord_497783, baseEnd_497783] using wordTrace_append hprefix tailTrace_497783
  have hstable : (prefixWord ++ tailWord_497783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497783).length < 2 ^ (prefixWord ++ tailWord_497783).sum := by decide
  have hdescent : baseEnd_497783 < baseStart_497783 := by decide
  rcases family_descends (prefixWord ++ tailWord_497783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497785 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_497785 : Nat := 118140960795 + 497785 * 2 ^ 59
def prefixEnd_497785 : Nat := 4983230072969 + 3 ^ 40 * 497785 * 2
def baseEnd_497785 : Nat := 170401978398960098398823

theorem tailTrace_497785 : CollatzResearch.WordTrace tailWord_497785 prefixEnd_497785 170401978398960098398823 := by
  unfold tailWord_497785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18155710501617434754726809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12103807001078289836484539 18155710501617434754726809)
  ·
    refine ⟨13616782876213076066045107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18155710501617434754726809 13616782876213076066045107)
    ·
      refine ⟨20425174314319614099067661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616782876213076066045107 20425174314319614099067661)
      ·
        refine ⟨7659440367869855287150373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20425174314319614099067661 7659440367869855287150373)
        ·
          refine ⟨1436145068975597866340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7659440367869855287150373 1436145068975597866340695)
          ·
            refine ⟨2154217603463396799511043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436145068975597866340695 2154217603463396799511043)
            ·
              refine ⟨3231326405195095199266565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154217603463396799511043 3231326405195095199266565)
              ·
                refine ⟨605873700974080349862481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3231326405195095199266565 605873700974080349862481)
                ·
                  refine ⟨454405275730560262396861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605873700974080349862481 454405275730560262396861)
                  ·
                    refine ⟨170401978398960098398823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454405275730560262396861 170401978398960098398823)
                    ·
                      rfl

theorem cell22_497785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_497785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497785 prefixEnd_497785 := by exact prefixLift 497785
  have htrace : WordTrace (prefixWord ++ tailWord_497785) baseStart_497785 baseEnd_497785 := by
    simpa [prefixWord, tailWord_497785, baseEnd_497785] using wordTrace_append hprefix tailTrace_497785
  have hstable : (prefixWord ++ tailWord_497785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497785).length < 2 ^ (prefixWord ++ tailWord_497785).sum := by decide
  have hdescent : baseEnd_497785 < baseStart_497785 := by decide
  rcases family_descends (prefixWord ++ tailWord_497785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497811 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_497811 : Nat := 118140960795 + 497811 * 2 ^ 59
def prefixEnd_497811 : Nat := 4983230072969 + 3 ^ 40 * 497811 * 2
def baseEnd_497811 : Nat := 170410878730304697248743

theorem tailTrace_497811 : CollatzResearch.WordTrace tailWord_497811 prefixEnd_497811 170410878730304697248743 := by
  unfold tailWord_497811
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156658799523241195173287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12104439199682160796782191 18156658799523241195173287)
  ·
    refine ⟨27234988199284861792759931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18156658799523241195173287 27234988199284861792759931)
    ·
      refine ⟨40852482298927292689139897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27234988199284861792759931 40852482298927292689139897)
      ·
        refine ⟨30639361724195469516854923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40852482298927292689139897 30639361724195469516854923)
        ·
          refine ⟨45959042586293204275282385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30639361724195469516854923 45959042586293204275282385)
          ·
            refine ⟨34469281939719903206461789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45959042586293204275282385 34469281939719903206461789)
            ·
              refine ⟨12925980727394963702423171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34469281939719903206461789 12925980727394963702423171)
              ·
                refine ⟨19388971091092445553634757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12925980727394963702423171 19388971091092445553634757)
                ·
                  refine ⟨3635432079579833541306517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19388971091092445553634757 3635432079579833541306517)
                  ·
                    refine ⟨170410878730304697248743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3635432079579833541306517 170410878730304697248743)
                    ·
                      rfl

theorem cell22_497811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_497811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497811 prefixEnd_497811 := by exact prefixLift 497811
  have htrace : WordTrace (prefixWord ++ tailWord_497811) baseStart_497811 baseEnd_497811 := by
    simpa [prefixWord, tailWord_497811, baseEnd_497811] using wordTrace_append hprefix tailTrace_497811
  have hstable : (prefixWord ++ tailWord_497811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497811).length < 2 ^ (prefixWord ++ tailWord_497811).sum := by decide
  have hdescent : baseEnd_497811 < baseStart_497811 := by decide
  rcases family_descends (prefixWord ++ tailWord_497811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497815 : List Nat := [1, 1, 3, 3, 4, 1, 3, 6]
def baseStart_497815 : Nat := 118140960795 + 497815 * 2 ^ 59
def prefixEnd_497815 : Nat := 4983230072969 + 3 ^ 40 * 497815 * 2
def baseEnd_497815 : Nat := 18934694223561113349859

theorem tailTrace_497815 : CollatzResearch.WordTrace tailWord_497815 prefixEnd_497815 18934694223561113349859 := by
  unfold tailWord_497815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18156804691508749878318899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12104536461005833252212599 18156804691508749878318899)
  ·
    refine ⟨27235207037263124817478349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18156804691508749878318899 27235207037263124817478349)
    ·
      refine ⟨10213202638973671806554381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27235207037263124817478349 10213202638973671806554381)
      ·
        refine ⟨3829950989615126927457893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10213202638973671806554381 3829950989615126927457893)
        ·
          refine ⟨718115810552836298898355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3829950989615126927457893 718115810552836298898355)
          ·
            refine ⟨1077173715829254448347533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718115810552836298898355 1077173715829254448347533)
            ·
              refine ⟨403940143435970418130325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077173715829254448347533 403940143435970418130325)
              ·
                refine ⟨18934694223561113349859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 403940143435970418130325 18934694223561113349859)
                ·
                  rfl

theorem cell22_497815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 6].length) (baseStart_497815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497815 prefixEnd_497815 := by exact prefixLift 497815
  have htrace : WordTrace (prefixWord ++ tailWord_497815) baseStart_497815 baseEnd_497815 := by
    simpa [prefixWord, tailWord_497815, baseEnd_497815] using wordTrace_append hprefix tailTrace_497815
  have hstable : (prefixWord ++ tailWord_497815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497815).length < 2 ^ (prefixWord ++ tailWord_497815).sum := by decide
  have hdescent : baseEnd_497815 < baseStart_497815 := by decide
  rcases family_descends (prefixWord ++ tailWord_497815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497847 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 1, 3]
def baseStart_497847 : Nat := 118140960795 + 497847 * 2 ^ 59
def prefixEnd_497847 : Nat := 4983230072969 + 3 ^ 40 * 497847 * 2
def baseEnd_497847 : Nat := 170423202266012603348633

theorem tailTrace_497847 : CollatzResearch.WordTrace tailWord_497847 prefixEnd_497847 170423202266012603348633 := by
  unfold tailWord_497847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157971827392819343483795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12105314551595212895655863 18157971827392819343483795)
  ·
    refine ⟨27236957741089229015225693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18157971827392819343483795 27236957741089229015225693)
    ·
      refine ⟨10213859152908460880709635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27236957741089229015225693 10213859152908460880709635)
      ·
        refine ⟨15320788729362691321064453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213859152908460880709635 15320788729362691321064453)
        ·
          refine ⟨2872647886755504622699585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15320788729362691321064453 2872647886755504622699585)
          ·
            refine ⟨2154485915066628467024689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2872647886755504622699585 2154485915066628467024689)
            ·
              refine ⟨1615864436299971350268517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154485915066628467024689 1615864436299971350268517)
              ·
                refine ⟨302974581806244628175347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1615864436299971350268517 302974581806244628175347)
                ·
                  refine ⟨454461872709366942263021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302974581806244628175347 454461872709366942263021)
                  ·
                    refine ⟨170423202266012603348633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454461872709366942263021 170423202266012603348633)
                    ·
                      rfl

theorem cell22_497847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_497847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497847 prefixEnd_497847 := by exact prefixLift 497847
  have htrace : WordTrace (prefixWord ++ tailWord_497847) baseStart_497847 baseEnd_497847 := by
    simpa [prefixWord, tailWord_497847, baseEnd_497847] using wordTrace_append hprefix tailTrace_497847
  have hstable : (prefixWord ++ tailWord_497847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497847).length < 2 ^ (prefixWord ++ tailWord_497847).sum := by decide
  have hdescent : baseEnd_497847 < baseStart_497847 := by decide
  rcases family_descends (prefixWord ++ tailWord_497847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497873 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_497873 : Nat := 118140960795 + 497873 * 2 ^ 59
def prefixEnd_497873 : Nat := 4983230072969 + 3 ^ 40 * 497873 * 2
def baseEnd_497873 : Nat := 170432102597357202198553

theorem tailTrace_497873 : CollatzResearch.WordTrace tailWord_497873 prefixEnd_497873 170432102597357202198553 := by
  unfold tailWord_497873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158920125298625783930273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12105946750199083855953515 18158920125298625783930273)
  ·
    refine ⟨13619190093973969337947705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18158920125298625783930273 13619190093973969337947705)
    ·
      refine ⟨10214392570480477003460779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13619190093973969337947705 10214392570480477003460779)
      ·
        refine ⟨15321588855720715505191169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214392570480477003460779 15321588855720715505191169)
        ·
          refine ⟨11491191641790536628893377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15321588855720715505191169 11491191641790536628893377)
          ·
            refine ⟨8618393731342902471670033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11491191641790536628893377 8618393731342902471670033)
            ·
              refine ⟨6463795298507176853752525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618393731342902471670033 6463795298507176853752525)
              ·
                refine ⟨2423923236940191320157197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6463795298507176853752525 2423923236940191320157197)
                ·
                  refine ⟨908971213852571745058949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2423923236940191320157197 908971213852571745058949)
                  ·
                    refine ⟨170432102597357202198553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 908971213852571745058949 170432102597357202198553)
                    ·
                      rfl

theorem cell22_497873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_497873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497873 prefixEnd_497873 := by exact prefixLift 497873
  have htrace : WordTrace (prefixWord ++ tailWord_497873) baseStart_497873 baseEnd_497873 := by
    simpa [prefixWord, tailWord_497873, baseEnd_497873] using wordTrace_append hprefix tailTrace_497873
  have hstable : (prefixWord ++ tailWord_497873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497873).length < 2 ^ (prefixWord ++ tailWord_497873).sum := by decide
  have hdescent : baseEnd_497873 < baseStart_497873 := by decide
  rcases family_descends (prefixWord ++ tailWord_497873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497905 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 4]
def baseStart_497905 : Nat := 118140960795 + 497905 * 2 ^ 59
def prefixEnd_497905 : Nat := 4983230072969 + 3 ^ 40 * 497905 * 2
def baseEnd_497905 : Nat := 56814352283773261799485

theorem tailTrace_497905 : CollatzResearch.WordTrace tailWord_497905 prefixEnd_497905 56814352283773261799485 := by
  unfold tailWord_497905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18160087261182695249095169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106724840788463499396779 18160087261182695249095169)
  ·
    refine ⟨13620065445887021436821377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18160087261182695249095169 13620065445887021436821377)
    ·
      refine ⟨10215049084415266077616033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13620065445887021436821377 10215049084415266077616033)
      ·
        refine ⟨7661286813311449558212025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10215049084415266077616033 7661286813311449558212025)
        ·
          refine ⟨5745965109983587168659019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7661286813311449558212025 5745965109983587168659019)
          ·
            refine ⟨8618947664975380752988529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745965109983587168659019 8618947664975380752988529)
            ·
              refine ⟨6464210748731535564741397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618947664975380752988529 6464210748731535564741397)
              ·
                refine ⟨303009878846790729597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6464210748731535564741397 303009878846790729597253)
                ·
                  refine ⟨56814352283773261799485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303009878846790729597253 56814352283773261799485)
                  ·
                    rfl

theorem cell22_497905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_497905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497905 prefixEnd_497905 := by exact prefixLift 497905
  have htrace : WordTrace (prefixWord ++ tailWord_497905) baseStart_497905 baseEnd_497905 := by
    simpa [prefixWord, tailWord_497905, baseEnd_497905] using wordTrace_append hprefix tailTrace_497905
  have hstable : (prefixWord ++ tailWord_497905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497905).length < 2 ^ (prefixWord ++ tailWord_497905).sum := by decide
  have hdescent : baseEnd_497905 < baseStart_497905 := by decide
  rcases family_descends (prefixWord ++ tailWord_497905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497924 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_497924 : Nat := 118140960795 + 497924 * 2 ^ 59
def prefixEnd_497924 : Nat := 4983230072969 + 3 ^ 40 * 497924 * 2
def baseEnd_497924 : Nat := 170449560939610069173397

theorem tailTrace_497924 : CollatzResearch.WordTrace tailWord_497924 prefixEnd_497924 170449560939610069173397 := by
  unfold tailWord_497924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080390124056930747018413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12107186832075907662691217 9080390124056930747018413)
  ·
    refine ⟨3405146296521349030131905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9080390124056930747018413 3405146296521349030131905)
    ·
      refine ⟨2553859722391011772598929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405146296521349030131905 2553859722391011772598929)
      ·
        refine ⟨1915394791793258829449197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553859722391011772598929 1915394791793258829449197)
        ·
          refine ⟨718273046922472061043449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1915394791793258829449197 718273046922472061043449)
          ·
            refine ⟨538704785191854045782587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718273046922472061043449 538704785191854045782587)
            ·
              refine ⟨808057177787781068673881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538704785191854045782587 808057177787781068673881)
              ·
                refine ⟨606042883340835801505411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808057177787781068673881 606042883340835801505411)
                ·
                  refine ⟨909064325011253702258117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606042883340835801505411 909064325011253702258117)
                  ·
                    refine ⟨170449560939610069173397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909064325011253702258117 170449560939610069173397)
                    ·
                      rfl

theorem cell22_497924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_497924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497924 prefixEnd_497924 := by exact prefixLift 497924
  have htrace : WordTrace (prefixWord ++ tailWord_497924) baseStart_497924 baseEnd_497924 := by
    simpa [prefixWord, tailWord_497924, baseEnd_497924] using wordTrace_append hprefix tailTrace_497924
  have hstable : (prefixWord ++ tailWord_497924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497924).length < 2 ^ (prefixWord ++ tailWord_497924).sum := by decide
  have hdescent : baseEnd_497924 < baseStart_497924 := by decide
  rcases family_descends (prefixWord ++ tailWord_497924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497954 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_497954 : Nat := 118140960795 + 497954 * 2 ^ 59
def prefixEnd_497954 : Nat := 4983230072969 + 3 ^ 40 * 497954 * 2
def baseEnd_497954 : Nat := 170459830552699990923305

theorem tailTrace_497954 : CollatzResearch.WordTrace tailWord_497954 prefixEnd_497954 170459830552699990923305 := by
  unfold tailWord_497954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540468609501294154407229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12107916292003451078419277 4540468609501294154407229)
  ·
    refine ⟨1702675728562985307902711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4540468609501294154407229 1702675728562985307902711)
    ·
      refine ⟨2554013592844477961854067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702675728562985307902711 2554013592844477961854067)
      ·
        refine ⟨3831020389266716942781101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554013592844477961854067 3831020389266716942781101)
        ·
          refine ⟨1436632645975018853542913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3831020389266716942781101 1436632645975018853542913)
          ·
            refine ⟨1077474484481264140157185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436632645975018853542913 1077474484481264140157185)
            ·
              refine ⟨808105863360948105117889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077474484481264140157185 808105863360948105117889)
              ·
                refine ⟨606079397520711078838417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808105863360948105117889 606079397520711078838417)
                ·
                  refine ⟨454559548140533309128813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606079397520711078838417 454559548140533309128813)
                  ·
                    refine ⟨170459830552699990923305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454559548140533309128813 170459830552699990923305)
                    ·
                      rfl

theorem cell22_497954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_497954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497954 prefixEnd_497954 := by exact prefixLift 497954
  have htrace : WordTrace (prefixWord ++ tailWord_497954) baseStart_497954 baseEnd_497954 := by
    simpa [prefixWord, tailWord_497954, baseEnd_497954] using wordTrace_append hprefix tailTrace_497954
  have hstable : (prefixWord ++ tailWord_497954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497954).length < 2 ^ (prefixWord ++ tailWord_497954).sum := by decide
  have hdescent : baseEnd_497954 < baseStart_497954 := by decide
  rcases family_descends (prefixWord ++ tailWord_497954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497982 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_497982 : Nat := 118140960795 + 497982 * 2 ^ 59
def prefixEnd_497982 : Nat := 4983230072969 + 3 ^ 40 * 497982 * 2
def baseEnd_497982 : Nat := 170469415524917251223219

theorem tailTrace_497982 : CollatzResearch.WordTrace tailWord_497982 prefixEnd_497982 170469415524917251223219 := by
  unfold tailWord_497982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270361960237967174956025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12108597121269158266432133 2270361960237967174956025)
  ·
    refine ⟨1702771470178475381217019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2270361960237967174956025 1702771470178475381217019)
    ·
      refine ⟨2554157205267713071825529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702771470178475381217019 2554157205267713071825529)
      ·
        refine ⟨1915617903950784803869147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554157205267713071825529 1915617903950784803869147)
        ·
          refine ⟨2873426855926177205803721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915617903950784803869147 2873426855926177205803721)
          ·
            refine ⟨2155070141944632904352791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873426855926177205803721 2155070141944632904352791)
            ·
              refine ⟨3232605212916949356529187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155070141944632904352791 3232605212916949356529187)
              ·
                refine ⟨4848907819375424034793781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232605212916949356529187 4848907819375424034793781)
                ·
                  refine ⟨454585108066446003261917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4848907819375424034793781 454585108066446003261917)
                  ·
                    refine ⟨170469415524917251223219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454585108066446003261917 170469415524917251223219)
                    ·
                      rfl

theorem cell22_497982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_497982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497982 prefixEnd_497982 := by exact prefixLift 497982
  have htrace : WordTrace (prefixWord ++ tailWord_497982) baseStart_497982 baseEnd_497982 := by
    simpa [prefixWord, tailWord_497982, baseEnd_497982] using wordTrace_append hprefix tailTrace_497982
  have hstable : (prefixWord ++ tailWord_497982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497982).length < 2 ^ (prefixWord ++ tailWord_497982).sum := by decide
  have hdescent : baseEnd_497982 < baseStart_497982 := by decide
  rcases family_descends (prefixWord ++ tailWord_497982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_497993 : Nat := 118140960795 + 497993 * 2 ^ 59
def prefixEnd_497993 : Nat := 4983230072969 + 3 ^ 40 * 497993 * 2
def baseEnd_497993 : Nat := 170473181049716889198185

theorem tailTrace_497993 : CollatzResearch.WordTrace tailWord_497993 prefixEnd_497993 170473181049716889198185 := by
  unfold tailWord_497993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163296884863886278298633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12108864589909257518865755 18163296884863886278298633)
  ·
    refine ⟨13622472663647914708723975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18163296884863886278298633 13622472663647914708723975)
    ·
      refine ⟨20433708995471872063085963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622472663647914708723975 20433708995471872063085963)
      ·
        refine ⟨30650563493207808094628945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433708995471872063085963 30650563493207808094628945)
        ·
          refine ⟨22987922619905856070971709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30650563493207808094628945 22987922619905856070971709)
          ·
            refine ⟨8620470982464696026614391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22987922619905856070971709 8620470982464696026614391)
            ·
              refine ⟨12930706473697044039921587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8620470982464696026614391 12930706473697044039921587)
              ·
                refine ⟨19396059710545566059882381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12930706473697044039921587 19396059710545566059882381)
                ·
                  refine ⟨7273522391454587272455893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19396059710545566059882381 7273522391454587272455893)
                  ·
                    refine ⟨170473181049716889198185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7273522391454587272455893 170473181049716889198185)
                    ·
                      rfl

theorem cell22_497993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_497993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_497993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_497993 prefixEnd_497993 := by exact prefixLift 497993
  have htrace : WordTrace (prefixWord ++ tailWord_497993) baseStart_497993 baseEnd_497993 := by
    simpa [prefixWord, tailWord_497993, baseEnd_497993] using wordTrace_append hprefix tailTrace_497993
  have hstable : (prefixWord ++ tailWord_497993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497993).length < 2 ^ (prefixWord ++ tailWord_497993).sum := by decide
  have hdescent : baseEnd_497993 < baseStart_497993 := by decide
  rcases family_descends (prefixWord ++ tailWord_497993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498050 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_498050 : Nat := 118140960795 + 498050 * 2 ^ 59
def prefixEnd_498050 : Nat := 4983230072969 + 3 ^ 40 * 498050 * 2
def baseEnd_498050 : Nat := 170492693314587740523011

theorem tailTrace_498050 : CollatzResearch.WordTrace tailWord_498050 prefixEnd_498050 170492693314587740523011 := by
  unfold tailWord_498050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541343961414346253280901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12110250563771590008749069 4541343961414346253280901)
  ·
    refine ⟨851501992765189922490169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4541343961414346253280901 851501992765189922490169)
    ·
      refine ⟨638626494573892441867627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 851501992765189922490169 638626494573892441867627)
      ·
        refine ⟨957939741860838662801441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638626494573892441867627 957939741860838662801441)
        ·
          refine ⟨718454806395628997101081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957939741860838662801441 718454806395628997101081)
          ·
            refine ⟨538841104796721747825811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718454806395628997101081 538841104796721747825811)
            ·
              refine ⟨808261657195082621738717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538841104796721747825811 808261657195082621738717)
              ·
                refine ⟨303098121448155983152019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808261657195082621738717 303098121448155983152019)
                ·
                  refine ⟨454647182172233974728029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303098121448155983152019 454647182172233974728029)
                  ·
                    refine ⟨170492693314587740523011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 454647182172233974728029 170492693314587740523011)
                    ·
                      rfl

theorem cell22_498050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_498050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498050 prefixEnd_498050 := by exact prefixLift 498050
  have htrace : WordTrace (prefixWord ++ tailWord_498050) baseStart_498050 baseEnd_498050 := by
    simpa [prefixWord, tailWord_498050, baseEnd_498050] using wordTrace_append hprefix tailTrace_498050
  have hstable : (prefixWord ++ tailWord_498050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498050).length < 2 ^ (prefixWord ++ tailWord_498050).sum := by decide
  have hdescent : baseEnd_498050 < baseStart_498050 := by decide
  rcases family_descends (prefixWord ++ tailWord_498050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498055 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_498055 : Nat := 118140960795 + 498055 * 2 ^ 59
def prefixEnd_498055 : Nat := 4983230072969 + 3 ^ 40 * 498055 * 2
def baseEnd_498055 : Nat := 170494404916769394147995

theorem tailTrace_498055 : CollatzResearch.WordTrace tailWord_498055 prefixEnd_498055 170494404916769394147995 := by
  unfold tailWord_498055
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165558210639270867055619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12110372140426180578037079 18165558210639270867055619)
  ·
    refine ⟨27248337315958906300583429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18165558210639270867055619 27248337315958906300583429)
    ·
      refine ⟨5109063246742294931359393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27248337315958906300583429 5109063246742294931359393)
      ·
        refine ⟨3831797435056721198519545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5109063246742294931359393 3831797435056721198519545)
        ·
          refine ⟨2873848076292540898889659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831797435056721198519545 2873848076292540898889659)
          ·
            refine ⟨4310772114438811348334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873848076292540898889659 4310772114438811348334489)
            ·
              refine ⟨3233079085829108511250867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310772114438811348334489 3233079085829108511250867)
              ·
                refine ⟨4849618628743662766876301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233079085829108511250867 4849618628743662766876301)
                ·
                  refine ⟨1818606985778873537578613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4849618628743662766876301 1818606985778873537578613)
                  ·
                    refine ⟨170494404916769394147995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1818606985778873537578613 170494404916769394147995)
                    ·
                      rfl

theorem cell22_498055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_498055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498055 prefixEnd_498055 := by exact prefixLift 498055
  have htrace : WordTrace (prefixWord ++ tailWord_498055) baseStart_498055 baseEnd_498055 := by
    simpa [prefixWord, tailWord_498055, baseEnd_498055] using wordTrace_append hprefix tailTrace_498055
  have hstable : (prefixWord ++ tailWord_498055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498055).length < 2 ^ (prefixWord ++ tailWord_498055).sum := by decide
  have hdescent : baseEnd_498055 < baseStart_498055 := by decide
  rcases family_descends (prefixWord ++ tailWord_498055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498085 : List Nat := [1, 3, 1, 2, 1, 1, 6, 7]
def baseStart_498085 : Nat := 118140960795 + 498085 * 2 ^ 59
def prefixEnd_498085 : Nat := 4983230072969 + 3 ^ 40 * 498085 * 2
def baseEnd_498085 : Nat := 18944963836651035099767

theorem tailTrace_498085 : CollatzResearch.WordTrace tailWord_498085 prefixEnd_498085 18944963836651035099767 := by
  unfold tailWord_498085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166652400530585990647709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12111101600353723993765139 18166652400530585990647709)
  ·
    refine ⟨6812494650198969746492891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18166652400530585990647709 6812494650198969746492891)
    ·
      refine ⟨10218741975298454619739337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812494650198969746492891 10218741975298454619739337)
      ·
        refine ⟨7664056481473840964804503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10218741975298454619739337 7664056481473840964804503)
        ·
          refine ⟨11496084722210761447206755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664056481473840964804503 11496084722210761447206755)
          ·
            refine ⟨17244127083316142170810133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496084722210761447206755 17244127083316142170810133)
            ·
              refine ⟨808318457030444164256725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17244127083316142170810133 808318457030444164256725)
              ·
                refine ⟨18944963836651035099767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 808318457030444164256725 18944963836651035099767)
                ·
                  rfl

theorem cell22_498085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 7].length) (baseStart_498085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498085 prefixEnd_498085 := by exact prefixLift 498085
  have htrace : WordTrace (prefixWord ++ tailWord_498085) baseStart_498085 baseEnd_498085 := by
    simpa [prefixWord, tailWord_498085, baseEnd_498085] using wordTrace_append hprefix tailTrace_498085
  have hstable : (prefixWord ++ tailWord_498085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498085).length < 2 ^ (prefixWord ++ tailWord_498085).sum := by decide
  have hdescent : baseEnd_498085 < baseStart_498085 := by decide
  rcases family_descends (prefixWord ++ tailWord_498085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498093 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_498093 : Nat := 118140960795 + 498093 * 2 ^ 59
def prefixEnd_498093 : Nat := 4983230072969 + 3 ^ 40 * 498093 * 2
def baseEnd_498093 : Nat := 170507413093349961697879

theorem tailTrace_498093 : CollatzResearch.WordTrace tailWord_498093 prefixEnd_498093 170507413093349961697879 := by
  unfold tailWord_498093
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166944184501603356938933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12111296123001068904625955 18166944184501603356938933)
  ·
    refine ⟨1703151017297025314713025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18166944184501603356938933 1703151017297025314713025)
    ·
      refine ⟨1277363262972768986034769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703151017297025314713025 1277363262972768986034769)
      ·
        refine ⟨958022447229576739526077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1277363262972768986034769 958022447229576739526077)
        ·
          refine ⟨359258417711091277322279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958022447229576739526077 359258417711091277322279)
          ·
            refine ⟨538887626566636915983419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359258417711091277322279 538887626566636915983419)
            ·
              refine ⟨808331439849955373975129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538887626566636915983419 808331439849955373975129)
              ·
                refine ⟨606248579887466530481347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808331439849955373975129 606248579887466530481347)
                ·
                  refine ⟨909372869831199795722021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606248579887466530481347 909372869831199795722021)
                  ·
                    refine ⟨170507413093349961697879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909372869831199795722021 170507413093349961697879)
                    ·
                      rfl

theorem cell22_498093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_498093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498093 prefixEnd_498093 := by exact prefixLift 498093
  have htrace : WordTrace (prefixWord ++ tailWord_498093) baseStart_498093 baseEnd_498093 := by
    simpa [prefixWord, tailWord_498093, baseEnd_498093] using wordTrace_append hprefix tailTrace_498093
  have hstable : (prefixWord ++ tailWord_498093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498093).length < 2 ^ (prefixWord ++ tailWord_498093).sum := by decide
  have hdescent : baseEnd_498093 < baseStart_498093 := by decide
  rcases family_descends (prefixWord ++ tailWord_498093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498132 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_498132 : Nat := 118140960795 + 498132 * 2 ^ 59
def prefixEnd_498132 : Nat := 4983230072969 + 3 ^ 40 * 498132 * 2
def baseEnd_498132 : Nat := 170520763590366859972759

theorem tailTrace_498132 : CollatzResearch.WordTrace tailWord_498132 prefixEnd_498132 170520763590366859972759 := by
  unfold tailWord_498132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084183315680156508804325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12112244420906875345072433 9084183315680156508804325)
  ·
    refine ⟨1703284371690029345400811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9084183315680156508804325 1703284371690029345400811)
    ·
      refine ⟨2554926557535044018101217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703284371690029345400811 2554926557535044018101217)
      ·
        refine ⟨1916194918151283013575913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554926557535044018101217 1916194918151283013575913)
        ·
          refine ⟨1437146188613462260181935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916194918151283013575913 1437146188613462260181935)
          ·
            refine ⟨2155719282920193390272903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437146188613462260181935 2155719282920193390272903)
            ·
              refine ⟨3233578924380290085409355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155719282920193390272903 3233578924380290085409355)
              ·
                refine ⟨4850368386570435128114033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233578924380290085409355 4850368386570435128114033)
                ·
                  refine ⟨3637776289927826346085525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4850368386570435128114033 3637776289927826346085525)
                  ·
                    refine ⟨170520763590366859972759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3637776289927826346085525 170520763590366859972759)
                    ·
                      rfl

theorem cell22_498132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_498132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498132 prefixEnd_498132 := by exact prefixLift 498132
  have htrace : WordTrace (prefixWord ++ tailWord_498132) baseStart_498132 baseEnd_498132 := by
    simpa [prefixWord, tailWord_498132, baseEnd_498132] using wordTrace_append hprefix tailTrace_498132
  have hstable : (prefixWord ++ tailWord_498132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498132).length < 2 ^ (prefixWord ++ tailWord_498132).sum := by decide
  have hdescent : baseEnd_498132 < baseStart_498132 := by decide
  rcases family_descends (prefixWord ++ tailWord_498132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498175 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 8]
def baseStart_498175 : Nat := 118140960795 + 498175 * 2 ^ 59
def prefixEnd_498175 : Nat := 4983230072969 + 3 ^ 40 * 498175 * 2
def baseEnd_498175 : Nat := 56845161123043027049209

theorem tailTrace_498175 : CollatzResearch.WordTrace tailWord_498175 prefixEnd_498175 56845161123043027049209 := by
  unfold tailWord_498175
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169934970204531361423979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12113289980136354240949319 18169934970204531361423979)
  ·
    refine ⟨27254902455306797042135969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18169934970204531361423979 27254902455306797042135969)
    ·
      refine ⟨20441176841480097781601977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27254902455306797042135969 20441176841480097781601977)
      ·
        refine ⟨15330882631110073336201483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20441176841480097781601977 15330882631110073336201483)
        ·
          refine ⟨22996323946665110004302225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15330882631110073336201483 22996323946665110004302225)
          ·
            refine ⟨17247242959998832503226669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22996323946665110004302225 17247242959998832503226669)
            ·
              refine ⟨6467716109999562188710001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17247242959998832503226669 6467716109999562188710001)
              ·
                refine ⟨4850787082499671641532501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6467716109999562188710001 4850787082499671641532501)
                ·
                  refine ⟨56845161123043027049209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4850787082499671641532501 56845161123043027049209)
                  ·
                    rfl

theorem cell22_498175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_498175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498175 prefixEnd_498175 := by exact prefixLift 498175
  have htrace : WordTrace (prefixWord ++ tailWord_498175) baseStart_498175 baseEnd_498175 := by
    simpa [prefixWord, tailWord_498175, baseEnd_498175] using wordTrace_append hprefix tailTrace_498175
  have hstable : (prefixWord ++ tailWord_498175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498175).length < 2 ^ (prefixWord ++ tailWord_498175).sum := by decide
  have hdescent : baseEnd_498175 < baseStart_498175 := by decide
  rcases family_descends (prefixWord ++ tailWord_498175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498237 : List Nat := [1, 4, 1, 3, 2, 1, 10]
def baseStart_498237 : Nat := 118140960795 + 498237 * 2 ^ 59
def prefixEnd_498237 : Nat := 4983230072969 + 3 ^ 40 * 498237 * 2
def baseEnd_498237 : Nat := 6316915082821540225831

theorem tailTrace_498237 : CollatzResearch.WordTrace tailWord_498237 prefixEnd_498237 6316915082821540225831 := by
  unfold tailWord_498237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172196295979915950180965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12114797530653277300120643 18172196295979915950180965)
  ·
    refine ⟨3407286805496234240658931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18172196295979915950180965 3407286805496234240658931)
    ·
      refine ⟨5110930208244351360988397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407286805496234240658931 5110930208244351360988397)
      ·
        refine ⟨1916598828091631760370649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5110930208244351360988397 1916598828091631760370649)
        ·
          refine ⟨1437449121068723820277987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916598828091631760370649 1437449121068723820277987)
          ·
            refine ⟨2156173681603085730416981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437449121068723820277987 2156173681603085730416981)
            ·
              refine ⟨6316915082821540225831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2156173681603085730416981 6316915082821540225831)
              ·
                rfl

theorem cell22_498237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 10].length) (baseStart_498237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498237 prefixEnd_498237 := by exact prefixLift 498237
  have htrace : WordTrace (prefixWord ++ tailWord_498237) baseStart_498237 baseEnd_498237 := by
    simpa [prefixWord, tailWord_498237, baseEnd_498237] using wordTrace_append hprefix tailTrace_498237
  have hstable : (prefixWord ++ tailWord_498237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498237).length < 2 ^ (prefixWord ++ tailWord_498237).sum := by decide
  have hdescent : baseEnd_498237 < baseStart_498237 := by decide
  rcases family_descends (prefixWord ++ tailWord_498237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498329 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_498329 : Nat := 118140960795 + 498329 * 2 ^ 59
def prefixEnd_498329 : Nat := 4983230072969 + 3 ^ 40 * 498329 * 2
def baseEnd_498329 : Nat := 170588200716324012797155

theorem tailTrace_498329 : CollatzResearch.WordTrace tailWord_498329 prefixEnd_498329 170588200716324012797155 := by
  unfold tailWord_498329
  simp only [CollatzResearch.WordTrace]
  refine ⟨18175551811646615662530041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12117034541097743775020027 18175551811646615662530041)
  ·
    refine ⟨13631663858734961746897531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18175551811646615662530041 13631663858734961746897531)
    ·
      refine ⟨20447495788102442620346297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13631663858734961746897531 20447495788102442620346297)
      ·
        refine ⟨15335621841076831965259723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20447495788102442620346297 15335621841076831965259723)
        ·
          refine ⟨23003432761615247947889585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335621841076831965259723 23003432761615247947889585)
          ·
            refine ⟨17252574571211435960917189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23003432761615247947889585 17252574571211435960917189)
            ·
              refine ⟨3234857732102144242671973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17252574571211435960917189 3234857732102144242671973)
              ·
                refine ⟨606535824769152045500995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3234857732102144242671973 606535824769152045500995)
                ·
                  refine ⟨909803737153728068251493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606535824769152045500995 909803737153728068251493)
                  ·
                    refine ⟨170588200716324012797155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 909803737153728068251493 170588200716324012797155)
                    ·
                      rfl

theorem cell22_498329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_498329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498329 prefixEnd_498329 := by exact prefixLift 498329
  have htrace : WordTrace (prefixWord ++ tailWord_498329) baseStart_498329 baseEnd_498329 := by
    simpa [prefixWord, tailWord_498329, baseEnd_498329] using wordTrace_append hprefix tailTrace_498329
  have hstable : (prefixWord ++ tailWord_498329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498329).length < 2 ^ (prefixWord ++ tailWord_498329).sum := by decide
  have hdescent : baseEnd_498329 < baseStart_498329 := by decide
  rcases family_descends (prefixWord ++ tailWord_498329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498376 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_498376 : Nat := 118140960795 + 498376 * 2 ^ 59
def prefixEnd_498376 : Nat := 4983230072969 + 3 ^ 40 * 498376 * 2
def baseEnd_498376 : Nat := 170604289776831556872011

theorem tailTrace_498376 : CollatzResearch.WordTrace tailWord_498376 prefixEnd_498376 170604289776831556872011 := by
  unfold tailWord_498376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088633021238171344745491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12118177361650895126327321 9088633021238171344745491)
  ·
    refine ⟨13632949531857257017118237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9088633021238171344745491 13632949531857257017118237)
    ·
      refine ⟨5112356074446471381419339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13632949531857257017118237 5112356074446471381419339)
      ·
        refine ⟨7668534111669707072129009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112356074446471381419339 7668534111669707072129009)
        ·
          refine ⟨5751400583752280304096757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7668534111669707072129009 5751400583752280304096757)
          ·
            refine ⟨539193804726776278509071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5751400583752280304096757 539193804726776278509071)
            ·
              refine ⟨808790707090164417763607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539193804726776278509071 808790707090164417763607)
              ·
                refine ⟨1213186060635246626645411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808790707090164417763607 1213186060635246626645411)
                ·
                  refine ⟨1819779090952869939968117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213186060635246626645411 1819779090952869939968117)
                  ·
                    refine ⟨170604289776831556872011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1819779090952869939968117 170604289776831556872011)
                    ·
                      rfl

theorem cell22_498376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_498376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498376 prefixEnd_498376 := by exact prefixLift 498376
  have htrace : WordTrace (prefixWord ++ tailWord_498376) baseStart_498376 baseEnd_498376 := by
    simpa [prefixWord, tailWord_498376, baseEnd_498376] using wordTrace_append hprefix tailTrace_498376
  have hstable : (prefixWord ++ tailWord_498376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498376).length < 2 ^ (prefixWord ++ tailWord_498376).sum := by decide
  have hdescent : baseEnd_498376 < baseStart_498376 := by decide
  rcases family_descends (prefixWord ++ tailWord_498376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498468 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_498468 : Nat := 118140960795 + 498468 * 2 ^ 59
def prefixEnd_498468 : Nat := 4983230072969 + 3 ^ 40 * 498468 * 2
def baseEnd_498468 : Nat := 56878594418991327857243

theorem tailTrace_498468 : CollatzResearch.WordTrace tailWord_498468 prefixEnd_498468 56878594418991327857243 := by
  unfold tailWord_498468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090310779071521200920029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12120414372095361601226705 9090310779071521200920029)
  ·
    refine ⟨3408866542151820450345011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9090310779071521200920029 3408866542151820450345011)
    ·
      refine ⟨5113299813227730675517517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408866542151820450345011 5113299813227730675517517)
      ·
        refine ⟨1917487429960399003319069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5113299813227730675517517 1917487429960399003319069)
        ·
          refine ⟨719057786235149626244651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1917487429960399003319069 719057786235149626244651)
          ·
            refine ⟨1078586679352724439366977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719057786235149626244651 1078586679352724439366977)
            ·
              refine ⟨808940009514543329525233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078586679352724439366977 808940009514543329525233)
              ·
                refine ⟨606705007135907497143925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808940009514543329525233 606705007135907497143925)
                ·
                  refine ⟨56878594418991327857243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 606705007135907497143925 56878594418991327857243)
                  ·
                    rfl

theorem cell22_498468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_498468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498468 prefixEnd_498468 := by exact prefixLift 498468
  have htrace : WordTrace (prefixWord ++ tailWord_498468) baseStart_498468 baseEnd_498468 := by
    simpa [prefixWord, tailWord_498468, baseEnd_498468] using wordTrace_append hprefix tailTrace_498468
  have hstable : (prefixWord ++ tailWord_498468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498468).length < 2 ^ (prefixWord ++ tailWord_498468).sum := by decide
  have hdescent : baseEnd_498468 < baseStart_498468 := by decide
  rcases family_descends (prefixWord ++ tailWord_498468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498545 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_498545 : Nat := 118140960795 + 498545 * 2 ^ 59
def prefixEnd_498545 : Nat := 4983230072969 + 3 ^ 40 * 498545 * 2
def baseEnd_498545 : Nat := 170662141930571449396493

theorem tailTrace_498545 : CollatzResearch.WordTrace tailWord_498545 prefixEnd_498545 170662141930571449396493 := by
  unfold tailWord_498545
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183429978864084552393089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12122286652576056368262059 18183429978864084552393089)
  ·
    refine ⟨13637572484148063414294817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18183429978864084552393089 13637572484148063414294817)
    ·
      refine ⟨10228179363111047560721113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13637572484148063414294817 10228179363111047560721113)
      ·
        refine ⟨7671134522333285670540835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10228179363111047560721113 7671134522333285670540835)
        ·
          refine ⟨11506701783499928505811253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671134522333285670540835 11506701783499928505811253)
          ·
            refine ⟨1078753292203118297419805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11506701783499928505811253 1078753292203118297419805)
            ·
              refine ⟨404532484576169361532427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078753292203118297419805 404532484576169361532427)
              ·
                refine ⟨606798726864254042298641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404532484576169361532427 606798726864254042298641)
                ·
                  refine ⟨455099045148190531723981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606798726864254042298641 455099045148190531723981)
                  ·
                    refine ⟨170662141930571449396493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455099045148190531723981 170662141930571449396493)
                    ·
                      rfl

theorem cell22_498545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_498545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498545 prefixEnd_498545 := by exact prefixLift 498545
  have htrace : WordTrace (prefixWord ++ tailWord_498545) baseStart_498545 baseEnd_498545 := by
    simpa [prefixWord, tailWord_498545, baseEnd_498545] using wordTrace_append hprefix tailTrace_498545
  have hstable : (prefixWord ++ tailWord_498545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498545).length < 2 ^ (prefixWord ++ tailWord_498545).sum := by decide
  have hdescent : baseEnd_498545 < baseStart_498545 := by decide
  rcases family_descends (prefixWord ++ tailWord_498545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498663 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_498663 : Nat := 118140960795 + 498663 * 2 ^ 59
def prefixEnd_498663 : Nat := 4983230072969 + 3 ^ 40 * 498663 * 2
def baseEnd_498663 : Nat := 170702535742058474946131

theorem tailTrace_498663 : CollatzResearch.WordTrace tailWord_498663 prefixEnd_498663 170702535742058474946131 := by
  unfold tailWord_498663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187733792436590705188643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12125155861624393803459095 18187733792436590705188643)
  ·
    refine ⟨27281600688654886057782965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18187733792436590705188643 27281600688654886057782965)
    ·
      refine ⟨2557650064561395567917153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27281600688654886057782965 2557650064561395567917153)
      ·
        refine ⟨1918237548421046675937865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2557650064561395567917153 1918237548421046675937865)
        ·
          refine ⟨1438678161315785006953399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918237548421046675937865 1438678161315785006953399)
          ·
            refine ⟨2158017241973677510430099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438678161315785006953399 2158017241973677510430099)
            ·
              refine ⟨3237025862960516265645149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158017241973677510430099 3237025862960516265645149)
              ·
                refine ⟨1213884698610193599616931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237025862960516265645149 1213884698610193599616931)
                ·
                  refine ⟨1820827047915290399425397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1213884698610193599616931 1820827047915290399425397)
                  ·
                    refine ⟨170702535742058474946131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1820827047915290399425397 170702535742058474946131)
                    ·
                      rfl

theorem cell22_498663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_498663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498663 prefixEnd_498663 := by exact prefixLift 498663
  have htrace : WordTrace (prefixWord ++ tailWord_498663) baseStart_498663 baseEnd_498663 := by
    simpa [prefixWord, tailWord_498663, baseEnd_498663] using wordTrace_append hprefix tailTrace_498663
  have hstable : (prefixWord ++ tailWord_498663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498663).length < 2 ^ (prefixWord ++ tailWord_498663).sum := by decide
  have hdescent : baseEnd_498663 < baseStart_498663 := by decide
  rcases family_descends (prefixWord ++ tailWord_498663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498727 : List Nat := [1, 1, 7, 1, 1, 3, 2, 6]
def baseStart_498727 : Nat := 118140960795 + 498727 * 2 ^ 59
def prefixEnd_498727 : Nat := 4983230072969 + 3 ^ 40 * 498727 * 2
def baseEnd_498727 : Nat := 18969382694442626816215

theorem tailTrace_498727 : CollatzResearch.WordTrace tailWord_498727 prefixEnd_498727 18969382694442626816215 := by
  unfold tailWord_498727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190068064204729635518435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12126712042803153090345623 18190068064204729635518435)
  ·
    refine ⟨27285102096307094453277653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18190068064204729635518435 27285102096307094453277653)
    ·
      refine ⟨639494580382197526248695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27285102096307094453277653 639494580382197526248695)
      ·
        refine ⟨959241870573296289373043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639494580382197526248695 959241870573296289373043)
        ·
          refine ⟨1438862805859944434059565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959241870573296289373043 1438862805859944434059565)
          ·
            refine ⟨539573552197479162772337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438862805859944434059565 539573552197479162772337)
            ·
              refine ⟨404680164148109372079253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539573552197479162772337 404680164148109372079253)
              ·
                refine ⟨18969382694442626816215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 404680164148109372079253 18969382694442626816215)
                ·
                  rfl

theorem cell22_498727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 6].length) (baseStart_498727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498727 prefixEnd_498727 := by exact prefixLift 498727
  have htrace : WordTrace (prefixWord ++ tailWord_498727) baseStart_498727 baseEnd_498727 := by
    simpa [prefixWord, tailWord_498727, baseEnd_498727] using wordTrace_append hprefix tailTrace_498727
  have hstable : (prefixWord ++ tailWord_498727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498727).length < 2 ^ (prefixWord ++ tailWord_498727).sum := by decide
  have hdescent : baseEnd_498727 < baseStart_498727 := by decide
  rcases family_descends (prefixWord ++ tailWord_498727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498759 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 1, 3]
def baseStart_498759 : Nat := 118140960795 + 498759 * 2 ^ 59
def prefixEnd_498759 : Nat := 4983230072969 + 3 ^ 40 * 498759 * 2
def baseEnd_498759 : Nat := 170735398503946224545837

theorem tailTrace_498759 : CollatzResearch.WordTrace tailWord_498759 prefixEnd_498759 170735398503946224545837 := by
  unfold tailWord_498759
  simp only [CollatzResearch.WordTrace]
  refine ⟨18191235200088799100683331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12127490133392532733788887 18191235200088799100683331)
  ·
    refine ⟨27286852800133198651024997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18191235200088799100683331 27286852800133198651024997)
    ·
      refine ⟨5116284900024974747067187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27286852800133198651024997 5116284900024974747067187)
      ·
        refine ⟨7674427350037462120600781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116284900024974747067187 7674427350037462120600781)
        ·
          refine ⟨2877910256264048295225293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7674427350037462120600781 2877910256264048295225293)
          ·
            refine ⟨1079216346099018110709485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2877910256264048295225293 1079216346099018110709485)
            ·
              refine ⟨404706129787131791516057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079216346099018110709485 404706129787131791516057)
              ·
                refine ⟨303529597340348843637043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404706129787131791516057 303529597340348843637043)
                ·
                  refine ⟨455294396010523265455565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303529597340348843637043 455294396010523265455565)
                  ·
                    refine ⟨170735398503946224545837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455294396010523265455565 170735398503946224545837)
                    ·
                      rfl

theorem cell22_498759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_498759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498759 prefixEnd_498759 := by exact prefixLift 498759
  have htrace : WordTrace (prefixWord ++ tailWord_498759) baseStart_498759 baseEnd_498759 := by
    simpa [prefixWord, tailWord_498759, baseEnd_498759] using wordTrace_append hprefix tailTrace_498759
  have hstable : (prefixWord ++ tailWord_498759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498759).length < 2 ^ (prefixWord ++ tailWord_498759).sum := by decide
  have hdescent : baseEnd_498759 < baseStart_498759 := by decide
  rcases family_descends (prefixWord ++ tailWord_498759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498785 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_498785 : Nat := 118140960795 + 498785 * 2 ^ 59
def prefixEnd_498785 : Nat := 4983230072969 + 3 ^ 40 * 498785 * 2
def baseEnd_498785 : Nat := 170744298835290823395757

theorem tailTrace_498785 : CollatzResearch.WordTrace tailWord_498785 prefixEnd_498785 170744298835290823395757 := by
  unfold tailWord_498785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18192183497994605541129809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128122331996403694086539 18192183497994605541129809)
  ·
    refine ⟨13644137623495954155847357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18192183497994605541129809 13644137623495954155847357)
    ·
      refine ⟨5116551608810982808442759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13644137623495954155847357 5116551608810982808442759)
      ·
        refine ⟨7674827413216474212664139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116551608810982808442759 7674827413216474212664139)
        ·
          refine ⟨11512241119824711318996209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674827413216474212664139 11512241119824711318996209)
          ·
            refine ⟨8634180839868533489247157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11512241119824711318996209 8634180839868533489247157)
            ·
              refine ⟨809454453737675014616921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8634180839868533489247157 809454453737675014616921)
              ·
                refine ⟨607090840303256260962691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809454453737675014616921 607090840303256260962691)
                ·
                  refine ⟨910636260454884391444037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607090840303256260962691 910636260454884391444037)
                  ·
                    refine ⟨170744298835290823395757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910636260454884391444037 170744298835290823395757)
                    ·
                      rfl

theorem cell22_498785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_498785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498785 prefixEnd_498785 := by exact prefixLift 498785
  have htrace : WordTrace (prefixWord ++ tailWord_498785) baseStart_498785 baseEnd_498785 := by
    simpa [prefixWord, tailWord_498785, baseEnd_498785] using wordTrace_append hprefix tailTrace_498785
  have hstable : (prefixWord ++ tailWord_498785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498785).length < 2 ^ (prefixWord ++ tailWord_498785).sum := by decide
  have hdescent : baseEnd_498785 < baseStart_498785 := by decide
  rcases family_descends (prefixWord ++ tailWord_498785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498800 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_498800 : Nat := 118140960795 + 498800 * 2 ^ 59
def prefixEnd_498800 : Nat := 4983230072969 + 3 ^ 40 * 498800 * 2
def baseEnd_498800 : Nat := 56916477880611928090237

theorem tailTrace_498800 : CollatzResearch.WordTrace tailWord_498800 prefixEnd_498800 56916477880611928090237 := by
  unfold tailWord_498800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096365296470131551462927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12128487061960175401950569 9096365296470131551462927)
  ·
    refine ⟨13644547944705197327194391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096365296470131551462927 13644547944705197327194391)
    ·
      refine ⟨20466821917057795990791587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644547944705197327194391 20466821917057795990791587)
      ·
        refine ⟨30700232875586693986187381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20466821917057795990791587 30700232875586693986187381)
        ·
          refine ⟨2878146832086252561205067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30700232875586693986187381 2878146832086252561205067)
          ·
            refine ⟨4317220248129378841807601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878146832086252561205067 4317220248129378841807601)
            ·
              refine ⟨3237915186097034131355701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317220248129378841807601 3237915186097034131355701)
              ·
                refine ⟨303554548696596949814597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3237915186097034131355701 303554548696596949814597)
                ·
                  refine ⟨56916477880611928090237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303554548696596949814597 56916477880611928090237)
                  ·
                    rfl

theorem cell22_498800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_498800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498800 prefixEnd_498800 := by exact prefixLift 498800
  have htrace : WordTrace (prefixWord ++ tailWord_498800) baseStart_498800 baseEnd_498800 := by
    simpa [prefixWord, tailWord_498800, baseEnd_498800] using wordTrace_append hprefix tailTrace_498800
  have hstable : (prefixWord ++ tailWord_498800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498800).length < 2 ^ (prefixWord ++ tailWord_498800).sum := by decide
  have hdescent : baseEnd_498800 < baseStart_498800 := by decide
  rcases family_descends (prefixWord ++ tailWord_498800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498802 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_498802 : Nat := 118140960795 + 498802 * 2 ^ 59
def prefixEnd_498802 : Nat := 4983230072969 + 3 ^ 40 * 498802 * 2
def baseEnd_498802 : Nat := 170750118282708445720705

theorem tailTrace_498802 : CollatzResearch.WordTrace tailWord_498802 prefixEnd_498802 170750118282708445720705 := by
  unfold tailWord_498802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548200884733254361124665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12128535692622011629665773 4548200884733254361124665)
  ·
    refine ⟨3411150663549940770843499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4548200884733254361124665 3411150663549940770843499)
    ·
      refine ⟨5116725995324911156265249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411150663549940770843499 5116725995324911156265249)
      ·
        refine ⟨3837544496493683367198937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5116725995324911156265249 3837544496493683367198937)
        ·
          refine ⟨2878158372370262525399203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3837544496493683367198937 2878158372370262525399203)
          ·
            refine ⟨4317237558555393788098805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878158372370262525399203 4317237558555393788098805)
            ·
              refine ⟨404741021114568167634263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4317237558555393788098805 404741021114568167634263)
              ·
                refine ⟨607111531671852251451395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404741021114568167634263 607111531671852251451395)
                ·
                  refine ⟨910667297507778377177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607111531671852251451395 910667297507778377177093)
                  ·
                    refine ⟨170750118282708445720705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 910667297507778377177093 170750118282708445720705)
                    ·
                      rfl

theorem cell22_498802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_498802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498802 prefixEnd_498802 := by exact prefixLift 498802
  have htrace : WordTrace (prefixWord ++ tailWord_498802) baseStart_498802 baseEnd_498802 := by
    simpa [prefixWord, tailWord_498802, baseEnd_498802] using wordTrace_append hprefix tailTrace_498802
  have hstable : (prefixWord ++ tailWord_498802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498802).length < 2 ^ (prefixWord ++ tailWord_498802).sum := by decide
  have hdescent : baseEnd_498802 < baseStart_498802 := by decide
  rcases family_descends (prefixWord ++ tailWord_498802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498817 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 4]
def baseStart_498817 : Nat := 118140960795 + 498817 * 2 ^ 59
def prefixEnd_498817 : Nat := 4983230072969 + 3 ^ 40 * 498817 * 2
def baseEnd_498817 : Nat := 56918417696417802198553

theorem tailTrace_498817 : CollatzResearch.WordTrace tailWord_498817 prefixEnd_498817 56918417696417802198553 := by
  unfold tailWord_498817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193350633878675006294705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128900422585783337529803 18193350633878675006294705)
  ·
    refine ⟨13645012975409006254721029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18193350633878675006294705 13645012975409006254721029)
    ·
      refine ⟨2558439932889188672760193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13645012975409006254721029 2558439932889188672760193)
      ·
        refine ⟨1918829949666891504570145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2558439932889188672760193 1918829949666891504570145)
        ·
          refine ⟨1439122462250168628427609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918829949666891504570145 1439122462250168628427609)
          ·
            refine ⟨1079341846687626471320707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439122462250168628427609 1079341846687626471320707)
            ·
              refine ⟨1619012770031439706981061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079341846687626471320707 1619012770031439706981061)
              ·
                refine ⟨303564894380894945058949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1619012770031439706981061 303564894380894945058949)
                ·
                  refine ⟨56918417696417802198553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303564894380894945058949 56918417696417802198553)
                  ·
                    rfl

theorem cell22_498817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_498817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498817 prefixEnd_498817 := by exact prefixLift 498817
  have htrace : WordTrace (prefixWord ++ tailWord_498817) baseStart_498817 baseEnd_498817 := by
    simpa [prefixWord, tailWord_498817, baseEnd_498817] using wordTrace_append hprefix tailTrace_498817
  have hstable : (prefixWord ++ tailWord_498817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498817).length < 2 ^ (prefixWord ++ tailWord_498817).sum := by decide
  have hdescent : baseEnd_498817 < baseStart_498817 := by decide
  rcases family_descends (prefixWord ++ tailWord_498817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498845 : List Nat := [1, 4, 2, 1, 1, 2, 5, 6]
def baseStart_498845 : Nat := 118140960795 + 498845 * 2 ^ 59
def prefixEnd_498845 : Nat := 4983230072969 + 3 ^ 40 * 498845 * 2
def baseEnd_498845 : Nat := 18973870895718962988397

theorem tailTrace_498845 : CollatzResearch.WordTrace tailWord_498845 prefixEnd_498845 18973870895718962988397 := by
  unfold tailWord_498845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194371877777235788313989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12129581251851490525542659 18194371877777235788313989)
  ·
    refine ⟨3411444727083231710308873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18194371877777235788313989 3411444727083231710308873)
    ·
      refine ⟨2558583545312423782731655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411444727083231710308873 2558583545312423782731655)
      ·
        refine ⟨3837875317968635674097483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558583545312423782731655 3837875317968635674097483)
        ·
          refine ⟨5756812976952953511146225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837875317968635674097483 5756812976952953511146225)
          ·
            refine ⟨4317609732714715133359669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756812976952953511146225 4317609732714715133359669)
            ·
              refine ⟨404775912442004543752469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4317609732714715133359669 404775912442004543752469)
              ·
                refine ⟨18973870895718962988397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 404775912442004543752469 18973870895718962988397)
                ·
                  rfl

theorem cell22_498845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 6].length) (baseStart_498845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498845 prefixEnd_498845 := by exact prefixLift 498845
  have htrace : WordTrace (prefixWord ++ tailWord_498845) baseStart_498845 baseEnd_498845 := by
    simpa [prefixWord, tailWord_498845, baseEnd_498845] using wordTrace_append hprefix tailTrace_498845
  have hstable : (prefixWord ++ tailWord_498845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498845).length < 2 ^ (prefixWord ++ tailWord_498845).sum := by decide
  have hdescent : baseEnd_498845 < baseStart_498845 := by decide
  rcases family_descends (prefixWord ++ tailWord_498845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498984 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_498984 : Nat := 118140960795 + 498984 * 2 ^ 59
def prefixEnd_498984 : Nat := 4983230072969 + 3 ^ 40 * 498984 * 2
def baseEnd_498984 : Nat := 170812420602120637670147

theorem tailTrace_498984 : CollatzResearch.WordTrace tailWord_498984 prefixEnd_498984 170812420602120637670147 := by
  unfold tailWord_498984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099720812136831263812003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12132961082849108351749337 9099720812136831263812003)
  ·
    refine ⟨13649581218205246895718005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099720812136831263812003 13649581218205246895718005)
    ·
      refine ⟨1279648239206741896473563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13649581218205246895718005 1279648239206741896473563)
      ·
        refine ⟨1919472358810112844710345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279648239206741896473563 1919472358810112844710345)
        ·
          refine ⟨1439604269107584633532759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1919472358810112844710345 1439604269107584633532759)
          ·
            refine ⟨2159406403661376950299139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439604269107584633532759 2159406403661376950299139)
            ·
              refine ⟨3239109605492065425448709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159406403661376950299139 3239109605492065425448709)
              ·
                refine ⟨607333051029762267271633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3239109605492065425448709 607333051029762267271633)
                ·
                  refine ⟨455499788272321700453725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607333051029762267271633 455499788272321700453725)
                  ·
                    refine ⟨170812420602120637670147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455499788272321700453725 170812420602120637670147)
                    ·
                      rfl

theorem cell22_498984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_498984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498984 prefixEnd_498984 := by exact prefixLift 498984
  have htrace : WordTrace (prefixWord ++ tailWord_498984) baseStart_498984 baseEnd_498984 := by
    simpa [prefixWord, tailWord_498984, baseEnd_498984] using wordTrace_append hprefix tailTrace_498984
  have hstable : (prefixWord ++ tailWord_498984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498984).length < 2 ^ (prefixWord ++ tailWord_498984).sum := by decide
  have hdescent : baseEnd_498984 < baseStart_498984 := by decide
  rcases family_descends (prefixWord ++ tailWord_498984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498986 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_498986 : Nat := 118140960795 + 498986 * 2 ^ 59
def prefixEnd_498986 : Nat := 4983230072969 + 3 ^ 40 * 498986 * 2
def baseEnd_498986 : Nat := 56937701747664433040047

theorem tailTrace_498986 : CollatzResearch.WordTrace tailWord_498986 prefixEnd_498986 56937701747664433040047 := by
  unfold tailWord_498986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549878642566604217299203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12133009713510944579464541 4549878642566604217299203)
  ·
    refine ⟨6824817963849906325948805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4549878642566604217299203 6824817963849906325948805)
    ·
      refine ⟨1279653368221857436115401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6824817963849906325948805 1279653368221857436115401)
      ·
        refine ⟨959740026166393077086551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279653368221857436115401 959740026166393077086551)
        ·
          refine ⟨1439610039249589615629827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959740026166393077086551 1439610039249589615629827)
          ·
            refine ⟨2159415058874384423444741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439610039249589615629827 2159415058874384423444741)
            ·
              refine ⟨404890323538947079395889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2159415058874384423444741 404890323538947079395889)
              ·
                refine ⟨303667742654210309546917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404890323538947079395889 303667742654210309546917)
                ·
                  refine ⟨56937701747664433040047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303667742654210309546917 56937701747664433040047)
                  ·
                    rfl

theorem cell22_498986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_498986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498986 prefixEnd_498986 := by exact prefixLift 498986
  have htrace : WordTrace (prefixWord ++ tailWord_498986) baseStart_498986 baseEnd_498986 := by
    simpa [prefixWord, tailWord_498986, baseEnd_498986] using wordTrace_append hprefix tailTrace_498986
  have hstable : (prefixWord ++ tailWord_498986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498986).length < 2 ^ (prefixWord ++ tailWord_498986).sum := by decide
  have hdescent : baseEnd_498986 < baseStart_498986 := by decide
  rcases family_descends (prefixWord ++ tailWord_498986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498997 : List Nat := [1, 3, 3, 1, 2, 4, 1, 7]
def baseStart_498997 : Nat := 118140960795 + 498997 * 2 ^ 59
def prefixEnd_498997 : Nat := 4983230072969 + 3 ^ 40 * 498997 * 2
def baseEnd_498997 : Nat := 18979652307532548566123

theorem tailTrace_498997 : CollatzResearch.WordTrace tailWord_498997 prefixEnd_498997 18979652307532548566123 := by
  unfold tailWord_498997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199915773226565747847245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12133277182151043831898163 18199915773226565747847245)
  ·
    refine ⟨6824968414959962155442717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18199915773226565747847245 6824968414959962155442717)
    ·
      refine ⟨2559363155609985808291019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6824968414959962155442717 2559363155609985808291019)
      ·
        refine ⟨3839044733414978712436529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559363155609985808291019 3839044733414978712436529)
        ·
          refine ⟨2879283550061234034327397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839044733414978712436529 2879283550061234034327397)
          ·
            refine ⟨539865665636481381436387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2879283550061234034327397 539865665636481381436387)
            ·
              refine ⟨809798498454722072154581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539865665636481381436387 809798498454722072154581)
              ·
                refine ⟨18979652307532548566123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 809798498454722072154581 18979652307532548566123)
                ·
                  rfl

theorem cell22_498997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 7].length) (baseStart_498997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_498997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_498997 prefixEnd_498997 := by exact prefixLift 498997
  have htrace : WordTrace (prefixWord ++ tailWord_498997) baseStart_498997 baseEnd_498997 := by
    simpa [prefixWord, tailWord_498997, baseEnd_498997] using wordTrace_append hprefix tailTrace_498997
  have hstable : (prefixWord ++ tailWord_498997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498997).length < 2 ^ (prefixWord ++ tailWord_498997).sum := by decide
  have hdescent : baseEnd_498997 < baseStart_498997 := by decide
  rcases family_descends (prefixWord ++ tailWord_498997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499025 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 7]
def baseStart_499025 : Nat := 118140960795 + 499025 * 2 ^ 59
def prefixEnd_499025 : Nat := 4983230072969 + 3 ^ 40 * 499025 * 2
def baseEnd_499025 : Nat := 56942151913336732465007

theorem tailTrace_499025 : CollatzResearch.WordTrace tailWord_499025 prefixEnd_499025 56942151913336732465007 := by
  unfold tailWord_499025
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200937017125126529866529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12133958011416751019911019 18200937017125126529866529)
  ·
    refine ⟨13650702762843844897399897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18200937017125126529866529 13650702762843844897399897)
    ·
      refine ⟨10238027072132883673049923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13650702762843844897399897 10238027072132883673049923)
      ·
        refine ⟨15357040608199325509574885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10238027072132883673049923 15357040608199325509574885)
        ·
          refine ⟨2879445114037373533045291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15357040608199325509574885 2879445114037373533045291)
          ·
            refine ⟨4319167671056060299567937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879445114037373533045291 4319167671056060299567937)
            ·
              refine ⟨3239375753292045224675953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319167671056060299567937 3239375753292045224675953)
              ·
                refine ⟨2429531814969033918506965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239375753292045224675953 2429531814969033918506965)
                ·
                  refine ⟨56942151913336732465007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2429531814969033918506965 56942151913336732465007)
                  ·
                    rfl

theorem cell22_499025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_499025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499025 prefixEnd_499025 := by exact prefixLift 499025
  have htrace : WordTrace (prefixWord ++ tailWord_499025) baseStart_499025 baseEnd_499025 := by
    simpa [prefixWord, tailWord_499025, baseEnd_499025] using wordTrace_append hprefix tailTrace_499025
  have hstable : (prefixWord ++ tailWord_499025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499025).length < 2 ^ (prefixWord ++ tailWord_499025).sum := by decide
  have hdescent : baseEnd_499025 < baseStart_499025 := by decide
  rcases family_descends (prefixWord ++ tailWord_499025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499042 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_499042 : Nat := 118140960795 + 499042 * 2 ^ 59
def prefixEnd_499042 : Nat := 4983230072969 + 3 ^ 40 * 499042 * 2
def baseEnd_499042 : Nat := 56944091729142606573323

theorem tailTrace_499042 : CollatzResearch.WordTrace tailWord_499042 prefixEnd_499042 56944091729142606573323 := by
  unfold tailWord_499042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550389264515884608308845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12134371372042358955490253 4550389264515884608308845)
  ·
    refine ⟨1706395974193456728115817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4550389264515884608308845 1706395974193456728115817)
    ·
      refine ⟨1279796980645092546086863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1706395974193456728115817 1279796980645092546086863)
      ·
        refine ⟨1919695470967638819130295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279796980645092546086863 1919695470967638819130295)
        ·
          refine ⟨2879543206451458228695443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919695470967638819130295 2879543206451458228695443)
          ·
            refine ⟨4319314809677187343043165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879543206451458228695443 4319314809677187343043165)
            ·
              refine ⟨1619743053628945253641187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4319314809677187343043165 1619743053628945253641187)
              ·
                refine ⟨2429614580443417880461781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619743053628945253641187 2429614580443417880461781)
                ·
                  refine ⟨56944091729142606573323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2429614580443417880461781 56944091729142606573323)
                  ·
                    rfl

theorem cell22_499042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_499042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499042 prefixEnd_499042 := by exact prefixLift 499042
  have htrace : WordTrace (prefixWord ++ tailWord_499042) baseStart_499042 baseEnd_499042 := by
    simpa [prefixWord, tailWord_499042, baseEnd_499042] using wordTrace_append hprefix tailTrace_499042
  have hstable : (prefixWord ++ tailWord_499042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499042).length < 2 ^ (prefixWord ++ tailWord_499042).sum := by decide
  have hdescent : baseEnd_499042 < baseStart_499042 := by decide
  rcases family_descends (prefixWord ++ tailWord_499042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499162 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_499162 : Nat := 118140960795 + 499162 * 2 ^ 59
def prefixEnd_499162 : Nat := 4983230072969 + 3 ^ 40 * 499162 * 2
def baseEnd_499162 : Nat := 170873353639787506719601

theorem tailTrace_499162 : CollatzResearch.WordTrace tailWord_499162 prefixEnd_499162 170873353639787506719601 := by
  unfold tailWord_499162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551483454407199731900935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12137289211752532618402493 4551483454407199731900935)
  ·
    refine ⟨6827225181610799597851403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551483454407199731900935 6827225181610799597851403)
    ·
      refine ⟨10240837772416199396777105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6827225181610799597851403 10240837772416199396777105)
      ·
        refine ⟨7680628329312149547582829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10240837772416199396777105 7680628329312149547582829)
        ·
          refine ⟨2880235623492056080343561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7680628329312149547582829 2880235623492056080343561)
          ·
            refine ⟨2160176717619042060257671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880235623492056080343561 2160176717619042060257671)
            ·
              refine ⟨3240265076428563090386507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160176717619042060257671 3240265076428563090386507)
              ·
                refine ⟨4860397614642844635579761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240265076428563090386507 4860397614642844635579761)
                ·
                  refine ⟨3645298210982133476684821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860397614642844635579761 3645298210982133476684821)
                  ·
                    refine ⟨170873353639787506719601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3645298210982133476684821 170873353639787506719601)
                    ·
                      rfl

theorem cell22_499162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_499162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499162 prefixEnd_499162 := by exact prefixLift 499162
  have htrace : WordTrace (prefixWord ++ tailWord_499162) baseStart_499162 baseEnd_499162 := by
    simpa [prefixWord, tailWord_499162, baseEnd_499162] using wordTrace_append hprefix tailTrace_499162
  have hstable : (prefixWord ++ tailWord_499162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499162).length < 2 ^ (prefixWord ++ tailWord_499162).sum := by decide
  have hdescent : baseEnd_499162 < baseStart_499162 := by decide
  rcases family_descends (prefixWord ++ tailWord_499162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499211 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 5]
def baseStart_499211 : Nat := 118140960795 + 499211 * 2 ^ 59
def prefixEnd_499211 : Nat := 4983230072969 + 3 ^ 40 * 499211 * 2
def baseEnd_499211 : Nat := 56963375780389237414817

theorem tailTrace_499211 : CollatzResearch.WordTrace tailWord_499211 prefixEnd_499211 56963375780389237414817 := by
  unfold tailWord_499211
  simp only [CollatzResearch.WordTrace]
  refine ⟨18207720994451280296137487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12138480662967520197424991 18207720994451280296137487)
  ·
    refine ⟨27311581491676920444206231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18207720994451280296137487 27311581491676920444206231)
    ·
      refine ⟨40967372237515380666309347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27311581491676920444206231 40967372237515380666309347)
      ·
        refine ⟨61451058356273070999464021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40967372237515380666309347 61451058356273070999464021)
        ·
          refine ⟨720129590112575050774969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 61451058356273070999464021 720129590112575050774969)
          ·
            refine ⟨540097192584431288081227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720129590112575050774969 540097192584431288081227)
            ·
              refine ⟨810145788876646932121841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540097192584431288081227 810145788876646932121841)
              ·
                refine ⟨607609341657485199091381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810145788876646932121841 607609341657485199091381)
                ·
                  refine ⟨56963375780389237414817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 607609341657485199091381 56963375780389237414817)
                  ·
                    rfl

theorem cell22_499211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 5].length) (baseStart_499211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499211 prefixEnd_499211 := by exact prefixLift 499211
  have htrace : WordTrace (prefixWord ++ tailWord_499211) baseStart_499211 baseEnd_499211 := by
    simpa [prefixWord, tailWord_499211, baseEnd_499211] using wordTrace_append hprefix tailTrace_499211
  have hstable : (prefixWord ++ tailWord_499211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499211).length < 2 ^ (prefixWord ++ tailWord_499211).sum := by decide
  have hdescent : baseEnd_499211 < baseStart_499211 := by decide
  rcases family_descends (prefixWord ++ tailWord_499211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499256 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_499256 : Nat := 118140960795 + 499256 * 2 ^ 59
def prefixEnd_499256 : Nat := 4983230072969 + 3 ^ 40 * 499256 * 2
def baseEnd_499256 : Nat := 56968510586934198289771

theorem tailTrace_499256 : CollatzResearch.WordTrace tailWord_499256 prefixEnd_499256 56968510586934198289771 := by
  unfold tailWord_499256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9104681139644126490762811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12139574852858835321017081 9104681139644126490762811)
  ·
    refine ⟨13657021709466189736144217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9104681139644126490762811 13657021709466189736144217)
    ·
      refine ⟨10242766282099642302108163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13657021709466189736144217 10242766282099642302108163)
      ·
        refine ⟨15364149423149463453162245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242766282099642302108163 15364149423149463453162245)
        ·
          refine ⟨2880778016840524397467921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15364149423149463453162245 2880778016840524397467921)
          ·
            refine ⟨2160583512630393298100941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880778016840524397467921 2160583512630393298100941)
            ·
              refine ⟨810218817236397486787853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160583512630393298100941 810218817236397486787853)
              ·
                refine ⟨303832056463649057545445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810218817236397486787853 303832056463649057545445)
                ·
                  refine ⟨56968510586934198289771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303832056463649057545445 56968510586934198289771)
                  ·
                    rfl

theorem cell22_499256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_499256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499256 prefixEnd_499256 := by exact prefixLift 499256
  have htrace : WordTrace (prefixWord ++ tailWord_499256) baseStart_499256 baseEnd_499256 := by
    simpa [prefixWord, tailWord_499256, baseEnd_499256] using wordTrace_append hprefix tailTrace_499256
  have hstable : (prefixWord ++ tailWord_499256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499256).length < 2 ^ (prefixWord ++ tailWord_499256).sum := by decide
  have hdescent : baseEnd_499256 < baseStart_499256 := by decide
  rcases family_descends (prefixWord ++ tailWord_499256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499269 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_499269 : Nat := 118140960795 + 499269 * 2 ^ 59
def prefixEnd_499269 : Nat := 4983230072969 + 3 ^ 40 * 499269 * 2
def baseEnd_499269 : Nat := 170909981926474894294273

theorem tailTrace_499269 : CollatzResearch.WordTrace tailWord_499269 prefixEnd_499269 170909981926474894294273 := by
  unfold tailWord_499269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18209836428241156201748861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12139890952160770801165907 18209836428241156201748861)
  ·
    refine ⟨6828688660590433575655823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18209836428241156201748861 6828688660590433575655823)
    ·
      refine ⟨10243032990885650363483735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828688660590433575655823 10243032990885650363483735)
      ·
        refine ⟨15364549486328475545225603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243032990885650363483735 15364549486328475545225603)
        ·
          refine ⟨23046824229492713317838405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15364549486328475545225603 23046824229492713317838405)
          ·
            refine ⟨4321279543029883747094701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23046824229492713317838405 4321279543029883747094701)
            ·
              refine ⟨1620479828636206405160513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4321279543029883747094701 1620479828636206405160513)
              ·
                refine ⟨1215359871477154803870385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620479828636206405160513 1215359871477154803870385)
                ·
                  refine ⟨911519903607866102902789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1215359871477154803870385 911519903607866102902789)
                  ·
                    refine ⟨170909981926474894294273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 911519903607866102902789 170909981926474894294273)
                    ·
                      rfl

theorem cell22_499269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_499269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499269 prefixEnd_499269 := by exact prefixLift 499269
  have htrace : WordTrace (prefixWord ++ tailWord_499269) baseStart_499269 baseEnd_499269 := by
    simpa [prefixWord, tailWord_499269, baseEnd_499269] using wordTrace_append hprefix tailTrace_499269
  have hstable : (prefixWord ++ tailWord_499269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499269).length < 2 ^ (prefixWord ++ tailWord_499269).sum := by decide
  have hdescent : baseEnd_499269 < baseStart_499269 := by decide
  rcases family_descends (prefixWord ++ tailWord_499269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499284 : List Nat := [2, 4, 1, 1, 1, 2, 4, 7]
def baseStart_499284 : Nat := 118140960795 + 499284 * 2 ^ 59
def prefixEnd_499284 : Nat := 4983230072969 + 3 ^ 40 * 499284 * 2
def baseEnd_499284 : Nat := 18990568525891095018803

theorem tailTrace_499284 : CollatzResearch.WordTrace tailWord_499284 prefixEnd_499284 18990568525891095018803 := by
  unfold tailWord_499284
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105191761593406881772453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12140255682124542509029937 9105191761593406881772453)
  ·
    refine ⟨1707223455298763790332335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9105191761593406881772453 1707223455298763790332335)
    ·
      refine ⟨2560835182948145685498503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707223455298763790332335 2560835182948145685498503)
      ·
        refine ⟨3841252774422218528247755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560835182948145685498503 3841252774422218528247755)
        ·
          refine ⟨5761879161633327792371633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841252774422218528247755 5761879161633327792371633)
          ·
            refine ⟨4321409371224995844278725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5761879161633327792371633 4321409371224995844278725)
            ·
              refine ⟨810264257104686720802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4321409371224995844278725 810264257104686720802261)
              ·
                refine ⟨18990568525891095018803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 810264257104686720802261 18990568525891095018803)
                ·
                  rfl

theorem cell22_499284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_499284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499284 prefixEnd_499284 := by exact prefixLift 499284
  have htrace : WordTrace (prefixWord ++ tailWord_499284) baseStart_499284 baseEnd_499284 := by
    simpa [prefixWord, tailWord_499284, baseEnd_499284] using wordTrace_append hprefix tailTrace_499284
  have hstable : (prefixWord ++ tailWord_499284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499284).length < 2 ^ (prefixWord ++ tailWord_499284).sum := by decide
  have hdescent : baseEnd_499284 < baseStart_499284 := by decide
  rcases family_descends (prefixWord ++ tailWord_499284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499333 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_499333 : Nat := 118140960795 + 499333 * 2 ^ 59
def prefixEnd_499333 : Nat := 4983230072969 + 3 ^ 40 * 499333 * 2
def baseEnd_499333 : Nat := 170931890434400060694077

theorem tailTrace_499333 : CollatzResearch.WordTrace tailWord_499333 prefixEnd_499333 170931890434400060694077 := by
  unfold tailWord_499333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212170700009295132078653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12141447133339530088052435 18212170700009295132078653)
  ·
    refine ⟨6829564012503485674529495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18212170700009295132078653 6829564012503485674529495)
    ·
      refine ⟨10244346018755228511794243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829564012503485674529495 10244346018755228511794243)
      ·
        refine ⟨15366519028132842767691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10244346018755228511794243 15366519028132842767691365)
        ·
          refine ⟨2881222317774908018942131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15366519028132842767691365 2881222317774908018942131)
          ·
            refine ⟨4321833476662362028413197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881222317774908018942131 4321833476662362028413197)
            ·
              refine ⟨1620687553748385760654949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4321833476662362028413197 1620687553748385760654949)
              ·
                refine ⟨303878916327822330122803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1620687553748385760654949 303878916327822330122803)
                ·
                  refine ⟨455818374491733495184205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303878916327822330122803 455818374491733495184205)
                  ·
                    refine ⟨170931890434400060694077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455818374491733495184205 170931890434400060694077)
                    ·
                      rfl

theorem cell22_499333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_499333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499333 prefixEnd_499333 := by exact prefixLift 499333
  have htrace : WordTrace (prefixWord ++ tailWord_499333) baseStart_499333 baseEnd_499333 := by
    simpa [prefixWord, tailWord_499333, baseEnd_499333] using wordTrace_append hprefix tailTrace_499333
  have hstable : (prefixWord ++ tailWord_499333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499333).length < 2 ^ (prefixWord ++ tailWord_499333).sum := by decide
  have hdescent : baseEnd_499333 < baseStart_499333 := by decide
  rcases family_descends (prefixWord ++ tailWord_499333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499391 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 4]
def baseStart_499391 : Nat := 118140960795 + 499391 * 2 ^ 59
def prefixEnd_499391 : Nat := 4983230072969 + 3 ^ 40 * 499391 * 2
def baseEnd_499391 : Nat := 56983915006569080914633

theorem tailTrace_499391 : CollatzResearch.WordTrace tailWord_499391 prefixEnd_499391 56983915006569080914633 := by
  unfold tailWord_499391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214286133799171037690027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12142857422532780691793351 18214286133799171037690027)
  ·
    refine ⟨27321429200698756556535041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18214286133799171037690027 27321429200698756556535041)
    ·
      refine ⟨20491071900524067417401281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27321429200698756556535041 20491071900524067417401281)
      ·
        refine ⟨15368303925393050563050961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20491071900524067417401281 15368303925393050563050961)
        ·
          refine ⟨11526227944044787922288221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368303925393050563050961 11526227944044787922288221)
          ·
            refine ⟨4322335479016795470858083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11526227944044787922288221 4322335479016795470858083)
            ·
              refine ⟨6483503218525193206287125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322335479016795470858083 6483503218525193206287125)
              ·
                refine ⟨303914213368368431544709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6483503218525193206287125 303914213368368431544709)
                ·
                  refine ⟨56983915006569080914633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303914213368368431544709 56983915006569080914633)
                  ·
                    rfl

theorem cell22_499391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 4].length) (baseStart_499391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499391 prefixEnd_499391 := by exact prefixLift 499391
  have htrace : WordTrace (prefixWord ++ tailWord_499391) baseStart_499391 baseEnd_499391 := by
    simpa [prefixWord, tailWord_499391, baseEnd_499391] using wordTrace_append hprefix tailTrace_499391
  have hstable : (prefixWord ++ tailWord_499391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499391).length < 2 ^ (prefixWord ++ tailWord_499391).sum := by decide
  have hdescent : baseEnd_499391 < baseStart_499391 := by decide
  rcases family_descends (prefixWord ++ tailWord_499391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499425 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 4]
def baseStart_499425 : Nat := 118140960795 + 499425 * 2 ^ 59
def prefixEnd_499425 : Nat := 4983230072969 + 3 ^ 40 * 499425 * 2
def baseEnd_499425 : Nat := 56987794638180829131265

theorem tailTrace_499425 : CollatzResearch.WordTrace tailWord_499425 prefixEnd_499425 56987794638180829131265 := by
  unfold tailWord_499425
  simp only [CollatzResearch.WordTrace]
  refine ⟨18215526215675994844427729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12143684143783996562951819 18215526215675994844427729)
  ·
    refine ⟨13661644661756996133320797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18215526215675994844427729 13661644661756996133320797)
    ·
      refine ⟨5123116748158873549995299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13661644661756996133320797 5123116748158873549995299)
      ·
        refine ⟨7684675122238310324992949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123116748158873549995299 7684675122238310324992949)
        ·
          refine ⟨720438292709841592968089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7684675122238310324992949 720438292709841592968089)
          ·
            refine ⟨540328719532381194726067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720438292709841592968089 540328719532381194726067)
            ·
              refine ⟨810493079298571792089101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540328719532381194726067 810493079298571792089101)
              ·
                refine ⟨303934904736964422033413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810493079298571792089101 303934904736964422033413)
                ·
                  refine ⟨56987794638180829131265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303934904736964422033413 56987794638180829131265)
                  ·
                    rfl

theorem cell22_499425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_499425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499425 prefixEnd_499425 := by exact prefixLift 499425
  have htrace : WordTrace (prefixWord ++ tailWord_499425) baseStart_499425 baseEnd_499425 := by
    simpa [prefixWord, tailWord_499425, baseEnd_499425] using wordTrace_append hprefix tailTrace_499425
  have hstable : (prefixWord ++ tailWord_499425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499425).length < 2 ^ (prefixWord ++ tailWord_499425).sum := by decide
  have hdescent : baseEnd_499425 < baseStart_499425 := by decide
  rcases family_descends (prefixWord ++ tailWord_499425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499451 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 3, 3]
def baseStart_499451 : Nat := 118140960795 + 499451 * 2 ^ 59
def prefixEnd_499451 : Nat := 4983230072969 + 3 ^ 40 * 499451 * 2
def baseEnd_499451 : Nat := 170972284245887086243715

theorem tailTrace_499451 : CollatzResearch.WordTrace tailWord_499451 prefixEnd_499451 170972284245887086243715 := by
  unfold tailWord_499451
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216474513581801284874207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12144316342387867523249471 18216474513581801284874207)
  ·
    refine ⟨27324711770372701927311311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216474513581801284874207 27324711770372701927311311)
    ·
      refine ⟨40987067655559052890966967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27324711770372701927311311 40987067655559052890966967)
      ·
        refine ⟨61480601483338579336450451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40987067655559052890966967 61480601483338579336450451)
        ·
          refine ⟨92220902225007869004675677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61480601483338579336450451 92220902225007869004675677)
          ·
            refine ⟨34582838334377950876753379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92220902225007869004675677 34582838334377950876753379)
            ·
              refine ⟨51874257501566926315130069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34582838334377950876753379 51874257501566926315130069)
              ·
                refine ⟨1215802910192974835510861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51874257501566926315130069 1215802910192974835510861)
                ·
                  refine ⟨455926091322365563316573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215802910192974835510861 455926091322365563316573)
                  ·
                    refine ⟨170972284245887086243715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 455926091322365563316573 170972284245887086243715)
                    ·
                      rfl

theorem cell22_499451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 3].length) (baseStart_499451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499451 prefixEnd_499451 := by exact prefixLift 499451
  have htrace : WordTrace (prefixWord ++ tailWord_499451) baseStart_499451 baseEnd_499451 := by
    simpa [prefixWord, tailWord_499451, baseEnd_499451] using wordTrace_append hprefix tailTrace_499451
  have hstable : (prefixWord ++ tailWord_499451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499451).length < 2 ^ (prefixWord ++ tailWord_499451).sum := by decide
  have hdescent : baseEnd_499451 < baseStart_499451 := by decide
  rcases family_descends (prefixWord ++ tailWord_499451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499588 : List Nat := [2, 3, 2, 1, 1, 1, 6, 6]
def baseStart_499588 : Nat := 118140960795 + 499588 * 2 ^ 59
def prefixEnd_499588 : Nat := 4983230072969 + 3 ^ 40 * 499588 * 2
def baseEnd_499588 : Nat := 19002131349518266174255

theorem tailTrace_499588 : CollatzResearch.WordTrace tailWord_499588 prefixEnd_499588 19002131349518266174255 := by
  unfold tailWord_499588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110735657042736841305709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12147647542723649121740945 9110735657042736841305709)
  ·
    refine ⟨3416525871391026315489641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9110735657042736841305709 3416525871391026315489641)
    ·
      refine ⟨2562394403543269736617231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3416525871391026315489641 2562394403543269736617231)
      ·
        refine ⟨3843591605314904604925847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562394403543269736617231 3843591605314904604925847)
        ·
          refine ⟨5765387407972356907388771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843591605314904604925847 5765387407972356907388771)
          ·
            refine ⟨8648081111958535361083157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765387407972356907388771 8648081111958535361083157)
            ·
              refine ⟨405378802123056345050773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8648081111958535361083157 405378802123056345050773)
              ·
                refine ⟨19002131349518266174255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405378802123056345050773 19002131349518266174255)
                ·
                  rfl

theorem cell22_499588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_499588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499588 prefixEnd_499588 := by exact prefixLift 499588
  have htrace : WordTrace (prefixWord ++ tailWord_499588) baseStart_499588 baseEnd_499588 := by
    simpa [prefixWord, tailWord_499588, baseEnd_499588] using wordTrace_append hprefix tailTrace_499588
  have hstable : (prefixWord ++ tailWord_499588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499588).length < 2 ^ (prefixWord ++ tailWord_499588).sum := by decide
  have hdescent : baseEnd_499588 < baseStart_499588 := by decide
  rcases family_descends (prefixWord ++ tailWord_499588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499594 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_499594 : Nat := 118140960795 + 499594 * 2 ^ 59
def prefixEnd_499594 : Nat := 4983230072969 + 3 ^ 40 * 499594 * 2
def baseEnd_499594 : Nat := 57007078689427459972759

theorem tailTrace_499594 : CollatzResearch.WordTrace tailWord_499594 prefixEnd_499594 57007078689427459972759 := by
  unfold tailWord_499594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555422538015934176832459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12147793434709157804886557 4555422538015934176832459)
  ·
    refine ⟨6833133807023901265248689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4555422538015934176832459 6833133807023901265248689)
    ·
      refine ⟨5124850355267925948936517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6833133807023901265248689 5124850355267925948936517)
      ·
        refine ⟨960909441612736115425597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5124850355267925948936517 960909441612736115425597)
        ·
          refine ⟨360341040604776043284599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960909441612736115425597 360341040604776043284599)
          ·
            refine ⟨540511560907164064926899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360341040604776043284599 540511560907164064926899)
            ·
              refine ⟨810767341360746097390349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540511560907164064926899 810767341360746097390349)
              ·
                refine ⟨304037753010279786521381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810767341360746097390349 304037753010279786521381)
                ·
                  refine ⟨57007078689427459972759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304037753010279786521381 57007078689427459972759)
                  ·
                    rfl

theorem cell22_499594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_499594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499594 prefixEnd_499594 := by exact prefixLift 499594
  have htrace : WordTrace (prefixWord ++ tailWord_499594) baseStart_499594 baseEnd_499594 := by
    simpa [prefixWord, tailWord_499594, baseEnd_499594] using wordTrace_append hprefix tailTrace_499594
  have hstable : (prefixWord ++ tailWord_499594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499594).length < 2 ^ (prefixWord ++ tailWord_499594).sum := by decide
  have hdescent : baseEnd_499594 < baseStart_499594 := by decide
  rcases family_descends (prefixWord ++ tailWord_499594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499620 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_499620 : Nat := 118140960795 + 499620 * 2 ^ 59
def prefixEnd_499620 : Nat := 4983230072969 + 3 ^ 40 * 499620 * 2
def baseEnd_499620 : Nat := 171030136399626978768197

theorem tailTrace_499620 : CollatzResearch.WordTrace tailWord_499620 prefixEnd_499620 171030136399626978768197 := by
  unfold tailWord_499620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9111319224984771573888157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12148425633313028765184209 9111319224984771573888157)
  ·
    refine ⟨3416744709369289340208059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9111319224984771573888157 3416744709369289340208059)
    ·
      refine ⟨5125117064053934010312089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416744709369289340208059 5125117064053934010312089)
      ·
        refine ⟨3843837798040450507734067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125117064053934010312089 3843837798040450507734067)
        ·
          refine ⟨5765756697060675761601101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843837798040450507734067 5765756697060675761601101)
          ·
            refine ⟨2162158761397753410600413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5765756697060675761601101 2162158761397753410600413)
            ·
              refine ⟨810809535524157528975155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2162158761397753410600413 810809535524157528975155)
              ·
                refine ⟨1216214303286236293462733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810809535524157528975155 1216214303286236293462733)
                ·
                  refine ⟨456080363732338610048525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216214303286236293462733 456080363732338610048525)
                  ·
                    refine ⟨171030136399626978768197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456080363732338610048525 171030136399626978768197)
                    ·
                      rfl

theorem cell22_499620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_499620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499620 prefixEnd_499620 := by exact prefixLift 499620
  have htrace : WordTrace (prefixWord ++ tailWord_499620) baseStart_499620 baseEnd_499620 := by
    simpa [prefixWord, tailWord_499620, baseEnd_499620] using wordTrace_append hprefix tailTrace_499620
  have hstable : (prefixWord ++ tailWord_499620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499620).length < 2 ^ (prefixWord ++ tailWord_499620).sum := by decide
  have hdescent : baseEnd_499620 < baseStart_499620 := by decide
  rcases family_descends (prefixWord ++ tailWord_499620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499631 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_499631 : Nat := 118140960795 + 499631 * 2 ^ 59
def prefixEnd_499631 : Nat := 4983230072969 + 3 ^ 40 * 499631 * 2
def baseEnd_499631 : Nat := 171033901924426616743163

theorem tailTrace_499631 : CollatzResearch.WordTrace tailWord_499631 prefixEnd_499631 171033901924426616743163 := by
  unfold tailWord_499631
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223039652929692026426747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12148693101953128017617831 18223039652929692026426747)
  ·
    refine ⟨27334559479394538039640121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18223039652929692026426747 27334559479394538039640121)
    ·
      refine ⟨20500919609545903529730091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27334559479394538039640121 20500919609545903529730091)
      ·
        refine ⟨30751379414318855294595137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500919609545903529730091 30751379414318855294595137)
        ·
          refine ⟨23063534560739141470946353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30751379414318855294595137 23063534560739141470946353)
          ·
            refine ⟨17297650920554356103209765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23063534560739141470946353 17297650920554356103209765)
            ·
              refine ⟨3243309547603941769351831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17297650920554356103209765 3243309547603941769351831)
              ·
                refine ⟨4864964321405912654027747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243309547603941769351831 4864964321405912654027747)
                ·
                  refine ⟨7297446482108868981041621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864964321405912654027747 7297446482108868981041621)
                  ·
                    refine ⟨171033901924426616743163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7297446482108868981041621 171033901924426616743163)
                    ·
                      rfl

theorem cell22_499631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_499631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499631 prefixEnd_499631 := by exact prefixLift 499631
  have htrace : WordTrace (prefixWord ++ tailWord_499631) baseStart_499631 baseEnd_499631 := by
    simpa [prefixWord, tailWord_499631, baseEnd_499631] using wordTrace_append hprefix tailTrace_499631
  have hstable : (prefixWord ++ tailWord_499631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499631).length < 2 ^ (prefixWord ++ tailWord_499631).sum := by decide
  have hdescent : baseEnd_499631 < baseStart_499631 := by decide
  rcases family_descends (prefixWord ++ tailWord_499631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499682 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_499682 : Nat := 118140960795 + 499682 * 2 ^ 59
def prefixEnd_499682 : Nat := 4983230072969 + 3 ^ 40 * 499682 * 2
def baseEnd_499682 : Nat := 171051360266679483718007

theorem tailTrace_499682 : CollatzResearch.WordTrace tailWord_499682 prefixEnd_499682 171051360266679483718007 := by
  unfold tailWord_499682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556224943936231934133325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12149933183829951824355533 4556224943936231934133325)
  ·
    refine ⟨1708584353976086975299997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4556224943936231934133325 1708584353976086975299997)
    ·
      refine ⟨640719132741032615737499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1708584353976086975299997 640719132741032615737499)
      ·
        refine ⟨961078699111548923606249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640719132741032615737499 961078699111548923606249)
        ·
          refine ⟨720809024333661692704687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 961078699111548923606249 720809024333661692704687)
          ·
            refine ⟨1081213536500492539057031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720809024333661692704687 1081213536500492539057031)
            ·
              refine ⟨1621820304750738808585547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081213536500492539057031 1621820304750738808585547)
              ·
                refine ⟨2432730457126108212878321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621820304750738808585547 2432730457126108212878321)
                ·
                  refine ⟨1824547842844581159658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2432730457126108212878321 1824547842844581159658741)
                  ·
                    refine ⟨171051360266679483718007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1824547842844581159658741 171051360266679483718007)
                    ·
                      rfl

theorem cell22_499682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_499682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499682 prefixEnd_499682 := by exact prefixLift 499682
  have htrace : WordTrace (prefixWord ++ tailWord_499682) baseStart_499682 baseEnd_499682 := by
    simpa [prefixWord, tailWord_499682, baseEnd_499682] using wordTrace_append hprefix tailTrace_499682
  have hstable : (prefixWord ++ tailWord_499682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499682).length < 2 ^ (prefixWord ++ tailWord_499682).sum := by decide
  have hdescent : baseEnd_499682 < baseStart_499682 := by decide
  rcases family_descends (prefixWord ++ tailWord_499682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499708 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_499708 : Nat := 118140960795 + 499708 * 2 ^ 59
def prefixEnd_499708 : Nat := 4983230072969 + 3 ^ 40 * 499708 * 2
def baseEnd_499708 : Nat := 171060260598024082567927

theorem tailTrace_499708 : CollatzResearch.WordTrace tailWord_499708 prefixEnd_499708 171060260598024082567927 := by
  unfold tailWord_499708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112924036825367088489889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12150565382433822784653185 9112924036825367088489889)
  ·
    refine ⟨6834693027619025316367417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9112924036825367088489889 6834693027619025316367417)
    ·
      refine ⟨5126019770714268987275563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834693027619025316367417 5126019770714268987275563)
      ·
        refine ⟨7689029656071403480913345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126019770714268987275563 7689029656071403480913345)
        ·
          refine ⟨5766772242053552610685009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7689029656071403480913345 5766772242053552610685009)
          ·
            refine ⟨4325079181540164458013757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5766772242053552610685009 4325079181540164458013757)
            ·
              refine ⟨1621904693077561671755159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4325079181540164458013757 1621904693077561671755159)
              ·
                refine ⟨2432857039616342507632739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621904693077561671755159 2432857039616342507632739)
                ·
                  refine ⟨3649285559424513761449109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432857039616342507632739 3649285559424513761449109)
                  ·
                    refine ⟨171060260598024082567927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3649285559424513761449109 171060260598024082567927)
                    ·
                      rfl

theorem cell22_499708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_499708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499708 prefixEnd_499708 := by exact prefixLift 499708
  have htrace : WordTrace (prefixWord ++ tailWord_499708) baseStart_499708 baseEnd_499708 := by
    simpa [prefixWord, tailWord_499708, baseEnd_499708] using wordTrace_append hprefix tailTrace_499708
  have hstable : (prefixWord ++ tailWord_499708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499708).length < 2 ^ (prefixWord ++ tailWord_499708).sum := by decide
  have hdescent : baseEnd_499708 < baseStart_499708 := by decide
  rcases family_descends (prefixWord ++ tailWord_499708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499718 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_499718 : Nat := 118140960795 + 499718 * 2 ^ 59
def prefixEnd_499718 : Nat := 4983230072969 + 3 ^ 40 * 499718 * 2
def baseEnd_499718 : Nat := 57021227934129129939299

theorem tailTrace_499718 : CollatzResearch.WordTrace tailWord_499718 prefixEnd_499718 57021227934129129939299 := by
  unfold tailWord_499718
  simp only [CollatzResearch.WordTrace]
  refine ⟨569569150112953308901369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12150808535743003923229205 569569150112953308901369)
  ·
    refine ⟨427176862584714981676027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 569569150112953308901369 427176862584714981676027)
    ·
      refine ⟨640765293877072472514041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427176862584714981676027 640765293877072472514041)
      ·
        refine ⟨480573970407804354385531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640765293877072472514041 480573970407804354385531)
        ·
          refine ⟨720860955611706531578297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480573970407804354385531 720860955611706531578297)
          ·
            refine ⟨540645716708779898683723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720860955611706531578297 540645716708779898683723)
            ·
              refine ⟨810968575063169848025585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540645716708779898683723 810968575063169848025585)
              ·
                refine ⟨608226431297377386019189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810968575063169848025585 608226431297377386019189)
                ·
                  refine ⟨57021227934129129939299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608226431297377386019189 57021227934129129939299)
                  ·
                    rfl

theorem cell22_499718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_499718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499718 prefixEnd_499718 := by exact prefixLift 499718
  have htrace : WordTrace (prefixWord ++ tailWord_499718) baseStart_499718 baseEnd_499718 := by
    simpa [prefixWord, tailWord_499718, baseEnd_499718] using wordTrace_append hprefix tailTrace_499718
  have hstable : (prefixWord ++ tailWord_499718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499718).length < 2 ^ (prefixWord ++ tailWord_499718).sum := by decide
  have hdescent : baseEnd_499718 < baseStart_499718 := by decide
  rcases family_descends (prefixWord ++ tailWord_499718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499815 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_499815 : Nat := 118140960795 + 499815 * 2 ^ 59
def prefixEnd_499815 : Nat := 4983230072969 + 3 ^ 40 * 499815 * 2
def baseEnd_499815 : Nat := 171096888884711470142599

theorem tailTrace_499815 : CollatzResearch.WordTrace tailWord_499815 prefixEnd_499815 171096888884711470142599 := by
  unfold tailWord_499815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229750684263091451124899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12153167122842060967416599 18229750684263091451124899)
  ·
    refine ⟨27344626026394637176687349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18229750684263091451124899 27344626026394637176687349)
    ·
      refine ⟨2563558689974497235314439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27344626026394637176687349 2563558689974497235314439)
      ·
        refine ⟨3845338034961745852971659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563558689974497235314439 3845338034961745852971659)
        ·
          refine ⟨5768007052442618779457489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3845338034961745852971659 5768007052442618779457489)
          ·
            refine ⟨4326005289331964084593117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5768007052442618779457489 4326005289331964084593117)
            ·
              refine ⟨1622251983499486531722419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4326005289331964084593117 1622251983499486531722419)
              ·
                refine ⟨2433377975249229797583629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622251983499486531722419 2433377975249229797583629)
                ·
                  refine ⟨912516740718461174093861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2433377975249229797583629 912516740718461174093861)
                  ·
                    refine ⟨171096888884711470142599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912516740718461174093861 171096888884711470142599)
                    ·
                      rfl

theorem cell22_499815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_499815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499815 prefixEnd_499815 := by exact prefixLift 499815
  have htrace : WordTrace (prefixWord ++ tailWord_499815) baseStart_499815 baseEnd_499815 := by
    simpa [prefixWord, tailWord_499815, baseEnd_499815] using wordTrace_append hprefix tailTrace_499815
  have hstable : (prefixWord ++ tailWord_499815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499815).length < 2 ^ (prefixWord ++ tailWord_499815).sum := by decide
  have hdescent : baseEnd_499815 < baseStart_499815 := by decide
  rcases family_descends (prefixWord ++ tailWord_499815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499926 : List Nat := [5, 2, 1, 2, 1, 3, 2, 6]
def baseStart_499926 : Nat := 118140960795 + 499926 * 2 ^ 59
def prefixEnd_499926 : Nat := 4983230072969 + 3 ^ 40 * 499926 * 2
def baseEnd_499926 : Nat := 19014987383682686735251

theorem tailTrace_499926 : CollatzResearch.WordTrace tailWord_499926 prefixEnd_499926 19014987383682686735251 := by
  unfold tailWord_499926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139612449178809838025977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12155866124573971605610421 1139612449178809838025977)
  ·
    refine ⟨854709336884107378519483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1139612449178809838025977 854709336884107378519483)
    ·
      refine ⟨1282064005326161067779225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854709336884107378519483 1282064005326161067779225)
      ·
        refine ⟨961548003994620800834419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1282064005326161067779225 961548003994620800834419)
        ·
          refine ⟨1442322005991931201251629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961548003994620800834419 1442322005991931201251629)
          ·
            refine ⟨540870752246974200469361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442322005991931201251629 540870752246974200469361)
            ·
              refine ⟨405653064185230650352021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540870752246974200469361 405653064185230650352021)
              ·
                refine ⟨19014987383682686735251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405653064185230650352021 19014987383682686735251)
                ·
                  rfl

theorem cell22_499926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_499926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499926 prefixEnd_499926 := by exact prefixLift 499926
  have htrace : WordTrace (prefixWord ++ tailWord_499926) baseStart_499926 baseEnd_499926 := by
    simpa [prefixWord, tailWord_499926, baseEnd_499926] using wordTrace_append hprefix tailTrace_499926
  have hstable : (prefixWord ++ tailWord_499926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499926).length < 2 ^ (prefixWord ++ tailWord_499926).sum := by decide
  have hdescent : baseEnd_499926 < baseStart_499926 := by decide
  rcases family_descends (prefixWord ++ tailWord_499926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499941 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_499941 : Nat := 118140960795 + 499941 * 2 ^ 59
def prefixEnd_499941 : Nat := 4983230072969 + 3 ^ 40 * 499941 * 2
def baseEnd_499941 : Nat := 171140021259689141492213

theorem tailTrace_499941 : CollatzResearch.WordTrace tailWord_499941 prefixEnd_499941 171140021259689141492213 := by
  unfold tailWord_499941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234346281806614970211677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156230854537743313474451 18234346281806614970211677)
  ·
    refine ⟨6837879855677480613829379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18234346281806614970211677 6837879855677480613829379)
    ·
      refine ⟨10256819783516220920744069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837879855677480613829379 10256819783516220920744069)
      ·
        refine ⟨1923153709409291422639513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10256819783516220920744069 1923153709409291422639513)
        ·
          refine ⟨1442365282056968566979635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923153709409291422639513 1442365282056968566979635)
          ·
            refine ⟨2163547923085452850469453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442365282056968566979635 2163547923085452850469453)
            ·
              refine ⟨811330471157044818926045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163547923085452850469453 811330471157044818926045)
              ·
                refine ⟨304248926683891807097267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811330471157044818926045 304248926683891807097267)
                ·
                  refine ⟨456373390025837710645901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304248926683891807097267 456373390025837710645901)
                  ·
                    refine ⟨171140021259689141492213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456373390025837710645901 171140021259689141492213)
                    ·
                      rfl

theorem cell22_499941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_499941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499941 prefixEnd_499941 := by exact prefixLift 499941
  have htrace : WordTrace (prefixWord ++ tailWord_499941) baseStart_499941 baseEnd_499941 := by
    simpa [prefixWord, tailWord_499941, baseEnd_499941] using wordTrace_append hprefix tailTrace_499941
  have hstable : (prefixWord ++ tailWord_499941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499941).length < 2 ^ (prefixWord ++ tailWord_499941).sum := by decide
  have hdescent : baseEnd_499941 < baseStart_499941 := by decide
  rcases family_descends (prefixWord ++ tailWord_499941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499995 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_499995 : Nat := 118140960795 + 499995 * 2 ^ 59
def prefixEnd_499995 : Nat := 4983230072969 + 3 ^ 40 * 499995 * 2
def baseEnd_499995 : Nat := 171158506563251000642047

theorem tailTrace_499995 : CollatzResearch.WordTrace tailWord_499995 prefixEnd_499995 171158506563251000642047 := by
  unfold tailWord_499995
  simp only [CollatzResearch.WordTrace]
  refine ⟨18236315823610982192677439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12157543882407321461784959 18236315823610982192677439)
  ·
    refine ⟨27354473735416473289016159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18236315823610982192677439 27354473735416473289016159)
    ·
      refine ⟨41031710603124709933524239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27354473735416473289016159 41031710603124709933524239)
      ·
        refine ⟨61547565904687064900286359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41031710603124709933524239 61547565904687064900286359)
        ·
          refine ⟨92321348857030597350429539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61547565904687064900286359 92321348857030597350429539)
          ·
            refine ⟨138482023285545896025644309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92321348857030597350429539 138482023285545896025644309)
            ·
              refine ⟨6491344841509963876202077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138482023285545896025644309 6491344841509963876202077)
              ·
                refine ⟨2434254315566236453575779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6491344841509963876202077 2434254315566236453575779)
                ·
                  refine ⟨3651381473349354680363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434254315566236453575779 3651381473349354680363669)
                  ·
                    refine ⟨171158506563251000642047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3651381473349354680363669 171158506563251000642047)
                    ·
                      rfl

theorem cell22_499995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_499995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_499995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_499995 prefixEnd_499995 := by exact prefixLift 499995
  have htrace : WordTrace (prefixWord ++ tailWord_499995) baseStart_499995 baseEnd_499995 := by
    simpa [prefixWord, tailWord_499995, baseEnd_499995] using wordTrace_append hprefix tailTrace_499995
  have hstable : (prefixWord ++ tailWord_499995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499995).length < 2 ^ (prefixWord ++ tailWord_499995).sum := by decide
  have hdescent : baseEnd_499995 < baseStart_499995 := by decide
  rcases family_descends (prefixWord ++ tailWord_499995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500012 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_500012 : Nat := 118140960795 + 500012 * 2 ^ 59
def prefixEnd_500012 : Nat := 4983230072969 + 3 ^ 40 * 500012 * 2
def baseEnd_500012 : Nat := 171164326010668622966995

theorem tailTrace_500012 : CollatzResearch.WordTrace tailWord_500012 prefixEnd_500012 171164326010668622966995 := by
  unfold tailWord_500012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118467932274697048023145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12157957243032929397364193 9118467932274697048023145)
  ·
    refine ⟨6838850949206022786017359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9118467932274697048023145 6838850949206022786017359)
    ·
      refine ⟨10258276423809034179026039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838850949206022786017359 10258276423809034179026039)
      ·
        refine ⟨15387414635713551268539059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258276423809034179026039 15387414635713551268539059)
        ·
          refine ⟨23081121953570326902808589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15387414635713551268539059 23081121953570326902808589)
          ·
            refine ⟨8655420732588872588553221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23081121953570326902808589 8655420732588872588553221)
            ·
              refine ⟨1622891387360413610353729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8655420732588872588553221 1622891387360413610353729)
              ·
                refine ⟨1217168540520310207765297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622891387360413610353729 1217168540520310207765297)
                ·
                  refine ⟨912876405390232655823973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217168540520310207765297 912876405390232655823973)
                  ·
                    refine ⟨171164326010668622966995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912876405390232655823973 171164326010668622966995)
                    ·
                      rfl

theorem cell22_500012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_500012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500012 prefixEnd_500012 := by exact prefixLift 500012
  have htrace : WordTrace (prefixWord ++ tailWord_500012) baseStart_500012 baseEnd_500012 := by
    simpa [prefixWord, tailWord_500012, baseEnd_500012] using wordTrace_append hprefix tailTrace_500012
  have hstable : (prefixWord ++ tailWord_500012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500012).length < 2 ^ (prefixWord ++ tailWord_500012).sum := by decide
  have hdescent : baseEnd_500012 < baseStart_500012 := by decide
  rcases family_descends (prefixWord ++ tailWord_500012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500076 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_500076 : Nat := 118140960795 + 500076 * 2 ^ 59
def prefixEnd_500076 : Nat := 4983230072969 + 3 ^ 40 * 500076 * 2
def baseEnd_500076 : Nat := 171186234518593789366799

theorem tailTrace_500076 : CollatzResearch.WordTrace tailWord_500076 prefixEnd_500076 171186234518593789366799 := by
  unfold tailWord_500076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119635068158766513188041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12159513424211688684250721 9119635068158766513188041)
  ·
    refine ⟨6839726301119074884891031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9119635068158766513188041 6839726301119074884891031)
    ·
      refine ⟨10259589451678612327336547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839726301119074884891031 10259589451678612327336547)
      ·
        refine ⟨15389384177517918491004821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10259589451678612327336547 15389384177517918491004821)
        ·
          refine ⟨721377383321152429265851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15389384177517918491004821 721377383321152429265851)
          ·
            refine ⟨1082066074981728643898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721377383321152429265851 1082066074981728643898777)
            ·
              refine ⟨811549556236296482924083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082066074981728643898777 811549556236296482924083)
              ·
                refine ⟨1217324334354444724386125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811549556236296482924083 1217324334354444724386125)
                ·
                  refine ⟨456496625382916771644797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217324334354444724386125 456496625382916771644797)
                  ·
                    refine ⟨171186234518593789366799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456496625382916771644797 171186234518593789366799)
                    ·
                      rfl

theorem cell22_500076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_500076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500076 prefixEnd_500076 := by exact prefixLift 500076
  have htrace : WordTrace (prefixWord ++ tailWord_500076) baseStart_500076 baseEnd_500076 := by
    simpa [prefixWord, tailWord_500076, baseEnd_500076] using wordTrace_append hprefix tailTrace_500076
  have hstable : (prefixWord ++ tailWord_500076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500076).length < 2 ^ (prefixWord ++ tailWord_500076).sum := by decide
  have hdescent : baseEnd_500076 < baseStart_500076 := by decide
  rcases family_descends (prefixWord ++ tailWord_500076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500110 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_500110 : Nat := 118140960795 + 500110 * 2 ^ 59
def prefixEnd_500110 : Nat := 4983230072969 + 3 ^ 40 * 500110 * 2
def baseEnd_500110 : Nat := 171197873413429034016695

theorem tailTrace_500110 : CollatzResearch.WordTrace tailWord_500110 prefixEnd_500110 171197873413429034016695 := by
  unfold tailWord_500110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280063777274294604139223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12160340145462904555409189 2280063777274294604139223)
  ·
    refine ⟨3420095665911441906208835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280063777274294604139223 3420095665911441906208835)
    ·
      refine ⟨5130143498867162859313253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420095665911441906208835 5130143498867162859313253)
      ·
        refine ⟨961901906037593036121235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5130143498867162859313253 961901906037593036121235)
        ·
          refine ⟨1442852859056389554181853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961901906037593036121235 1442852859056389554181853)
          ·
            refine ⟨541069822146146082818195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442852859056389554181853 541069822146146082818195)
            ·
              refine ⟨811604733219219124227293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541069822146146082818195 811604733219219124227293)
              ·
                refine ⟨304351774957207171585235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811604733219219124227293 304351774957207171585235)
                ·
                  refine ⟨456527662435810757377853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304351774957207171585235 456527662435810757377853)
                  ·
                    refine ⟨171197873413429034016695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456527662435810757377853 171197873413429034016695)
                    ·
                      rfl

theorem cell22_500110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_500110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500110 prefixEnd_500110 := by exact prefixLift 500110
  have htrace : WordTrace (prefixWord ++ tailWord_500110) baseStart_500110 baseEnd_500110 := by
    simpa [prefixWord, tailWord_500110, baseEnd_500110] using wordTrace_append hprefix tailTrace_500110
  have hstable : (prefixWord ++ tailWord_500110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500110).length < 2 ^ (prefixWord ++ tailWord_500110).sum := by decide
  have hdescent : baseEnd_500110 < baseStart_500110 := by decide
  rcases family_descends (prefixWord ++ tailWord_500110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500119 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 1, 4]
def baseStart_500119 : Nat := 118140960795 + 500119 * 2 ^ 59
def prefixEnd_500119 : Nat := 4983230072969 + 3 ^ 40 * 500119 * 2
def baseEnd_500119 : Nat := 171200954297356010541667

theorem tailTrace_500119 : CollatzResearch.WordTrace tailWord_500119 prefixEnd_500119 171200954297356010541667 := by
  unfold tailWord_500119
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240838475161751370191411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12160558983441167580127607 18240838475161751370191411)
  ·
    refine ⟨27361257712742627055287117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18240838475161751370191411 27361257712742627055287117)
    ·
      refine ⟨10260471642278485145732669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27361257712742627055287117 10260471642278485145732669)
      ·
        refine ⟨3847676865854431929649751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10260471642278485145732669 3847676865854431929649751)
        ·
          refine ⟨5771515298781647894474627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847676865854431929649751 5771515298781647894474627)
          ·
            refine ⟨8657272948172471841711941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771515298781647894474627 8657272948172471841711941)
            ·
              refine ⟨1623238677782338470320989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8657272948172471841711941 1623238677782338470320989)
              ·
                refine ⟨608714504168376926370371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623238677782338470320989 608714504168376926370371)
                ·
                  refine ⟨913071756252565389555557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608714504168376926370371 913071756252565389555557)
                  ·
                    refine ⟨171200954297356010541667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913071756252565389555557 171200954297356010541667)
                    ·
                      rfl

theorem cell22_500119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_500119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500119 prefixEnd_500119 := by exact prefixLift 500119
  have htrace : WordTrace (prefixWord ++ tailWord_500119) baseStart_500119 baseEnd_500119 := by
    simpa [prefixWord, tailWord_500119, baseEnd_500119] using wordTrace_append hprefix tailTrace_500119
  have hstable : (prefixWord ++ tailWord_500119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500119).length < 2 ^ (prefixWord ++ tailWord_500119).sum := by decide
  have hdescent : baseEnd_500119 < baseStart_500119 := by decide
  rcases family_descends (prefixWord ++ tailWord_500119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500192 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_500192 : Nat := 118140960795 + 500192 * 2 ^ 59
def prefixEnd_500192 : Nat := 4983230072969 + 3 ^ 40 * 500192 * 2
def baseEnd_500192 : Nat := 171225943689208153466443

theorem tailTrace_500192 : CollatzResearch.WordTrace tailWord_500192 prefixEnd_500192 171225943689208153466443 := by
  unfold tailWord_500192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121750501948642418799415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12162334002598189891732553 9121750501948642418799415)
  ·
    refine ⟨13682625752922963628199123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9121750501948642418799415 13682625752922963628199123)
    ·
      refine ⟨20523938629384445442298685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682625752922963628199123 20523938629384445442298685)
      ·
        refine ⟨7696476986019167040862007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20523938629384445442298685 7696476986019167040862007)
        ·
          refine ⟨11544715479028750561293011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7696476986019167040862007 11544715479028750561293011)
          ·
            refine ⟨17317073218543125841939517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11544715479028750561293011 17317073218543125841939517)
            ·
              refine ⟨6493902456953672190727319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17317073218543125841939517 6493902456953672190727319)
              ·
                refine ⟨9740853685430508286090979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493902456953672190727319 9740853685430508286090979)
                ·
                  refine ⟨14611280528145762429136469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740853685430508286090979 14611280528145762429136469)
                  ·
                    refine ⟨171225943689208153466443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14611280528145762429136469 171225943689208153466443)
                    ·
                      rfl

theorem cell22_500192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_500192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500192 prefixEnd_500192 := by exact prefixLift 500192
  have htrace : WordTrace (prefixWord ++ tailWord_500192) baseStart_500192 baseEnd_500192 := by
    simpa [prefixWord, tailWord_500192, baseEnd_500192] using wordTrace_append hprefix tailTrace_500192
  have hstable : (prefixWord ++ tailWord_500192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500192).length < 2 ^ (prefixWord ++ tailWord_500192).sum := by decide
  have hdescent : baseEnd_500192 < baseStart_500192 := by decide
  rcases family_descends (prefixWord ++ tailWord_500192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500207 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 9]
def baseStart_500207 : Nat := 118140960795 + 500207 * 2 ^ 59
def prefixEnd_500207 : Nat := 4983230072969 + 3 ^ 40 * 500207 * 2
def baseEnd_500207 : Nat := 57077026165251038113799

theorem tailTrace_500207 : CollatzResearch.WordTrace tailWord_500207 prefixEnd_500207 57077026165251038113799 := by
  unfold tailWord_500207
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244048098842942399394875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162698732561961599596583 18244048098842942399394875)
  ·
    refine ⟨27366072148264413599092313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18244048098842942399394875 27366072148264413599092313)
    ·
      refine ⟨20524554111198310199319235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27366072148264413599092313 20524554111198310199319235)
      ·
        refine ⟨30786831166797465298978853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20524554111198310199319235 30786831166797465298978853)
        ·
          refine ⟨5772530843774524743558535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30786831166797465298978853 5772530843774524743558535)
          ·
            refine ⟨8658796265661787115337803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772530843774524743558535 8658796265661787115337803)
            ·
              refine ⟨12988194398492680673006705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658796265661787115337803 12988194398492680673006705)
              ·
                refine ⟨9741145798869510504755029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12988194398492680673006705 9741145798869510504755029)
                ·
                  refine ⟨57077026165251038113799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9741145798869510504755029 57077026165251038113799)
                  ·
                    rfl

theorem cell22_500207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_500207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500207 prefixEnd_500207 := by exact prefixLift 500207
  have htrace : WordTrace (prefixWord ++ tailWord_500207) baseStart_500207 baseEnd_500207 := by
    simpa [prefixWord, tailWord_500207, baseEnd_500207] using wordTrace_append hprefix tailTrace_500207
  have hstable : (prefixWord ++ tailWord_500207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500207).length < 2 ^ (prefixWord ++ tailWord_500207).sum := by decide
  have hdescent : baseEnd_500207 < baseStart_500207 := by decide
  rcases family_descends (prefixWord ++ tailWord_500207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500213 : List Nat := [1, 3, 5, 1, 2, 1, 3, 6]
def baseStart_500213 : Nat := 118140960795 + 500213 * 2 ^ 59
def prefixEnd_500213 : Nat := 4983230072969 + 3 ^ 40 * 500213 * 2
def baseEnd_500213 : Nat := 19025903602041233187931

theorem tailTrace_500213 : CollatzResearch.WordTrace tailWord_500213 prefixEnd_500213 19025903602041233187931 := by
  unfold tailWord_500213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244266936821205424113293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12162844624547470282742195 18244266936821205424113293)
  ·
    refine ⟨6841600101307952034042485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18244266936821205424113293 6841600101307952034042485)
    ·
      refine ⟨641400009497620503191483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6841600101307952034042485 641400009497620503191483)
      ·
        refine ⟨962100014246430754787225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641400009497620503191483 962100014246430754787225)
        ·
          refine ⟨721575010684823066090419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962100014246430754787225 721575010684823066090419)
          ·
            refine ⟨1082362516027234599135629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721575010684823066090419 1082362516027234599135629)
            ·
              refine ⟨405885943510212974675861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082362516027234599135629 405885943510212974675861)
              ·
                refine ⟨19025903602041233187931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405885943510212974675861 19025903602041233187931)
                ·
                  rfl

theorem cell22_500213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 6].length) (baseStart_500213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500213 prefixEnd_500213 := by exact prefixLift 500213
  have htrace : WordTrace (prefixWord ++ tailWord_500213) baseStart_500213 baseEnd_500213 := by
    simpa [prefixWord, tailWord_500213, baseEnd_500213] using wordTrace_append hprefix tailTrace_500213
  have hstable : (prefixWord ++ tailWord_500213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500213).length < 2 ^ (prefixWord ++ tailWord_500213).sum := by decide
  have hdescent : baseEnd_500213 < baseStart_500213 := by decide
  rcases family_descends (prefixWord ++ tailWord_500213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500299 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_500299 : Nat := 118140960795 + 500299 * 2 ^ 59
def prefixEnd_500299 : Nat := 4983230072969 + 3 ^ 40 * 500299 * 2
def baseEnd_500299 : Nat := 171262571975895541041115

theorem tailTrace_500299 : CollatzResearch.WordTrace tailWord_500299 prefixEnd_500299 171262571975895541041115 := by
  unfold tailWord_500299
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247403614509642111743951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12164935743006428074495967 18247403614509642111743951)
  ·
    refine ⟨27371105421764463167615927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18247403614509642111743951 27371105421764463167615927)
    ·
      refine ⟨41056658132646694751423891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27371105421764463167615927 41056658132646694751423891)
      ·
        refine ⟨61584987198970042127135837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41056658132646694751423891 61584987198970042127135837)
        ·
          refine ⟨23094370199613765797675939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61584987198970042127135837 23094370199613765797675939)
          ·
            refine ⟨34641555299420648696513909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23094370199613765797675939 34641555299420648696513909)
            ·
              refine ⟨3247645809320685815298179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34641555299420648696513909 3247645809320685815298179)
              ·
                refine ⟨4871468713981028722947269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247645809320685815298179 4871468713981028722947269)
                ·
                  refine ⟨913400383871442885552613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4871468713981028722947269 913400383871442885552613)
                  ·
                    refine ⟨171262571975895541041115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913400383871442885552613 171262571975895541041115)
                    ·
                      rfl

theorem cell22_500299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_500299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500299 prefixEnd_500299 := by exact prefixLift 500299
  have htrace : WordTrace (prefixWord ++ tailWord_500299) baseStart_500299 baseEnd_500299 := by
    simpa [prefixWord, tailWord_500299, baseEnd_500299] using wordTrace_append hprefix tailTrace_500299
  have hstable : (prefixWord ++ tailWord_500299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500299).length < 2 ^ (prefixWord ++ tailWord_500299).sum := by decide
  have hdescent : baseEnd_500299 < baseStart_500299 := by decide
  rcases family_descends (prefixWord ++ tailWord_500299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500322 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_500322 : Nat := 118140960795 + 500322 * 2 ^ 59
def prefixEnd_500322 : Nat := 4983230072969 + 3 ^ 40 * 500322 * 2
def baseEnd_500322 : Nat := 171270445345931147716045

theorem tailTrace_500322 : CollatzResearch.WordTrace tailWord_500322 prefixEnd_500322 171270445345931147716045 := by
  unfold tailWord_500322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562060623356579259957805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12165494995617544693220813 4562060623356579259957805)
  ·
    refine ⟨1710772733758717222484177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4562060623356579259957805 1710772733758717222484177)
    ·
      refine ⟨1283079550319037916863133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1710772733758717222484177 1283079550319037916863133)
      ·
        refine ⟨481154831369639218823675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1283079550319037916863133 481154831369639218823675)
        ·
          refine ⟨721732247054458828235513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481154831369639218823675 721732247054458828235513)
          ·
            refine ⟨541299185290844121176635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721732247054458828235513 541299185290844121176635)
            ·
              refine ⟨811948777936266181764953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541299185290844121176635 811948777936266181764953)
              ·
                refine ⟨608961583452199636323715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811948777936266181764953 608961583452199636323715)
                ·
                  refine ⟨913442375178299454485573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608961583452199636323715 913442375178299454485573)
                  ·
                    refine ⟨171270445345931147716045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913442375178299454485573 171270445345931147716045)
                    ·
                      rfl

theorem cell22_500322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_500322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500322 prefixEnd_500322 := by exact prefixLift 500322
  have htrace : WordTrace (prefixWord ++ tailWord_500322) baseStart_500322 baseEnd_500322 := by
    simpa [prefixWord, tailWord_500322, baseEnd_500322] using wordTrace_append hprefix tailTrace_500322
  have hstable : (prefixWord ++ tailWord_500322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500322).length < 2 ^ (prefixWord ++ tailWord_500322).sum := by decide
  have hdescent : baseEnd_500322 < baseStart_500322 := by decide
  rcases family_descends (prefixWord ++ tailWord_500322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500333 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_500333 : Nat := 118140960795 + 500333 * 2 ^ 59
def prefixEnd_500333 : Nat := 4983230072969 + 3 ^ 40 * 500333 * 2
def baseEnd_500333 : Nat := 171274210870730785691011

theorem tailTrace_500333 : CollatzResearch.WordTrace tailWord_500333 prefixEnd_500333 171274210870730785691011 := by
  unfold tailWord_500333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248643696386465918481653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12165762464257643945654435 18248643696386465918481653)
  ·
    refine ⟨1710810346536231179857655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18248643696386465918481653 1710810346536231179857655)
    ·
      refine ⟨2566215519804346769786483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710810346536231179857655 2566215519804346769786483)
      ·
        refine ⟨3849323279706520154679725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566215519804346769786483 3849323279706520154679725)
        ·
          refine ⟨1443496229889945058004897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3849323279706520154679725 1443496229889945058004897)
          ·
            refine ⟨1082622172417458793503673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443496229889945058004897 1082622172417458793503673)
            ·
              refine ⟨811966629313094095127755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082622172417458793503673 811966629313094095127755)
              ·
                refine ⟨1217949943969641142691633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811966629313094095127755 1217949943969641142691633)
                ·
                  refine ⟨913462457977230857018725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217949943969641142691633 913462457977230857018725)
                  ·
                    refine ⟨171274210870730785691011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913462457977230857018725 171274210870730785691011)
                    ·
                      rfl

theorem cell22_500333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_500333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500333 prefixEnd_500333 := by exact prefixLift 500333
  have htrace : WordTrace (prefixWord ++ tailWord_500333) baseStart_500333 baseEnd_500333 := by
    simpa [prefixWord, tailWord_500333, baseEnd_500333] using wordTrace_append hprefix tailTrace_500333
  have hstable : (prefixWord ++ tailWord_500333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500333).length < 2 ^ (prefixWord ++ tailWord_500333).sum := by decide
  have hdescent : baseEnd_500333 < baseStart_500333 := by decide
  rcases family_descends (prefixWord ++ tailWord_500333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500354 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_500354 : Nat := 118140960795 + 500354 * 2 ^ 59
def prefixEnd_500354 : Nat := 4983230072969 + 3 ^ 40 * 500354 * 2
def baseEnd_500354 : Nat := 57093799866631243638649

theorem tailTrace_500354 : CollatzResearch.WordTrace tailWord_500354 prefixEnd_500354 57093799866631243638649 := by
  unfold tailWord_500354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562352407327596626249029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12166273086206924336664077 4562352407327596626249029)
  ·
    refine ⟨855441076373924367421693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4562352407327596626249029 855441076373924367421693)
    ·
      refine ⟨320790403640221637783135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 855441076373924367421693 320790403640221637783135)
      ·
        refine ⟨481185605460332456674703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320790403640221637783135 481185605460332456674703)
        ·
          refine ⟨721778408190498685012055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481185605460332456674703 721778408190498685012055)
          ·
            refine ⟨1082667612285748027518083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721778408190498685012055 1082667612285748027518083)
            ·
              refine ⟨1624001418428622041277125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082667612285748027518083 1624001418428622041277125)
              ·
                refine ⟨304500265955366632739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1624001418428622041277125 304500265955366632739461)
                ·
                  refine ⟨57093799866631243638649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304500265955366632739461 57093799866631243638649)
                  ·
                    rfl

theorem cell22_500354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_500354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500354 prefixEnd_500354 := by exact prefixLift 500354
  have htrace : WordTrace (prefixWord ++ tailWord_500354) baseStart_500354 baseEnd_500354 := by
    simpa [prefixWord, tailWord_500354, baseEnd_500354] using wordTrace_append hprefix tailTrace_500354
  have hstable : (prefixWord ++ tailWord_500354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500354).length < 2 ^ (prefixWord ++ tailWord_500354).sum := by decide
  have hdescent : baseEnd_500354 < baseStart_500354 := by decide
  rcases family_descends (prefixWord ++ tailWord_500354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500376 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_500376 : Nat := 118140960795 + 500376 * 2 ^ 59
def prefixEnd_500376 : Nat := 4983230072969 + 3 ^ 40 * 500376 * 2
def baseEnd_500376 : Nat := 57096310216497668955293

theorem tailTrace_500376 : CollatzResearch.WordTrace tailWord_500376 prefixEnd_500376 57096310216497668955293 := by
  unfold tailWord_500376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125106017615342131148491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12166808023487122841531321 9125106017615342131148491)
  ·
    refine ⟨13687659026423013196722737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9125106017615342131148491 13687659026423013196722737)
    ·
      refine ⟨10265744269817259897542053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13687659026423013196722737 10265744269817259897542053)
      ·
        refine ⟨1924827050590736230789135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10265744269817259897542053 1924827050590736230789135)
        ·
          refine ⟨2887240575886104346183703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924827050590736230789135 2887240575886104346183703)
          ·
            refine ⟨4330860863829156519275555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887240575886104346183703 4330860863829156519275555)
            ·
              refine ⟨6496291295743734778913333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330860863829156519275555 6496291295743734778913333)
              ·
                refine ⟨609027308975975135523125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6496291295743734778913333 609027308975975135523125)
                ·
                  refine ⟨57096310216497668955293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609027308975975135523125 57096310216497668955293)
                  ·
                    rfl

theorem cell22_500376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_500376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500376 prefixEnd_500376 := by exact prefixLift 500376
  have htrace : WordTrace (prefixWord ++ tailWord_500376) baseStart_500376 baseEnd_500376 := by
    simpa [prefixWord, tailWord_500376, baseEnd_500376] using wordTrace_append hprefix tailTrace_500376
  have hstable : (prefixWord ++ tailWord_500376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500376).length < 2 ^ (prefixWord ++ tailWord_500376).sum := by decide
  have hdescent : baseEnd_500376 < baseStart_500376 := by decide
  rcases family_descends (prefixWord ++ tailWord_500376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500397 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_500397 : Nat := 118140960795 + 500397 * 2 ^ 59
def prefixEnd_500397 : Nat := 4983230072969 + 3 ^ 40 * 500397 * 2
def baseEnd_500397 : Nat := 171296119378655952090815

theorem tailTrace_500397 : CollatzResearch.WordTrace tailWord_500397 prefixEnd_500397 171296119378655952090815 := by
  unfold tailWord_500397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250977968154604848811445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12167318645436403232540963 18250977968154604848811445)
  ·
    refine ⟨1711029184514494204576073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18250977968154604848811445 1711029184514494204576073)
    ·
      refine ⟨1283271888385870653432055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1711029184514494204576073 1283271888385870653432055)
      ·
        refine ⟨1924907832578805980148083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283271888385870653432055 1924907832578805980148083)
        ·
          refine ⟨2887361748868208970222125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924907832578805980148083 2887361748868208970222125)
          ·
            refine ⟨1082760655825578363833297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2887361748868208970222125 1082760655825578363833297)
            ·
              refine ⟨812070491869183772874973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082760655825578363833297 812070491869183772874973)
              ·
                refine ⟨304526434450943914828115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812070491869183772874973 304526434450943914828115)
                ·
                  refine ⟨456789651676415872242173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304526434450943914828115 456789651676415872242173)
                  ·
                    refine ⟨171296119378655952090815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456789651676415872242173 171296119378655952090815)
                    ·
                      rfl

theorem cell22_500397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_500397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500397 prefixEnd_500397 := by exact prefixLift 500397
  have htrace : WordTrace (prefixWord ++ tailWord_500397) baseStart_500397 baseEnd_500397 := by
    simpa [prefixWord, tailWord_500397, baseEnd_500397] using wordTrace_append hprefix tailTrace_500397
  have hstable : (prefixWord ++ tailWord_500397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500397).length < 2 ^ (prefixWord ++ tailWord_500397).sum := by decide
  have hdescent : baseEnd_500397 < baseStart_500397 := by decide
  rcases family_descends (prefixWord ++ tailWord_500397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500419 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_500419 : Nat := 118140960795 + 500419 * 2 ^ 59
def prefixEnd_500419 : Nat := 4983230072969 + 3 ^ 40 * 500419 * 2
def baseEnd_500419 : Nat := 171303650428255228040747

theorem tailTrace_500419 : CollatzResearch.WordTrace tailWord_500419 prefixEnd_500419 171303650428255228040747 := by
  unfold tailWord_500419
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251780374074902606112311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12167853582716601737408207 18251780374074902606112311)
  ·
    refine ⟨27377670561112353909168467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18251780374074902606112311 27377670561112353909168467)
    ·
      refine ⟨41066505841668530863752701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27377670561112353909168467 41066505841668530863752701)
      ·
        refine ⟨15399939690625699073907263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41066505841668530863752701 15399939690625699073907263)
        ·
          refine ⟨23099909535938548610860895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399939690625699073907263 23099909535938548610860895)
          ·
            refine ⟨34649864303907822916291343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23099909535938548610860895 34649864303907822916291343)
            ·
              refine ⟨51974796455861734374437015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34649864303907822916291343 51974796455861734374437015)
              ·
                refine ⟨77962194683792601561655523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51974796455861734374437015 77962194683792601561655523)
                ·
                  refine ⟨116943292025688902342483285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77962194683792601561655523 116943292025688902342483285)
                  ·
                    refine ⟨171303650428255228040747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 116943292025688902342483285 171303650428255228040747)
                    ·
                      rfl

theorem cell22_500419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_500419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500419 prefixEnd_500419 := by exact prefixLift 500419
  have htrace : WordTrace (prefixWord ++ tailWord_500419) baseStart_500419 baseEnd_500419 := by
    simpa [prefixWord, tailWord_500419, baseEnd_500419] using wordTrace_append hprefix tailTrace_500419
  have hstable : (prefixWord ++ tailWord_500419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500419).length < 2 ^ (prefixWord ++ tailWord_500419).sum := by decide
  have hdescent : baseEnd_500419 < baseStart_500419 := by decide
  rcases family_descends (prefixWord ++ tailWord_500419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500453 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 4, 3]
def baseStart_500453 : Nat := 118140960795 + 500453 * 2 ^ 59
def prefixEnd_500453 : Nat := 4983230072969 + 3 ^ 40 * 500453 * 2
def baseEnd_500453 : Nat := 171315289323090472690643

theorem tailTrace_500453 : CollatzResearch.WordTrace tailWord_500453 prefixEnd_500453 171315289323090472690643 := by
  unfold tailWord_500453
  simp only [CollatzResearch.WordTrace]
  refine ⟨18253020455951726412850013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12168680303967817608566675 18253020455951726412850013)
  ·
    refine ⟨6844882670981897404818755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18253020455951726412850013 6844882670981897404818755)
    ·
      refine ⟨10267324006472846107228133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844882670981897404818755 10267324006472846107228133)
      ·
        refine ⟨1925123251213658645105275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10267324006472846107228133 1925123251213658645105275)
        ·
          refine ⟨2887684876820487967657913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925123251213658645105275 2887684876820487967657913)
          ·
            refine ⟨2165763657615365975743435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887684876820487967657913 2165763657615365975743435)
            ·
              refine ⟨3248645486423048963615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165763657615365975743435 3248645486423048963615153)
              ·
                refine ⟨2436484114817286722711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3248645486423048963615153 2436484114817286722711365)
                ·
                  refine ⟨456840771528241260508381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2436484114817286722711365 456840771528241260508381)
                  ·
                    refine ⟨171315289323090472690643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456840771528241260508381 171315289323090472690643)
                    ·
                      rfl

theorem cell22_500453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_500453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500453 prefixEnd_500453 := by exact prefixLift 500453
  have htrace : WordTrace (prefixWord ++ tailWord_500453) baseStart_500453 baseEnd_500453 := by
    simpa [prefixWord, tailWord_500453, baseEnd_500453] using wordTrace_append hprefix tailTrace_500453
  have hstable : (prefixWord ++ tailWord_500453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500453).length < 2 ^ (prefixWord ++ tailWord_500453).sum := by decide
  have hdescent : baseEnd_500453 < baseStart_500453 := by decide
  rcases family_descends (prefixWord ++ tailWord_500453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500466 : List Nat := [3, 2, 1, 3, 1, 2, 10]
def baseStart_500466 : Nat := 118140960795 + 500466 * 2 ^ 59
def prefixEnd_500466 : Nat := 4983230072969 + 3 ^ 40 * 500466 * 2
def baseEnd_500466 : Nat := 6345175536620843411689

theorem tailTrace_500466 : CollatzResearch.WordTrace tailWord_500466 prefixEnd_500466 6345175536620843411689 := by
  unfold tailWord_500466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563373651226157408268313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12168996403269753088715501 4563373651226157408268313)
  ·
    refine ⟨3422530238419618056201235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4563373651226157408268313 3422530238419618056201235)
    ·
      refine ⟨5133795357629427084301853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422530238419618056201235 5133795357629427084301853)
      ·
        refine ⟨1925173259111035156613195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5133795357629427084301853 1925173259111035156613195)
        ·
          refine ⟨2887759888666552734919793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925173259111035156613195 2887759888666552734919793)
          ·
            refine ⟨2165819916499914551189845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2887759888666552734919793 2165819916499914551189845)
            ·
              refine ⟨6345175536620843411689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2165819916499914551189845 6345175536620843411689)
              ·
                rfl

theorem cell22_500466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 10].length) (baseStart_500466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500466 prefixEnd_500466 := by exact prefixLift 500466
  have htrace : WordTrace (prefixWord ++ tailWord_500466) baseStart_500466 baseEnd_500466 := by
    simpa [prefixWord, tailWord_500466, baseEnd_500466] using wordTrace_append hprefix tailTrace_500466
  have hstable : (prefixWord ++ tailWord_500466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500466).length < 2 ^ (prefixWord ++ tailWord_500466).sum := by decide
  have hdescent : baseEnd_500466 < baseStart_500466 := by decide
  rcases family_descends (prefixWord ++ tailWord_500466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500470 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_500470 : Nat := 118140960795 + 500470 * 2 ^ 59
def prefixEnd_500470 : Nat := 4983230072969 + 3 ^ 40 * 500470 * 2
def baseEnd_500470 : Nat := 171321108770508095015591

theorem tailTrace_500470 : CollatzResearch.WordTrace tailWord_500470 prefixEnd_500470 171321108770508095015591 := by
  unfold tailWord_500470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140852531055633644763679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12169093664593425544145909 1140852531055633644763679)
  ·
    refine ⟨1711278796583450467145519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1140852531055633644763679 1711278796583450467145519)
    ·
      refine ⟨2566918194875175700718279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711278796583450467145519 2566918194875175700718279)
      ·
        refine ⟨3850377292312763551077419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566918194875175700718279 3850377292312763551077419)
        ·
          refine ⟨5775565938469145326616129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850377292312763551077419 5775565938469145326616129)
          ·
            refine ⟨4331674453851858994962097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775565938469145326616129 4331674453851858994962097)
            ·
              refine ⟨3248755840388894246221573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331674453851858994962097 3248755840388894246221573)
              ·
                refine ⟨609141720072917671166545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3248755840388894246221573 609141720072917671166545)
                ·
                  refine ⟨456856290054688253374909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609141720072917671166545 456856290054688253374909)
                  ·
                    refine ⟨171321108770508095015591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456856290054688253374909 171321108770508095015591)
                    ·
                      rfl

theorem cell22_500470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_500470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500470 prefixEnd_500470 := by exact prefixLift 500470
  have htrace : WordTrace (prefixWord ++ tailWord_500470) baseStart_500470 baseEnd_500470 := by
    simpa [prefixWord, tailWord_500470, baseEnd_500470] using wordTrace_append hprefix tailTrace_500470
  have hstable : (prefixWord ++ tailWord_500470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500470).length < 2 ^ (prefixWord ++ tailWord_500470).sum := by decide
  have hdescent : baseEnd_500470 < baseStart_500470 := by decide
  rcases family_descends (prefixWord ++ tailWord_500470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500487 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 2, 3]
def baseStart_500487 : Nat := 118140960795 + 500487 * 2 ^ 59
def prefixEnd_500487 : Nat := 4983230072969 + 3 ^ 40 * 500487 * 2
def baseEnd_500487 : Nat := 171326928217925717340539

theorem tailTrace_500487 : CollatzResearch.WordTrace tailWord_500487 prefixEnd_500487 171326928217925717340539 := by
  unfold tailWord_500487
  simp only [CollatzResearch.WordTrace]
  refine ⟨18254260537828550219587715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12169507025219033479725143 18254260537828550219587715)
  ·
    refine ⟨27381390806742825329381573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18254260537828550219587715 27381390806742825329381573)
    ·
      refine ⟨5134010776264279749259045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27381390806742825329381573 5134010776264279749259045)
      ·
        refine ⟨962627020549552452986071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5134010776264279749259045 962627020549552452986071)
        ·
          refine ⟨1443940530824328679479107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962627020549552452986071 1443940530824328679479107)
          ·
            refine ⟨2165910796236493019218661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443940530824328679479107 2165910796236493019218661)
            ·
              refine ⟨406108274294342441103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2165910796236493019218661 406108274294342441103499)
              ·
                refine ⟨609162411441513661655249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406108274294342441103499 609162411441513661655249)
                ·
                  refine ⟨456871808581135246241437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609162411441513661655249 456871808581135246241437)
                  ·
                    refine ⟨171326928217925717340539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456871808581135246241437 171326928217925717340539)
                    ·
                      rfl

theorem cell22_500487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_500487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500487 prefixEnd_500487 := by exact prefixLift 500487
  have htrace : WordTrace (prefixWord ++ tailWord_500487) baseStart_500487 baseEnd_500487 := by
    simpa [prefixWord, tailWord_500487, baseEnd_500487] using wordTrace_append hprefix tailTrace_500487
  have hstable : (prefixWord ++ tailWord_500487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500487).length < 2 ^ (prefixWord ++ tailWord_500487).sum := by decide
  have hdescent : baseEnd_500487 < baseStart_500487 := by decide
  rcases family_descends (prefixWord ++ tailWord_500487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500515 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 1, 3]
def baseStart_500515 : Nat := 118140960795 + 500515 * 2 ^ 59
def prefixEnd_500515 : Nat := 4983230072969 + 3 ^ 40 * 500515 * 2
def baseEnd_500515 : Nat := 171336513190142977640453

theorem tailTrace_500515 : CollatzResearch.WordTrace tailWord_500515 prefixEnd_500515 171336513190142977640453 := by
  unfold tailWord_500515
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255281781727111001606999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12170187854484740667737999 18255281781727111001606999)
  ·
    refine ⟨27382922672590666502410499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255281781727111001606999 27382922672590666502410499)
    ·
      refine ⟨41074384008885999753615749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27382922672590666502410499 41074384008885999753615749)
      ·
        refine ⟨7701447001666124953802953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41074384008885999753615749 7701447001666124953802953)
        ·
          refine ⟨5776085251249593715352215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701447001666124953802953 5776085251249593715352215)
          ·
            refine ⟨8664127876874390573028323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776085251249593715352215 8664127876874390573028323)
            ·
              refine ⟨12996191815311585859542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664127876874390573028323 12996191815311585859542485)
              ·
                refine ⟨304598245671365293583027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12996191815311585859542485 304598245671365293583027)
                ·
                  refine ⟨456897368507047940374541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304598245671365293583027 456897368507047940374541)
                  ·
                    refine ⟨171336513190142977640453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456897368507047940374541 171336513190142977640453)
                    ·
                      rfl

theorem cell22_500515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 3].length) (baseStart_500515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500515 prefixEnd_500515 := by exact prefixLift 500515
  have htrace : WordTrace (prefixWord ++ tailWord_500515) baseStart_500515 baseEnd_500515 := by
    simpa [prefixWord, tailWord_500515, baseEnd_500515] using wordTrace_append hprefix tailTrace_500515
  have hstable : (prefixWord ++ tailWord_500515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500515).length < 2 ^ (prefixWord ++ tailWord_500515).sum := by decide
  have hdescent : baseEnd_500515 < baseStart_500515 := by decide
  rcases family_descends (prefixWord ++ tailWord_500515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500543 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_500543 : Nat := 118140960795 + 500543 * 2 ^ 59
def prefixEnd_500543 : Nat := 4983230072969 + 3 ^ 40 * 500543 * 2
def baseEnd_500543 : Nat := 171346098162360237940367

theorem tailTrace_500543 : CollatzResearch.WordTrace tailWord_500543 prefixEnd_500543 171346098162360237940367 := by
  unfold tailWord_500543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256303025625671783626283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12170868683750447855750855 18256303025625671783626283)
  ·
    refine ⟨27384454538438507675439425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18256303025625671783626283 27384454538438507675439425)
    ·
      refine ⟨20538340903828880756579569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27384454538438507675439425 20538340903828880756579569)
      ·
        refine ⟨15403755677871660567434677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20538340903828880756579569 15403755677871660567434677)
        ·
          refine ⟨1444102094800468178197001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15403755677871660567434677 1444102094800468178197001)
          ·
            refine ⟨1083076571100351133647751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444102094800468178197001 1083076571100351133647751)
            ·
              refine ⟨1624614856650526700471627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083076571100351133647751 1624614856650526700471627)
              ·
                refine ⟨2436922284975790050707441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624614856650526700471627 2436922284975790050707441)
                ·
                  refine ⟨1827691713731842538030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436922284975790050707441 1827691713731842538030581)
                  ·
                    refine ⟨171346098162360237940367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1827691713731842538030581 171346098162360237940367)
                    ·
                      rfl

theorem cell22_500543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_500543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500543 prefixEnd_500543 := by exact prefixLift 500543
  have htrace : WordTrace (prefixWord ++ tailWord_500543) baseStart_500543 baseEnd_500543 := by
    simpa [prefixWord, tailWord_500543, baseEnd_500543] using wordTrace_append hprefix tailTrace_500543
  have hstable : (prefixWord ++ tailWord_500543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500543).length < 2 ^ (prefixWord ++ tailWord_500543).sum := by decide
  have hdescent : baseEnd_500543 < baseStart_500543 := by decide
  rcases family_descends (prefixWord ++ tailWord_500543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_500571 : Nat := 118140960795 + 500571 * 2 ^ 59
def prefixEnd_500571 : Nat := 4983230072969 + 3 ^ 40 * 500571 * 2
def baseEnd_500571 : Nat := 171355683134577498240281

theorem tailTrace_500571 : CollatzResearch.WordTrace tailWord_500571 prefixEnd_500571 171355683134577498240281 := by
  unfold tailWord_500571
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257324269524232565645567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171549513016155043763711 18257324269524232565645567)
  ·
    refine ⟨27385986404286348848468351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18257324269524232565645567 27385986404286348848468351)
    ·
      refine ⟨41078979606429523272702527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27385986404286348848468351 41078979606429523272702527)
      ·
        refine ⟨61618469409644284909053791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41078979606429523272702527 61618469409644284909053791)
        ·
          refine ⟨92427704114466427363580687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61618469409644284909053791 92427704114466427363580687)
          ·
            refine ⟨138641556171699641045371031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92427704114466427363580687 138641556171699641045371031)
            ·
              refine ⟨207962334257549461568056547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138641556171699641045371031 207962334257549461568056547)
              ·
                refine ⟨311943501386324192352084821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207962334257549461568056547 311943501386324192352084821)
                ·
                  refine ⟨1827793953435493314562997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 311943501386324192352084821 1827793953435493314562997)
                  ·
                    refine ⟨171355683134577498240281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1827793953435493314562997 171355683134577498240281)
                    ·
                      rfl

theorem cell22_500571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_500571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500571 prefixEnd_500571 := by exact prefixLift 500571
  have htrace : WordTrace (prefixWord ++ tailWord_500571) baseStart_500571 baseEnd_500571 := by
    simpa [prefixWord, tailWord_500571, baseEnd_500571] using wordTrace_append hprefix tailTrace_500571
  have hstable : (prefixWord ++ tailWord_500571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500571).length < 2 ^ (prefixWord ++ tailWord_500571).sum := by decide
  have hdescent : baseEnd_500571 < baseStart_500571 := by decide
  rcases family_descends (prefixWord ++ tailWord_500571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500605 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_500605 : Nat := 118140960795 + 500605 * 2 ^ 59
def prefixEnd_500605 : Nat := 4983230072969 + 3 ^ 40 * 500605 * 2
def baseEnd_500605 : Nat := 171367322029412742890177

theorem tailTrace_500605 : CollatzResearch.WordTrace tailWord_500605 prefixEnd_500605 171367322029412742890177 := by
  unfold tailWord_500605
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258564351401056372383269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12172376234267370914922179 18258564351401056372383269)
  ·
    refine ⟨3423480815887698069821863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18258564351401056372383269 3423480815887698069821863)
    ·
      refine ⟨5135221223831547104732795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423480815887698069821863 5135221223831547104732795)
      ·
        refine ⟨7702831835747320657099193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135221223831547104732795 7702831835747320657099193)
        ·
          refine ⟨5777123876810490492824395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7702831835747320657099193 5777123876810490492824395)
          ·
            refine ⟨8665685815215735739236593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777123876810490492824395 8665685815215735739236593)
            ·
              refine ⟨6499264361411801804427445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665685815215735739236593 6499264361411801804427445)
              ·
                refine ⟨609306033882356419165073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6499264361411801804427445 609306033882356419165073)
                ·
                  refine ⟨456979525411767314373805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609306033882356419165073 456979525411767314373805)
                  ·
                    refine ⟨171367322029412742890177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456979525411767314373805 171367322029412742890177)
                    ·
                      rfl

theorem cell22_500605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_500605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500605 prefixEnd_500605 := by exact prefixLift 500605
  have htrace : WordTrace (prefixWord ++ tailWord_500605) baseStart_500605 baseEnd_500605 := by
    simpa [prefixWord, tailWord_500605, baseEnd_500605] using wordTrace_append hprefix tailTrace_500605
  have hstable : (prefixWord ++ tailWord_500605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500605).length < 2 ^ (prefixWord ++ tailWord_500605).sum := by decide
  have hdescent : baseEnd_500605 < baseStart_500605 := by decide
  rcases family_descends (prefixWord ++ tailWord_500605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500701 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_500701 : Nat := 118140960795 + 500701 * 2 ^ 59
def prefixEnd_500701 : Nat := 4983230072969 + 3 ^ 40 * 500701 * 2
def baseEnd_500701 : Nat := 171400184791300492489883

theorem tailTrace_500701 : CollatzResearch.WordTrace tailWord_500701 prefixEnd_500701 171400184791300492489883 := by
  unfold tailWord_500701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262065759053264767877957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12174710506035509845251971 18262065759053264767877957)
  ·
    refine ⟨3424137329822487143977117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18262065759053264767877957 3424137329822487143977117)
    ·
      refine ⟨1284051498683432678991419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3424137329822487143977117 1284051498683432678991419)
      ·
        refine ⟨1926077248025149018487129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284051498683432678991419 1926077248025149018487129)
        ·
          refine ⟨1444557936018861763865347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926077248025149018487129 1444557936018861763865347)
          ·
            refine ⟨2166836904028292645798021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444557936018861763865347 2166836904028292645798021)
            ·
              refine ⟨406281919505304871087129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2166836904028292645798021 406281919505304871087129)
              ·
                refine ⟨304711439628978653315347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406281919505304871087129 304711439628978653315347)
                ·
                  refine ⟨457067159443467979973021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304711439628978653315347 457067159443467979973021)
                  ·
                    refine ⟨171400184791300492489883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457067159443467979973021 171400184791300492489883)
                    ·
                      rfl

theorem cell22_500701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_500701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500701 prefixEnd_500701 := by exact prefixLift 500701
  have htrace : WordTrace (prefixWord ++ tailWord_500701) baseStart_500701 baseEnd_500701 := by
    simpa [prefixWord, tailWord_500701, baseEnd_500701] using wordTrace_append hprefix tailTrace_500701
  have hstable : (prefixWord ++ tailWord_500701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500701).length < 2 ^ (prefixWord ++ tailWord_500701).sum := by decide
  have hdescent : baseEnd_500701 < baseStart_500701 := by decide
  rcases family_descends (prefixWord ++ tailWord_500701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500744 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_500744 : Nat := 118140960795 + 500744 * 2 ^ 59
def prefixEnd_500744 : Nat := 4983230072969 + 3 ^ 40 * 500744 * 2
def baseEnd_500744 : Nat := 171414904570062713664751

theorem tailTrace_500744 : CollatzResearch.WordTrace tailWord_500744 prefixEnd_500744 171414904570062713664751 := by
  unfold tailWord_500744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131817048948741555846643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12175756065264988741128857 9131817048948741555846643)
  ·
    refine ⟨13697725573423112333769965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131817048948741555846643 13697725573423112333769965)
    ·
      refine ⟨5136647090033667125163737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13697725573423112333769965 5136647090033667125163737)
      ·
        refine ⟨3852485317525250343872803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5136647090033667125163737 3852485317525250343872803)
        ·
          refine ⟨5778727976287875515809205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852485317525250343872803 5778727976287875515809205)
          ·
            refine ⟨541755747776988329607113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5778727976287875515809205 541755747776988329607113)
            ·
              refine ⟨406316810832741247205335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541755747776988329607113 406316810832741247205335)
              ·
                refine ⟨609475216249111870808003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406316810832741247205335 609475216249111870808003)
                ·
                  refine ⟨914212824373667806212005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609475216249111870808003 914212824373667806212005)
                  ·
                    refine ⟨171414904570062713664751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914212824373667806212005 171414904570062713664751)
                    ·
                      rfl

theorem cell22_500744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_500744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500744 prefixEnd_500744 := by exact prefixLift 500744
  have htrace : WordTrace (prefixWord ++ tailWord_500744) baseStart_500744 baseEnd_500744 := by
    simpa [prefixWord, tailWord_500744, baseEnd_500744] using wordTrace_append hprefix tailTrace_500744
  have hstable : (prefixWord ++ tailWord_500744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500744).length < 2 ^ (prefixWord ++ tailWord_500744).sum := by decide
  have hdescent : baseEnd_500744 < baseStart_500744 := by decide
  rcases family_descends (prefixWord ++ tailWord_500744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500757 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_500757 : Nat := 118140960795 + 500757 * 2 ^ 59
def prefixEnd_500757 : Nat := 4983230072969 + 3 ^ 40 * 500757 * 2
def baseEnd_500757 : Nat := 171419354735735013089711

theorem tailTrace_500757 : CollatzResearch.WordTrace tailWord_500757 prefixEnd_500757 171419354735735013089711 := by
  unfold tailWord_500757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18264108246850386331916525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12176072164566924221277683 18264108246850386331916525)
  ·
    refine ⟨6849040592568894874468697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18264108246850386331916525 6849040592568894874468697)
    ·
      refine ⟨5136780444426671155851523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849040592568894874468697 5136780444426671155851523)
      ·
        refine ⟨7705170666640006733777285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136780444426671155851523 7705170666640006733777285)
        ·
          refine ⟨1444719499995001262583241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7705170666640006733777285 1444719499995001262583241)
          ·
            refine ⟨1083539624996250946937431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444719499995001262583241 1083539624996250946937431)
            ·
              refine ⟨1625309437494376420406147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083539624996250946937431 1625309437494376420406147)
              ·
                refine ⟨2437964156241564630609221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625309437494376420406147 2437964156241564630609221)
                ·
                  refine ⟨457118279295293368239229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2437964156241564630609221 457118279295293368239229)
                  ·
                    refine ⟨171419354735735013089711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457118279295293368239229 171419354735735013089711)
                    ·
                      rfl

theorem cell22_500757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_500757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500757 prefixEnd_500757 := by exact prefixLift 500757
  have htrace : WordTrace (prefixWord ++ tailWord_500757) baseStart_500757 baseEnd_500757 := by
    simpa [prefixWord, tailWord_500757, baseEnd_500757] using wordTrace_append hprefix tailTrace_500757
  have hstable : (prefixWord ++ tailWord_500757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500757).length < 2 ^ (prefixWord ++ tailWord_500757).sum := by decide
  have hdescent : baseEnd_500757 < baseStart_500757 := by decide
  rcases family_descends (prefixWord ++ tailWord_500757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500783 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_500783 : Nat := 118140960795 + 500783 * 2 ^ 59
def prefixEnd_500783 : Nat := 4983230072969 + 3 ^ 40 * 500783 * 2
def baseEnd_500783 : Nat := 171428255067079611939631

theorem tailTrace_500783 : CollatzResearch.WordTrace tailWord_500783 prefixEnd_500783 171428255067079611939631 := by
  unfold tailWord_500783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265056544756192772363003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12176704363170795181575335 18265056544756192772363003)
  ·
    refine ⟨27397584817134289158544505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18265056544756192772363003 27397584817134289158544505)
    ·
      refine ⟨20548188612850716868908379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27397584817134289158544505 20548188612850716868908379)
      ·
        refine ⟨30822282919276075303362569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20548188612850716868908379 30822282919276075303362569)
        ·
          refine ⟨23116712189457056477521927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30822282919276075303362569 23116712189457056477521927)
          ·
            refine ⟨34675068284185584716282891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116712189457056477521927 34675068284185584716282891)
            ·
              refine ⟨52012602426278377074424337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34675068284185584716282891 52012602426278377074424337)
              ·
                refine ⟨39009451819708782805818253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52012602426278377074424337 39009451819708782805818253)
                ·
                  refine ⟨14628544432390793552181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39009451819708782805818253 14628544432390793552181845)
                  ·
                    refine ⟨171428255067079611939631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14628544432390793552181845 171428255067079611939631)
                    ·
                      rfl

theorem cell22_500783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_500783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500783 prefixEnd_500783 := by exact prefixLift 500783
  have htrace : WordTrace (prefixWord ++ tailWord_500783) baseStart_500783 baseEnd_500783 := by
    simpa [prefixWord, tailWord_500783, baseEnd_500783] using wordTrace_append hprefix tailTrace_500783
  have hstable : (prefixWord ++ tailWord_500783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500783).length < 2 ^ (prefixWord ++ tailWord_500783).sum := by decide
  have hdescent : baseEnd_500783 < baseStart_500783 := by decide
  rcases family_descends (prefixWord ++ tailWord_500783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500892 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_500892 : Nat := 118140960795 + 500892 * 2 ^ 59
def prefixEnd_500892 : Nat := 4983230072969 + 3 ^ 40 * 500892 * 2
def baseEnd_500892 : Nat := 171465567994639660964297

theorem tailTrace_500892 : CollatzResearch.WordTrace tailWord_500892 prefixEnd_500892 171465567994639660964297 := by
  unfold tailWord_500892
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134516050680652194040465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12179354734240869592053953 9134516050680652194040465)
  ·
    refine ⟨6850887038010489145530349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9134516050680652194040465 6850887038010489145530349)
    ·
      refine ⟨2569082639253933429573881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6850887038010489145530349 2569082639253933429573881)
      ·
        refine ⟨1926811979440450072180411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2569082639253933429573881 1926811979440450072180411)
        ·
          refine ⟨2890217969160675108270617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926811979440450072180411 2890217969160675108270617)
          ·
            refine ⟨2167663476870506331202963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890217969160675108270617 2167663476870506331202963)
            ·
              refine ⟨3251495215305759496804445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167663476870506331202963 3251495215305759496804445)
              ·
                refine ⟨1219310705739659811301667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251495215305759496804445 1219310705739659811301667)
                ·
                  refine ⟨1828966058609489716952501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219310705739659811301667 1828966058609489716952501)
                  ·
                    refine ⟨171465567994639660964297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1828966058609489716952501 171465567994639660964297)
                    ·
                      rfl

theorem cell22_500892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_500892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500892 prefixEnd_500892 := by exact prefixLift 500892
  have htrace : WordTrace (prefixWord ++ tailWord_500892) baseStart_500892 baseEnd_500892 := by
    simpa [prefixWord, tailWord_500892, baseEnd_500892] using wordTrace_append hprefix tailTrace_500892
  have hstable : (prefixWord ++ tailWord_500892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500892).length < 2 ^ (prefixWord ++ tailWord_500892).sum := by decide
  have hdescent : baseEnd_500892 < baseStart_500892 := by decide
  rcases family_descends (prefixWord ++ tailWord_500892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500894 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_500894 : Nat := 118140960795 + 500894 * 2 ^ 59
def prefixEnd_500894 : Nat := 4983230072969 + 3 ^ 40 * 500894 * 2
def baseEnd_500894 : Nat := 57155417545170774138097

theorem tailTrace_500894 : CollatzResearch.WordTrace tailWord_500894 prefixEnd_500894 57155417545170774138097 := by
  unfold tailWord_500894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283638130919257341206717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12179403364902705819769157 2283638130919257341206717)
  ·
    refine ⟨856364299094721502952519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2283638130919257341206717 856364299094721502952519)
    ·
      refine ⟨1284546448642082254428779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856364299094721502952519 1284546448642082254428779)
      ·
        refine ⟨1926819672963123381643169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284546448642082254428779 1926819672963123381643169)
        ·
          refine ⟨1445114754722342536232377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926819672963123381643169 1445114754722342536232377)
          ·
            refine ⟨1083836066041756902174283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445114754722342536232377 1083836066041756902174283)
            ·
              refine ⟨1625754099062635353261425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083836066041756902174283 1625754099062635353261425)
              ·
                refine ⟨1219315574296976514946069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625754099062635353261425 1219315574296976514946069)
                ·
                  refine ⟨57155417545170774138097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1219315574296976514946069 57155417545170774138097)
                  ·
                    rfl

theorem cell22_500894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_500894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500894 prefixEnd_500894 := by exact prefixLift 500894
  have htrace : WordTrace (prefixWord ++ tailWord_500894) baseStart_500894 baseEnd_500894 := by
    simpa [prefixWord, tailWord_500894, baseEnd_500894] using wordTrace_append hprefix tailTrace_500894
  have hstable : (prefixWord ++ tailWord_500894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500894).length < 2 ^ (prefixWord ++ tailWord_500894).sum := by decide
  have hdescent : baseEnd_500894 < baseStart_500894 := by decide
  rcases family_descends (prefixWord ++ tailWord_500894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500926 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_500926 : Nat := 118140960795 + 500926 * 2 ^ 59
def prefixEnd_500926 : Nat := 4983230072969 + 3 ^ 40 * 500926 * 2
def baseEnd_500926 : Nat := 171477206889474905614193

theorem tailTrace_500926 : CollatzResearch.WordTrace tailWord_500926 prefixEnd_500926 171477206889474905614193 := by
  unfold tailWord_500926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283784022904766024352329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12180181455492085463212421 2283784022904766024352329)
  ·
    refine ⟨1712838017178574518264247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2283784022904766024352329 1712838017178574518264247)
    ·
      refine ⟨2569257025767861777396371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712838017178574518264247 2569257025767861777396371)
      ·
        refine ⟨3853885538651792666094557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569257025767861777396371 3853885538651792666094557)
        ·
          refine ⟨1445207076994422249785459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3853885538651792666094557 1445207076994422249785459)
          ·
            refine ⟨2167810615491633374678189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445207076994422249785459 2167810615491633374678189)
            ·
              refine ⟨812928980809362515504321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2167810615491633374678189 812928980809362515504321)
              ·
                refine ⟨609696735607021886628241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812928980809362515504321 609696735607021886628241)
                ·
                  refine ⟨457272551705266414971181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609696735607021886628241 457272551705266414971181)
                  ·
                    refine ⟨171477206889474905614193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457272551705266414971181 171477206889474905614193)
                    ·
                      rfl

theorem cell22_500926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_500926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500926 prefixEnd_500926 := by exact prefixLift 500926
  have htrace : WordTrace (prefixWord ++ tailWord_500926) baseStart_500926 baseEnd_500926 := by
    simpa [prefixWord, tailWord_500926, baseEnd_500926] using wordTrace_append hprefix tailTrace_500926
  have hstable : (prefixWord ++ tailWord_500926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500926).length < 2 ^ (prefixWord ++ tailWord_500926).sum := by decide
  have hdescent : baseEnd_500926 < baseStart_500926 := by decide
  rcases family_descends (prefixWord ++ tailWord_500926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500935 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_500935 : Nat := 118140960795 + 500935 * 2 ^ 59
def prefixEnd_500935 : Nat := 4983230072969 + 3 ^ 40 * 500935 * 2
def baseEnd_500935 : Nat := 171480287773401882139165

theorem tailTrace_500935 : CollatzResearch.WordTrace tailWord_500935 prefixEnd_500935 171480287773401882139165 := by
  unfold tailWord_500935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270600440205522731896259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12180400293470348487930839 18270600440205522731896259)
  ·
    refine ⟨27405900660308284097844389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18270600440205522731896259 27405900660308284097844389)
    ·
      refine ⟨5138606373807803268345823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27405900660308284097844389 5138606373807803268345823)
      ·
        refine ⟨7707909560711704902518735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138606373807803268345823 7707909560711704902518735)
        ·
          refine ⟨11561864341067557353778103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707909560711704902518735 11561864341067557353778103)
          ·
            refine ⟨17342796511601336030667155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561864341067557353778103 17342796511601336030667155)
            ·
              refine ⟨26014194767402004046000733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17342796511601336030667155 26014194767402004046000733)
              ·
                refine ⟨9755323037775751517250275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26014194767402004046000733 9755323037775751517250275)
                ·
                  refine ⟨14632984556663627275875413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9755323037775751517250275 14632984556663627275875413)
                  ·
                    refine ⟨171480287773401882139165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14632984556663627275875413 171480287773401882139165)
                    ·
                      rfl

theorem cell22_500935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_500935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500935 prefixEnd_500935 := by exact prefixLift 500935
  have htrace : WordTrace (prefixWord ++ tailWord_500935) baseStart_500935 baseEnd_500935 := by
    simpa [prefixWord, tailWord_500935, baseEnd_500935] using wordTrace_append hprefix tailTrace_500935
  have hstable : (prefixWord ++ tailWord_500935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500935).length < 2 ^ (prefixWord ++ tailWord_500935).sum := by decide
  have hdescent : baseEnd_500935 < baseStart_500935 := by decide
  rcases family_descends (prefixWord ++ tailWord_500935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500971 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 1, 3]
def baseStart_500971 : Nat := 118140960795 + 500971 * 2 ^ 59
def prefixEnd_500971 : Nat := 4983230072969 + 3 ^ 40 * 500971 * 2
def baseEnd_500971 : Nat := 171492611309109788239055

theorem tailTrace_500971 : CollatzResearch.WordTrace tailWord_500971 prefixEnd_500971 171492611309109788239055 := by
  unfold tailWord_500971
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271913468075100880206767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12181275645383400586804511 18271913468075100880206767)
  ·
    refine ⟨27407870202112651320310151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18271913468075100880206767 27407870202112651320310151)
    ·
      refine ⟨41111805303168976980465227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27407870202112651320310151 41111805303168976980465227)
      ·
        refine ⟨61667707954753465470697841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41111805303168976980465227 61667707954753465470697841)
        ·
          refine ⟨46250780966065099103023381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61667707954753465470697841 46250780966065099103023381)
          ·
            refine ⟨2168005357784301520454221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46250780966065099103023381 2168005357784301520454221)
            ·
              refine ⟨813002009169113070170333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2168005357784301520454221 813002009169113070170333)
              ·
                refine ⟨304875753438417401313875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813002009169113070170333 304875753438417401313875)
                ·
                  refine ⟨457313630157626101970813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304875753438417401313875 457313630157626101970813)
                  ·
                    refine ⟨171492611309109788239055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457313630157626101970813 171492611309109788239055)
                    ·
                      rfl

theorem cell22_500971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 3].length) (baseStart_500971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500971 prefixEnd_500971 := by exact prefixLift 500971
  have htrace : WordTrace (prefixWord ++ tailWord_500971) baseStart_500971 baseEnd_500971 := by
    simpa [prefixWord, tailWord_500971, baseEnd_500971] using wordTrace_append hprefix tailTrace_500971
  have hstable : (prefixWord ++ tailWord_500971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500971).length < 2 ^ (prefixWord ++ tailWord_500971).sum := by decide
  have hdescent : baseEnd_500971 < baseStart_500971 := by decide
  rcases family_descends (prefixWord ++ tailWord_500971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500988 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_500988 : Nat := 118140960795 + 500988 * 2 ^ 59
def prefixEnd_500988 : Nat := 4983230072969 + 3 ^ 40 * 500988 * 2
def baseEnd_500988 : Nat := 171498430756527410564003

theorem tailTrace_500988 : CollatzResearch.WordTrace tailWord_500988 prefixEnd_500988 171498430756527410564003 := by
  unfold tailWord_500988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136266754506756391787809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12181689006009008522383745 9136266754506756391787809)
  ·
    refine ⟨6852200065880067293840857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9136266754506756391787809 6852200065880067293840857)
    ·
      refine ⟨5139150049410050470380643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6852200065880067293840857 5139150049410050470380643)
      ·
        refine ⟨7708725074115075705570965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139150049410050470380643 7708725074115075705570965)
        ·
          refine ⟨361346487849144173698639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7708725074115075705570965 361346487849144173698639)
          ·
            refine ⟨542019731773716260547959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361346487849144173698639 542019731773716260547959)
            ·
              refine ⟨813029597660574390821939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542019731773716260547959 813029597660574390821939)
              ·
                refine ⟨1219544396490861586232909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813029597660574390821939 1219544396490861586232909)
                ·
                  refine ⟨457329148684073094837341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219544396490861586232909 457329148684073094837341)
                  ·
                    refine ⟨171498430756527410564003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457329148684073094837341 171498430756527410564003)
                    ·
                      rfl

theorem cell22_500988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_500988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500988 prefixEnd_500988 := by exact prefixLift 500988
  have htrace : WordTrace (prefixWord ++ tailWord_500988) baseStart_500988 baseEnd_500988 := by
    simpa [prefixWord, tailWord_500988, baseEnd_500988] using wordTrace_append hprefix tailTrace_500988
  have hstable : (prefixWord ++ tailWord_500988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500988).length < 2 ^ (prefixWord ++ tailWord_500988).sum := by decide
  have hdescent : baseEnd_500988 < baseStart_500988 := by decide
  rcases family_descends (prefixWord ++ tailWord_500988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500997 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_500997 : Nat := 118140960795 + 500997 * 2 ^ 59
def prefixEnd_500997 : Nat := 4983230072969 + 3 ^ 40 * 500997 * 2
def baseEnd_500997 : Nat := 171501511640454387088975

theorem tailTrace_500997 : CollatzResearch.WordTrace tailWord_500997 prefixEnd_500997 171501511640454387088975 := by
  unfold tailWord_500997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272861765980907320653245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12181907843987271547102163 18272861765980907320653245)
  ·
    refine ⟨6852323162242840245244967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18272861765980907320653245 6852323162242840245244967)
    ·
      refine ⟨10278484743364260367867451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852323162242840245244967 10278484743364260367867451)
      ·
        refine ⟨15417727115046390551801177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10278484743364260367867451 15417727115046390551801177)
        ·
          refine ⟨11563295336284792913850883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15417727115046390551801177 11563295336284792913850883)
          ·
            refine ⟨17344943004427189370776325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563295336284792913850883 17344943004427189370776325)
            ·
              refine ⟨3252176813330098007020561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17344943004427189370776325 3252176813330098007020561)
              ·
                refine ⟨2439132609997573505265421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252176813330098007020561 2439132609997573505265421)
                ·
                  refine ⟨914674728749090064474533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2439132609997573505265421 914674728749090064474533)
                  ·
                    refine ⟨171501511640454387088975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914674728749090064474533 171501511640454387088975)
                    ·
                      rfl

theorem cell22_500997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_500997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_500997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_500997 prefixEnd_500997 := by exact prefixLift 500997
  have htrace : WordTrace (prefixWord ++ tailWord_500997) baseStart_500997 baseEnd_500997 := by
    simpa [prefixWord, tailWord_500997, baseEnd_500997] using wordTrace_append hprefix tailTrace_500997
  have hstable : (prefixWord ++ tailWord_500997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500997).length < 2 ^ (prefixWord ++ tailWord_500997).sum := by decide
  have hdescent : baseEnd_500997 < baseStart_500997 := by decide
  rcases family_descends (prefixWord ++ tailWord_500997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501027 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_501027 : Nat := 118140960795 + 501027 * 2 ^ 59
def prefixEnd_501027 : Nat := 4983230072969 + 3 ^ 40 * 501027 * 2
def baseEnd_501027 : Nat := 171511781253544308838883

theorem tailTrace_501027 : CollatzResearch.WordTrace tailWord_501027 prefixEnd_501027 171511781253544308838883 := by
  unfold tailWord_501027
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273955955872222444245335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12182637303914814962830223 18273955955872222444245335)
  ·
    refine ⟨27410933933808333666368003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18273955955872222444245335 27410933933808333666368003)
    ·
      refine ⟨41116400900712500499552005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27410933933808333666368003 41116400900712500499552005)
      ·
        refine ⟨7709325168883593843666001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41116400900712500499552005 7709325168883593843666001)
        ·
          refine ⟨5781993876662695382749501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709325168883593843666001 5781993876662695382749501)
          ·
            refine ⟨2168247703748510768531063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781993876662695382749501 2168247703748510768531063)
            ·
              refine ⟨3252371555622766152796595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168247703748510768531063 3252371555622766152796595)
              ·
                refine ⟨4878557333434149229194893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252371555622766152796595 4878557333434149229194893)
                ·
                  refine ⟨1829459000037805960948085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4878557333434149229194893 1829459000037805960948085)
                  ·
                    refine ⟨171511781253544308838883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1829459000037805960948085 171511781253544308838883)
                    ·
                      rfl

theorem cell22_501027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_501027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501027 prefixEnd_501027 := by exact prefixLift 501027
  have htrace : WordTrace (prefixWord ++ tailWord_501027) baseStart_501027 baseEnd_501027 := by
    simpa [prefixWord, tailWord_501027, baseEnd_501027] using wordTrace_append hprefix tailTrace_501027
  have hstable : (prefixWord ++ tailWord_501027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501027).length < 2 ^ (prefixWord ++ tailWord_501027).sum := by decide
  have hdescent : baseEnd_501027 < baseStart_501027 := by decide
  rcases family_descends (prefixWord ++ tailWord_501027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501044 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_501044 : Nat := 118140960795 + 501044 * 2 ^ 59
def prefixEnd_501044 : Nat := 4983230072969 + 3 ^ 40 * 501044 * 2
def baseEnd_501044 : Nat := 171517600700961931163831

theorem tailTrace_501044 : CollatzResearch.WordTrace tailWord_501044 prefixEnd_501044 171517600700961931163831 := by
  unfold tailWord_501044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137287998405317173807093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12183050664540422898409457 9137287998405317173807093)
  ·
    refine ⟨856620749850498485044415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9137287998405317173807093 856620749850498485044415)
    ·
      refine ⟨1284931124775747727566623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 856620749850498485044415 1284931124775747727566623)
      ·
        refine ⟨1927396687163621591349935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284931124775747727566623 1927396687163621591349935)
        ·
          refine ⟨2891095030745432387024903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927396687163621591349935 2891095030745432387024903)
          ·
            refine ⟨4336642546118148580537355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891095030745432387024903 4336642546118148580537355)
            ·
              refine ⟨6504963819177222870806033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336642546118148580537355 6504963819177222870806033)
              ·
                refine ⟨4878722864382917153104525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504963819177222870806033 4878722864382917153104525)
                ·
                  refine ⟨1829521074143593932414197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4878722864382917153104525 1829521074143593932414197)
                  ·
                    refine ⟨171517600700961931163831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1829521074143593932414197 171517600700961931163831)
                    ·
                      rfl

theorem cell22_501044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_501044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501044 prefixEnd_501044 := by exact prefixLift 501044
  have htrace : WordTrace (prefixWord ++ tailWord_501044) baseStart_501044 baseEnd_501044 := by
    simpa [prefixWord, tailWord_501044, baseEnd_501044] using wordTrace_append hprefix tailTrace_501044
  have hstable : (prefixWord ++ tailWord_501044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501044).length < 2 ^ (prefixWord ++ tailWord_501044).sum := by decide
  have hdescent : baseEnd_501044 < baseStart_501044 := by decide
  rcases family_descends (prefixWord ++ tailWord_501044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501095 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 2, 3]
def baseStart_501095 : Nat := 118140960795 + 501095 * 2 ^ 59
def prefixEnd_501095 : Nat := 4983230072969 + 3 ^ 40 * 501095 * 2
def baseEnd_501095 : Nat := 171535059043214798138675

theorem tailTrace_501095 : CollatzResearch.WordTrace tailWord_501095 prefixEnd_501095 171535059043214798138675 := by
  unfold tailWord_501095
  simp only [CollatzResearch.WordTrace]
  refine ⟨18276436119625870057720739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12184290746417246705147159 18276436119625870057720739)
  ·
    refine ⟨27414654179438805086581109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18276436119625870057720739 27414654179438805086581109)
    ·
      refine ⟨2570123829322387976866979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27414654179438805086581109 2570123829322387976866979)
      ·
        refine ⟨3855185743983581965300469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570123829322387976866979 3855185743983581965300469)
        ·
          refine ⟨361423663498460809246919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3855185743983581965300469 361423663498460809246919)
          ·
            refine ⟨542135495247691213870379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361423663498460809246919 542135495247691213870379)
            ·
              refine ⟨813203242871536820805569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542135495247691213870379 813203242871536820805569)
              ·
                refine ⟨609902432153652615604177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813203242871536820805569 609902432153652615604177)
                ·
                  refine ⟨457426824115239461703133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609902432153652615604177 457426824115239461703133)
                  ·
                    refine ⟨171535059043214798138675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457426824115239461703133 171535059043214798138675)
                    ·
                      rfl

theorem cell22_501095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_501095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501095 prefixEnd_501095 := by exact prefixLift 501095
  have htrace : WordTrace (prefixWord ++ tailWord_501095) baseStart_501095 baseEnd_501095 := by
    simpa [prefixWord, tailWord_501095, baseEnd_501095] using wordTrace_append hprefix tailTrace_501095
  have hstable : (prefixWord ++ tailWord_501095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501095).length < 2 ^ (prefixWord ++ tailWord_501095).sum := by decide
  have hdescent : baseEnd_501095 < baseStart_501095 := by decide
  rcases family_descends (prefixWord ++ tailWord_501095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501106 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_501106 : Nat := 118140960795 + 501106 * 2 ^ 59
def prefixEnd_501106 : Nat := 4983230072969 + 3 ^ 40 * 501106 * 2
def baseEnd_501106 : Nat := 171538824568014436113641

theorem tailTrace_501106 : CollatzResearch.WordTrace tailWord_501106 prefixEnd_501106 171538824568014436113641 := by
  unfold tailWord_501106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569209330646504734092793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12184558215057345957580781 4569209330646504734092793)
  ·
    refine ⟨3426906997984878550569595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4569209330646504734092793 3426906997984878550569595)
    ·
      refine ⟨5140360496977317825854393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426906997984878550569595 5140360496977317825854393)
      ·
        refine ⟨3855270372732988369390795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5140360496977317825854393 3855270372732988369390795)
        ·
          refine ⟨5782905559099482554086193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855270372732988369390795 5782905559099482554086193)
          ·
            refine ⟨4337179169324611915564645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5782905559099482554086193 4337179169324611915564645)
            ·
              refine ⟨813221094248364734168371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4337179169324611915564645 813221094248364734168371)
              ·
                refine ⟨1219831641372547101252557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813221094248364734168371 1219831641372547101252557)
                ·
                  refine ⟨457436865514705162969709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1219831641372547101252557 457436865514705162969709)
                  ·
                    refine ⟨171538824568014436113641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457436865514705162969709 171538824568014436113641)
                    ·
                      rfl

theorem cell22_501106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_501106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501106 prefixEnd_501106 := by exact prefixLift 501106
  have htrace : WordTrace (prefixWord ++ tailWord_501106) baseStart_501106 baseEnd_501106 := by
    simpa [prefixWord, tailWord_501106, baseEnd_501106] using wordTrace_append hprefix tailTrace_501106
  have hstable : (prefixWord ++ tailWord_501106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501106).length < 2 ^ (prefixWord ++ tailWord_501106).sum := by decide
  have hdescent : baseEnd_501106 < baseStart_501106 := by decide
  rcases family_descends (prefixWord ++ tailWord_501106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501140 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_501140 : Nat := 118140960795 + 501140 * 2 ^ 59
def prefixEnd_501140 : Nat := 4983230072969 + 3 ^ 40 * 501140 * 2
def baseEnd_501140 : Nat := 171550463462849680763537

theorem tailTrace_501140 : CollatzResearch.WordTrace tailWord_501140 prefixEnd_501140 171550463462849680763537 := by
  unfold tailWord_501140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139038702231421371554437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12185384936308561828739249 9139038702231421371554437)
  ·
    refine ⟨1713569756668391507166457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9139038702231421371554437 1713569756668391507166457)
    ·
      refine ⟨1285177317501293630374843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1713569756668391507166457 1285177317501293630374843)
      ·
        refine ⟨1927765976251940445562265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285177317501293630374843 1927765976251940445562265)
        ·
          refine ⟨1445824482188955334171699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927765976251940445562265 1445824482188955334171699)
          ·
            refine ⟨2168736723283433001257549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445824482188955334171699 2168736723283433001257549)
            ·
              refine ⟨813276271231287375471581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2168736723283433001257549 813276271231287375471581)
              ·
                refine ⟨304978601711732765801843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813276271231287375471581 304978601711732765801843)
                ·
                  refine ⟨457467902567599148702765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304978601711732765801843 457467902567599148702765)
                  ·
                    refine ⟨171550463462849680763537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457467902567599148702765 171550463462849680763537)
                    ·
                      rfl

theorem cell22_501140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_501140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501140 prefixEnd_501140 := by exact prefixLift 501140
  have htrace : WordTrace (prefixWord ++ tailWord_501140) baseStart_501140 baseEnd_501140 := by
    simpa [prefixWord, tailWord_501140, baseEnd_501140] using wordTrace_append hprefix tailTrace_501140
  have hstable : (prefixWord ++ tailWord_501140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501140).length < 2 ^ (prefixWord ++ tailWord_501140).sum := by decide
  have hdescent : baseEnd_501140 < baseStart_501140 := by decide
  rcases family_descends (prefixWord ++ tailWord_501140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501164 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_501164 : Nat := 118140960795 + 501164 * 2 ^ 59
def prefixEnd_501164 : Nat := 4983230072969 + 3 ^ 40 * 501164 * 2
def baseEnd_501164 : Nat := 57186226384440539387821

theorem tailTrace_501164 : CollatzResearch.WordTrace tailWord_501164 prefixEnd_501164 57186226384440539387821 := by
  unfold tailWord_501164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9139476378187947420991273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12185968504250596561321697 9139476378187947420991273)
  ·
    refine ⟨6854607283640960565743455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9139476378187947420991273 6854607283640960565743455)
    ·
      refine ⟨10281910925461440848615183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854607283640960565743455 10281910925461440848615183)
      ·
        refine ⟨15422866388192161272922775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10281910925461440848615183 15422866388192161272922775)
        ·
          refine ⟨23134299582288241909384163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15422866388192161272922775 23134299582288241909384163)
          ·
            refine ⟨34701449373432362864076245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23134299582288241909384163 34701449373432362864076245)
            ·
              refine ⟨813315219689821004626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34701449373432362864076245 813315219689821004626787)
              ·
                refine ⟨1219972829534731506940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813315219689821004626787 1219972829534731506940181)
                ·
                  refine ⟨57186226384440539387821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1219972829534731506940181 57186226384440539387821)
                  ·
                    rfl

theorem cell22_501164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_501164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501164 prefixEnd_501164 := by exact prefixLift 501164
  have htrace : WordTrace (prefixWord ++ tailWord_501164) baseStart_501164 baseEnd_501164 := by
    simpa [prefixWord, tailWord_501164, baseEnd_501164] using wordTrace_append hprefix tailTrace_501164
  have hstable : (prefixWord ++ tailWord_501164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501164).length < 2 ^ (prefixWord ++ tailWord_501164).sum := by decide
  have hdescent : baseEnd_501164 < baseStart_501164 := by decide
  rcases family_descends (prefixWord ++ tailWord_501164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501196 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_501196 : Nat := 118140960795 + 501196 * 2 ^ 59
def prefixEnd_501196 : Nat := 4983230072969 + 3 ^ 40 * 501196 * 2
def baseEnd_501196 : Nat := 171569633407284201363365

theorem tailTrace_501196 : CollatzResearch.WordTrace tailWord_501196 prefixEnd_501196 171569633407284201363365 := by
  unfold tailWord_501196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140059946129982153573721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12186746594839976204764961 9140059946129982153573721)
  ·
    refine ⟨6855044959597486615180291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9140059946129982153573721 6855044959597486615180291)
    ·
      refine ⟨10282567439396229922770437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6855044959597486615180291 10282567439396229922770437)
      ·
        refine ⟨1927981394886793110519457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10282567439396229922770437 1927981394886793110519457)
        ·
          refine ⟨1445986046165094832889593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927981394886793110519457 1445986046165094832889593)
          ·
            refine ⟨1084489534623821124667195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445986046165094832889593 1084489534623821124667195)
            ·
              refine ⟨1626734301935731687000793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084489534623821124667195 1626734301935731687000793)
              ·
                refine ⟨1220050726451798765250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626734301935731687000793 1220050726451798765250595)
                ·
                  refine ⟨1830076089677698147875893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220050726451798765250595 1830076089677698147875893)
                  ·
                    refine ⟨171569633407284201363365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1830076089677698147875893 171569633407284201363365)
                    ·
                      rfl

theorem cell22_501196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_501196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501196 prefixEnd_501196 := by exact prefixLift 501196
  have htrace : WordTrace (prefixWord ++ tailWord_501196) baseStart_501196 baseEnd_501196 := by
    simpa [prefixWord, tailWord_501196, baseEnd_501196] using wordTrace_append hprefix tailTrace_501196
  have hstable : (prefixWord ++ tailWord_501196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501196).length < 2 ^ (prefixWord ++ tailWord_501196).sum := by decide
  have hdescent : baseEnd_501196 < baseStart_501196 := by decide
  rcases family_descends (prefixWord ++ tailWord_501196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501213 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_501213 : Nat := 118140960795 + 501213 * 2 ^ 59
def prefixEnd_501213 : Nat := 4983230072969 + 3 ^ 40 * 501213 * 2
def baseEnd_501213 : Nat := 171575452854701823688313

theorem tailTrace_501213 : CollatzResearch.WordTrace tailWord_501213 prefixEnd_501213 171575452854701823688313 := by
  unfold tailWord_501213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280739933198376210516293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12187159955465584140344195 18280739933198376210516293)
  ·
    refine ⟨3427638737474695539471805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18280739933198376210516293 3427638737474695539471805)
    ·
      refine ⟨1285364526553010827301927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3427638737474695539471805 1285364526553010827301927)
      ·
        refine ⟨1928046789829516240952891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285364526553010827301927 1928046789829516240952891)
        ·
          refine ⟨2892070184744274361429337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928046789829516240952891 2892070184744274361429337)
          ·
            refine ⟨2169052638558205771072003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892070184744274361429337 2169052638558205771072003)
            ·
              refine ⟨3253578957837308656608005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169052638558205771072003 3253578957837308656608005)
              ·
                refine ⟨610046054594495373114001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3253578957837308656608005 610046054594495373114001)
                ·
                  refine ⟨457534540945871529835501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610046054594495373114001 457534540945871529835501)
                  ·
                    refine ⟨171575452854701823688313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457534540945871529835501 171575452854701823688313)
                    ·
                      rfl

theorem cell22_501213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_501213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501213 prefixEnd_501213 := by exact prefixLift 501213
  have htrace : WordTrace (prefixWord ++ tailWord_501213) baseStart_501213 baseEnd_501213 := by
    simpa [prefixWord, tailWord_501213, baseEnd_501213] using wordTrace_append hprefix tailTrace_501213
  have hstable : (prefixWord ++ tailWord_501213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501213).length < 2 ^ (prefixWord ++ tailWord_501213).sum := by decide
  have hdescent : baseEnd_501213 < baseStart_501213 := by decide
  rcases family_descends (prefixWord ++ tailWord_501213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501309 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_501309 : Nat := 118140960795 + 501309 * 2 ^ 59
def prefixEnd_501309 : Nat := 4983230072969 + 3 ^ 40 * 501309 * 2
def baseEnd_501309 : Nat := 171608315616589573288019

theorem tailTrace_501309 : CollatzResearch.WordTrace tailWord_501309 prefixEnd_501309 171608315616589573288019 := by
  unfold tailWord_501309
  simp only [CollatzResearch.WordTrace]
  refine ⟨18284241340850584606010981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12189494227233723070673987 18284241340850584606010981)
  ·
    refine ⟨3428295251409484613627059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18284241340850584606010981 3428295251409484613627059)
    ·
      refine ⟨5142442877114226920440589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428295251409484613627059 5142442877114226920440589)
      ·
        refine ⟨1928416078917835095165221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5142442877114226920440589 1928416078917835095165221)
        ·
          refine ⟨361578014797094080343479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1928416078917835095165221 361578014797094080343479)
          ·
            refine ⟨542367022195641120515219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361578014797094080343479 542367022195641120515219)
            ·
              refine ⟨813550533293461680772829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542367022195641120515219 813550533293461680772829)
              ·
                refine ⟨305081449985048130289811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813550533293461680772829 305081449985048130289811)
                ·
                  refine ⟨457622174977572195434717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305081449985048130289811 457622174977572195434717)
                  ·
                    refine ⟨171608315616589573288019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457622174977572195434717 171608315616589573288019)
                    ·
                      rfl

theorem cell22_501309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_501309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501309 prefixEnd_501309 := by exact prefixLift 501309
  have htrace : WordTrace (prefixWord ++ tailWord_501309) baseStart_501309 baseEnd_501309 := by
    simpa [prefixWord, tailWord_501309, baseEnd_501309] using wordTrace_append hprefix tailTrace_501309
  have hstable : (prefixWord ++ tailWord_501309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501309).length < 2 ^ (prefixWord ++ tailWord_501309).sum := by decide
  have hdescent : baseEnd_501309 < baseStart_501309 := by decide
  rcases family_descends (prefixWord ++ tailWord_501309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501378 : List Nat := [3, 4, 3, 12]
def baseStart_501378 : Nat := 118140960795 + 501378 * 2 ^ 59
def prefixEnd_501378 : Nat := 4983230072969 + 3 ^ 40 * 501378 * 2
def baseEnd_501378 : Nat := 235434754083259798783

theorem tailTrace_501378 : CollatzResearch.WordTrace tailWord_501378 prefixEnd_501378 235434754083259798783 := by
  unfold tailWord_501378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571689494400152347568197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12191171985067072926848525 4571689494400152347568197)
  ·
    refine ⟨857191780200028565169037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4571689494400152347568197 857191780200028565169037)
    ·
      refine ⟨321446917575010711938389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 857191780200028565169037 321446917575010711938389)
      ·
        refine ⟨235434754083259798783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 321446917575010711938389 235434754083259798783)
        ·
          rfl

theorem cell22_501378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 12].length) (baseStart_501378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501378 prefixEnd_501378 := by exact prefixLift 501378
  have htrace : WordTrace (prefixWord ++ tailWord_501378) baseStart_501378 baseEnd_501378 := by
    simpa [prefixWord, tailWord_501378, baseEnd_501378] using wordTrace_append hprefix tailTrace_501378
  have hstable : (prefixWord ++ tailWord_501378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501378).length < 2 ^ (prefixWord ++ tailWord_501378).sum := by decide
  have hdescent : baseEnd_501378 < baseStart_501378 := by decide
  rcases family_descends (prefixWord ++ tailWord_501378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501384 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_501384 : Nat := 118140960795 + 501384 * 2 ^ 59
def prefixEnd_501384 : Nat := 4983230072969 + 3 ^ 40 * 501384 * 2
def baseEnd_501384 : Nat := 57211329883104792554263

theorem tailTrace_501384 : CollatzResearch.WordTrace tailWord_501384 prefixEnd_501384 57211329883104792554263 := by
  unfold tailWord_501384
  simp only [CollatzResearch.WordTrace]
  refine ⟨9143488407789436207495603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12191317877052581609994137 9143488407789436207495603)
  ·
    refine ⟨13715232611684154311243405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9143488407789436207495603 13715232611684154311243405)
    ·
      refine ⟨5143212229381557866716277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13715232611684154311243405 5143212229381557866716277)
      ·
        refine ⟨482176146504521050004651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5143212229381557866716277 482176146504521050004651)
        ·
          refine ⟨723264219756781575006977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482176146504521050004651 723264219756781575006977)
          ·
            refine ⟨542448164817586181255233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723264219756781575006977 542448164817586181255233)
            ·
              refine ⟨406836123613189635941425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542448164817586181255233 406836123613189635941425)
              ·
                refine ⟨305127092709892226956069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406836123613189635941425 305127092709892226956069)
                ·
                  refine ⟨57211329883104792554263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305127092709892226956069 57211329883104792554263)
                  ·
                    rfl

theorem cell22_501384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_501384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501384 prefixEnd_501384 := by exact prefixLift 501384
  have htrace : WordTrace (prefixWord ++ tailWord_501384) baseStart_501384 baseEnd_501384 := by
    simpa [prefixWord, tailWord_501384, baseEnd_501384] using wordTrace_append hprefix tailTrace_501384
  have hstable : (prefixWord ++ tailWord_501384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501384).length < 2 ^ (prefixWord ++ tailWord_501384).sum := by decide
  have hdescent : baseEnd_501384 < baseStart_501384 := by decide
  rcases family_descends (prefixWord ++ tailWord_501384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501438 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_501438 : Nat := 118140960795 + 501438 * 2 ^ 59
def prefixEnd_501438 : Nat := 4983230072969 + 3 ^ 40 * 501438 * 2
def baseEnd_501438 : Nat := 171652474952876236812623

theorem tailTrace_501438 : CollatzResearch.WordTrace tailWord_501438 prefixEnd_501438 171652474952876236812623 := by
  unfold tailWord_501438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286118294672904954682121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12192630904922159758304645 2286118294672904954682121)
  ·
    refine ⟨1714588721004678716011591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2286118294672904954682121 1714588721004678716011591)
    ·
      refine ⟨2571883081507018074017387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714588721004678716011591 2571883081507018074017387)
      ·
        refine ⟨3857824622260527111026081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571883081507018074017387 3857824622260527111026081)
        ·
          refine ⟨2893368466695395333269561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3857824622260527111026081 2893368466695395333269561)
          ·
            refine ⟨2170026350021546499952171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2893368466695395333269561 2170026350021546499952171)
            ·
              refine ⟨3255039525032319749928257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170026350021546499952171 3255039525032319749928257)
              ·
                refine ⟨2441279643774239812446193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255039525032319749928257 2441279643774239812446193)
                ·
                  refine ⟨1830959732830679859334645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441279643774239812446193 1830959732830679859334645)
                  ·
                    refine ⟨171652474952876236812623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1830959732830679859334645 171652474952876236812623)
                    ·
                      rfl

theorem cell22_501438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_501438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501438 prefixEnd_501438 := by exact prefixLift 501438
  have htrace : WordTrace (prefixWord ++ tailWord_501438) baseStart_501438 baseEnd_501438 := by
    simpa [prefixWord, tailWord_501438, baseEnd_501438] using wordTrace_append hprefix tailTrace_501438
  have hstable : (prefixWord ++ tailWord_501438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501438).length < 2 ^ (prefixWord ++ tailWord_501438).sum := by decide
  have hdescent : baseEnd_501438 < baseStart_501438 := by decide
  rcases family_descends (prefixWord ++ tailWord_501438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501483 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 4, 3]
def baseStart_501483 : Nat := 118140960795 + 501483 * 2 ^ 59
def prefixEnd_501483 : Nat := 4983230072969 + 3 ^ 40 * 501483 * 2
def baseEnd_501483 : Nat := 171667879372511119437485

theorem tailTrace_501483 : CollatzResearch.WordTrace tailWord_501483 prefixEnd_501483 171667879372511119437485 := by
  unfold tailWord_501483
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290587642220212322845103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12193725094813474881896735 18290587642220212322845103)
  ·
    refine ⟨27435881463330318484267655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290587642220212322845103 27435881463330318484267655)
    ·
      refine ⟨41153822194995477726401483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27435881463330318484267655 41153822194995477726401483)
      ·
        refine ⟨61730733292493216589602225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41153822194995477726401483 61730733292493216589602225)
        ·
          refine ⟨46298049969369912442201669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61730733292493216589602225 46298049969369912442201669)
          ·
            refine ⟨8680884369256858582912813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46298049969369912442201669 8680884369256858582912813)
            ·
              refine ⟨3255331638471321968592305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8680884369256858582912813 3255331638471321968592305)
              ·
                refine ⟨2441498728853491476444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3255331638471321968592305 2441498728853491476444229)
                ·
                  refine ⟨457781011660029651833293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2441498728853491476444229 457781011660029651833293)
                  ·
                    refine ⟨171667879372511119437485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457781011660029651833293 171667879372511119437485)
                    ·
                      rfl

theorem cell22_501483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 3].length) (baseStart_501483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501483 prefixEnd_501483 := by exact prefixLift 501483
  have htrace : WordTrace (prefixWord ++ tailWord_501483) baseStart_501483 baseEnd_501483 := by
    simpa [prefixWord, tailWord_501483, baseEnd_501483] using wordTrace_append hprefix tailTrace_501483
  have hstable : (prefixWord ++ tailWord_501483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501483).length < 2 ^ (prefixWord ++ tailWord_501483).sum := by decide
  have hdescent : baseEnd_501483 < baseStart_501483 := by decide
  rcases family_descends (prefixWord ++ tailWord_501483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501500 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_501500 : Nat := 118140960795 + 501500 * 2 ^ 59
def prefixEnd_501500 : Nat := 4983230072969 + 3 ^ 40 * 501500 * 2
def baseEnd_501500 : Nat := 171673698819928741762433

theorem tailTrace_501500 : CollatzResearch.WordTrace tailWord_501500 prefixEnd_501500 171673698819928741762433 := by
  unfold tailWord_501500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145603841579312113106977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12194138455439082817475969 9145603841579312113106977)
  ·
    refine ⟨6859202881184484084830233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9145603841579312113106977 6859202881184484084830233)
    ·
      refine ⟨5144402160888363063622675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6859202881184484084830233 5144402160888363063622675)
      ·
        refine ⟨7716603241332544595434013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144402160888363063622675 7716603241332544595434013)
        ·
          refine ⟨2893726215499704223287755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7716603241332544595434013 2893726215499704223287755)
          ·
            refine ⟨4340589323249556334931633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893726215499704223287755 4340589323249556334931633)
            ·
              refine ⟨3255441992437167251198725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4340589323249556334931633 3255441992437167251198725)
              ·
                refine ⟨610395373581968859599761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3255441992437167251198725 610395373581968859599761)
                ·
                  refine ⟨457796530186476644699821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610395373581968859599761 457796530186476644699821)
                  ·
                    refine ⟨171673698819928741762433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457796530186476644699821 171673698819928741762433)
                    ·
                      rfl

theorem cell22_501500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_501500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501500 prefixEnd_501500 := by exact prefixLift 501500
  have htrace : WordTrace (prefixWord ++ tailWord_501500) baseStart_501500 baseEnd_501500 := by
    simpa [prefixWord, tailWord_501500, baseEnd_501500] using wordTrace_append hprefix tailTrace_501500
  have hstable : (prefixWord ++ tailWord_501500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501500).length < 2 ^ (prefixWord ++ tailWord_501500).sum := by decide
  have hdescent : baseEnd_501500 < baseStart_501500 := by decide
  rcases family_descends (prefixWord ++ tailWord_501500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501502 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_501502 : Nat := 118140960795 + 501502 * 2 ^ 59
def prefixEnd_501502 : Nat := 4983230072969 + 3 ^ 40 * 501502 * 2
def baseEnd_501502 : Nat := 57224794486933801070809

theorem tailTrace_501502 : CollatzResearch.WordTrace tailWord_501502 prefixEnd_501502 57224794486933801070809 := by
  unfold tailWord_501502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286410078643922320973345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12194187086100919045191173 2286410078643922320973345)
  ·
    refine ⟨1714807558982941740730009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2286410078643922320973345 1714807558982941740730009)
    ·
      refine ⟨1286105669237206305547507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1714807558982941740730009 1286105669237206305547507)
      ·
        refine ⟨1929158503855809458321261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286105669237206305547507 1929158503855809458321261)
        ·
          refine ⟨723434438945928546870473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1929158503855809458321261 723434438945928546870473)
          ·
            refine ⟨542575829209446410152855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723434438945928546870473 542575829209446410152855)
            ·
              refine ⟨813863743814169615229283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542575829209446410152855 813863743814169615229283)
              ·
                refine ⟨1220795615721254422843925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813863743814169615229283 1220795615721254422843925)
                ·
                  refine ⟨57224794486933801070809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1220795615721254422843925 57224794486933801070809)
                  ·
                    rfl

theorem cell22_501502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_501502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501502 prefixEnd_501502 := by exact prefixLift 501502
  have htrace : WordTrace (prefixWord ++ tailWord_501502) baseStart_501502 baseEnd_501502 := by
    simpa [prefixWord, tailWord_501502, baseEnd_501502] using wordTrace_append hprefix tailTrace_501502
  have hstable : (prefixWord ++ tailWord_501502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501502).length < 2 ^ (prefixWord ++ tailWord_501502).sum := by decide
  have hdescent : baseEnd_501502 < baseStart_501502 := by decide
  rcases family_descends (prefixWord ++ tailWord_501502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501534 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_501534 : Nat := 118140960795 + 501534 * 2 ^ 59
def prefixEnd_501534 : Nat := 4983230072969 + 3 ^ 40 * 501534 * 2
def baseEnd_501534 : Nat := 171685337714763986412329

theorem tailTrace_501534 : CollatzResearch.WordTrace tailWord_501534 prefixEnd_501534 171685337714763986412329 := by
  unfold tailWord_501534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286555970629431004118957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12194965176690298688634437 2286555970629431004118957)
  ·
    refine ⟨857458488986036626544609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2286555970629431004118957 857458488986036626544609)
    ·
      refine ⟨643093866739527469908457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 857458488986036626544609 643093866739527469908457)
      ·
        refine ⟨482320400054645602431343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643093866739527469908457 482320400054645602431343)
        ·
          refine ⟨723480600081968403647015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482320400054645602431343 723480600081968403647015)
          ·
            refine ⟨1085220900122952605470523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723480600081968403647015 1085220900122952605470523)
            ·
              refine ⟨1627831350184428908205785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085220900122952605470523 1627831350184428908205785)
              ·
                refine ⟨1220873512638321681154339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1627831350184428908205785 1220873512638321681154339)
                ·
                  refine ⟨1831310268957482521731509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220873512638321681154339 1831310268957482521731509)
                  ·
                    refine ⟨171685337714763986412329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1831310268957482521731509 171685337714763986412329)
                    ·
                      rfl

theorem cell22_501534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_501534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501534 prefixEnd_501534 := by exact prefixLift 501534
  have htrace : WordTrace (prefixWord ++ tailWord_501534) baseStart_501534 baseEnd_501534 := by
    simpa [prefixWord, tailWord_501534, baseEnd_501534] using wordTrace_append hprefix tailTrace_501534
  have hstable : (prefixWord ++ tailWord_501534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501534).length < 2 ^ (prefixWord ++ tailWord_501534).sum := by decide
  have hdescent : baseEnd_501534 < baseStart_501534 := by decide
  rcases family_descends (prefixWord ++ tailWord_501534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501573 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_501573 : Nat := 118140960795 + 501573 * 2 ^ 59
def prefixEnd_501573 : Nat := 4983230072969 + 3 ^ 40 * 501573 * 2
def baseEnd_501573 : Nat := 171698688211780884687209

theorem tailTrace_501573 : CollatzResearch.WordTrace tailWord_501573 prefixEnd_501573 171698688211780884687209 := by
  unfold tailWord_501573
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293870211894157693621373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195913474596105129080915 18293870211894157693621373)
  ·
    refine ⟨6860201329460309135108015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18293870211894157693621373 6860201329460309135108015)
    ·
      refine ⟨10290301994190463702662023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860201329460309135108015 10290301994190463702662023)
      ·
        refine ⟨15435452991285695553993035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10290301994190463702662023 15435452991285695553993035)
        ·
          refine ⟨23153179486928543330989553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15435452991285695553993035 23153179486928543330989553)
          ·
            refine ⟨17364884615196407498242165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23153179486928543330989553 17364884615196407498242165)
            ·
              refine ⟨1627957932674663202960203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17364884615196407498242165 1627957932674663202960203)
              ·
                refine ⟨2441936899011994804440305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627957932674663202960203 2441936899011994804440305)
                ·
                  refine ⟨1831452674258996103330229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2441936899011994804440305 1831452674258996103330229)
                  ·
                    refine ⟨171698688211780884687209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1831452674258996103330229 171698688211780884687209)
                    ·
                      rfl

theorem cell22_501573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_501573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501573 prefixEnd_501573 := by exact prefixLift 501573
  have htrace : WordTrace (prefixWord ++ tailWord_501573) baseStart_501573 baseEnd_501573 := by
    simpa [prefixWord, tailWord_501573, baseEnd_501573] using wordTrace_append hprefix tailTrace_501573
  have hstable : (prefixWord ++ tailWord_501573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501573).length < 2 ^ (prefixWord ++ tailWord_501573).sum := by decide
  have hdescent : baseEnd_501573 < baseStart_501573 := by decide
  rcases family_descends (prefixWord ++ tailWord_501573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501596 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_501596 : Nat := 118140960795 + 501596 * 2 ^ 59
def prefixEnd_501596 : Nat := 4983230072969 + 3 ^ 40 * 501596 * 2
def baseEnd_501596 : Nat := 171706561581816491362139

theorem tailTrace_501596 : CollatzResearch.WordTrace tailWord_501596 prefixEnd_501596 171706561581816491362139 := by
  unfold tailWord_501596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9147354545405416310854321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12196472727207221747805761 9147354545405416310854321)
  ·
    refine ⟨6860515909054062233140741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9147354545405416310854321 6860515909054062233140741)
    ·
      refine ⟨1286346732947636668713889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6860515909054062233140741 1286346732947636668713889)
      ·
        refine ⟨964760049710727501535417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286346732947636668713889 964760049710727501535417)
        ·
          refine ⟨723570037283045626151563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964760049710727501535417 723570037283045626151563)
          ·
            refine ⟨1085355055924568439227345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723570037283045626151563 1085355055924568439227345)
            ·
              refine ⟨814016291943426329420509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085355055924568439227345 814016291943426329420509)
              ·
                refine ⟨305256109478784873532691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814016291943426329420509 305256109478784873532691)
                ·
                  refine ⟨457884164218177310299037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305256109478784873532691 457884164218177310299037)
                  ·
                    refine ⟨171706561581816491362139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457884164218177310299037 171706561581816491362139)
                    ·
                      rfl

theorem cell22_501596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_501596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501596 prefixEnd_501596 := by exact prefixLift 501596
  have htrace : WordTrace (prefixWord ++ tailWord_501596) baseStart_501596 baseEnd_501596 := by
    simpa [prefixWord, tailWord_501596, baseEnd_501596] using wordTrace_append hprefix tailTrace_501596
  have hstable : (prefixWord ++ tailWord_501596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501596).length < 2 ^ (prefixWord ++ tailWord_501596).sum := by decide
  have hdescent : baseEnd_501596 < baseStart_501596 := by decide
  rcases family_descends (prefixWord ++ tailWord_501596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501635 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_501635 : Nat := 118140960795 + 501635 * 2 ^ 59
def prefixEnd_501635 : Nat := 4983230072969 + 3 ^ 40 * 501635 * 2
def baseEnd_501635 : Nat := 171719912078833389637019

theorem tailTrace_501635 : CollatzResearch.WordTrace tailWord_501635 prefixEnd_501635 171719912078833389637019 := by
  unfold tailWord_501635
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296131537669542282378359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12197421025113028188252239 18296131537669542282378359)
  ·
    refine ⟨27444197306504313423567539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18296131537669542282378359 27444197306504313423567539)
    ·
      refine ⟨41166295959756470135351309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27444197306504313423567539 41166295959756470135351309)
      ·
        refine ⟨15437360984908676300756741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41166295959756470135351309 15437360984908676300756741)
        ·
          refine ⟨2894505184670376806391889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15437360984908676300756741 2894505184670376806391889)
          ·
            refine ⟨2170878888502782604793917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894505184670376806391889 2170878888502782604793917)
            ·
              refine ⟨814079583188543476797719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2170878888502782604793917 814079583188543476797719)
              ·
                refine ⟨1221119374782815215196579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814079583188543476797719 1221119374782815215196579)
                ·
                  refine ⟨1831679062174222822794869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221119374782815215196579 1831679062174222822794869)
                  ·
                    refine ⟨171719912078833389637019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1831679062174222822794869 171719912078833389637019)
                    ·
                      rfl

theorem cell22_501635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_501635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501635 prefixEnd_501635 := by exact prefixLift 501635
  have htrace : WordTrace (prefixWord ++ tailWord_501635) baseStart_501635 baseEnd_501635 := by
    simpa [prefixWord, tailWord_501635, baseEnd_501635] using wordTrace_append hprefix tailTrace_501635
  have hstable : (prefixWord ++ tailWord_501635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501635).length < 2 ^ (prefixWord ++ tailWord_501635).sum := by decide
  have hdescent : baseEnd_501635 < baseStart_501635 := by decide
  rcases family_descends (prefixWord ++ tailWord_501635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501652 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_501652 : Nat := 118140960795 + 501652 * 2 ^ 59
def prefixEnd_501652 : Nat := 4983230072969 + 3 ^ 40 * 501652 * 2
def baseEnd_501652 : Nat := 171725731526251011961967

theorem tailTrace_501652 : CollatzResearch.WordTrace tailWord_501652 prefixEnd_501652 171725731526251011961967 := by
  unfold tailWord_501652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148375789303977092873605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12197834385738636123831473 9148375789303977092873605)
  ·
    refine ⟨1715320460494495704913801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9148375789303977092873605 1715320460494495704913801)
    ·
      refine ⟨1286490345370871778685351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1715320460494495704913801 1286490345370871778685351)
      ·
        refine ⟨1929735518056307668028027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286490345370871778685351 1929735518056307668028027)
        ·
          refine ⟨2894603277084461502042041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929735518056307668028027 2894603277084461502042041)
          ·
            refine ⟨2170952457813346126531531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894603277084461502042041 2170952457813346126531531)
            ·
              refine ⟨3256428686720019189797297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170952457813346126531531 3256428686720019189797297)
              ·
                refine ⟨2442321515040014392347973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256428686720019189797297 2442321515040014392347973)
                ·
                  refine ⟨457935284070002698565245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442321515040014392347973 457935284070002698565245)
                  ·
                    refine ⟨171725731526251011961967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457935284070002698565245 171725731526251011961967)
                    ·
                      rfl

theorem cell22_501652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_501652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501652 prefixEnd_501652 := by exact prefixLift 501652
  have htrace : WordTrace (prefixWord ++ tailWord_501652) baseStart_501652 baseEnd_501652 := by
    simpa [prefixWord, tailWord_501652, baseEnd_501652] using wordTrace_append hprefix tailTrace_501652
  have hstable : (prefixWord ++ tailWord_501652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501652).length < 2 ^ (prefixWord ++ tailWord_501652).sum := by decide
  have hdescent : baseEnd_501652 < baseStart_501652 := by decide
  rcases family_descends (prefixWord ++ tailWord_501652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501727 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 5]
def baseStart_501727 : Nat := 118140960795 + 501727 * 2 ^ 59
def prefixEnd_501727 : Nat := 4983230072969 + 3 ^ 40 * 501727 * 2
def baseEnd_501727 : Nat := 57250468519658605445579

theorem tailTrace_501727 : CollatzResearch.WordTrace tailWord_501727 prefixEnd_501727 57250468519658605445579 := by
  unfold tailWord_501727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299487053336241994727435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12199658035557494663151623 18299487053336241994727435)
  ·
    refine ⟨27449230580004362992091153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18299487053336241994727435 27449230580004362992091153)
    ·
      refine ⟨20586922935003272244068365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27449230580004362992091153 20586922935003272244068365)
      ·
        refine ⟨7720096100626227091525637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20586922935003272244068365 7720096100626227091525637)
        ·
          refine ⟨1447518018867417579661057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7720096100626227091525637 1447518018867417579661057)
          ·
            refine ⟨1085638514150563184745793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1447518018867417579661057 1085638514150563184745793)
            ·
              refine ⟨814228885612922388559345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085638514150563184745793 814228885612922388559345)
              ·
                refine ⟨610671664209691791419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814228885612922388559345 610671664209691791419509)
                ·
                  refine ⟨57250468519658605445579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610671664209691791419509 57250468519658605445579)
                  ·
                    rfl

theorem cell22_501727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 5].length) (baseStart_501727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501727 prefixEnd_501727 := by exact prefixLift 501727
  have htrace : WordTrace (prefixWord ++ tailWord_501727) baseStart_501727 baseEnd_501727 := by
    simpa [prefixWord, tailWord_501727, baseEnd_501727] using wordTrace_append hprefix tailTrace_501727
  have hstable : (prefixWord ++ tailWord_501727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501727).length < 2 ^ (prefixWord ++ tailWord_501727).sum := by decide
  have hdescent : baseEnd_501727 < baseStart_501727 := by decide
  rcases family_descends (prefixWord ++ tailWord_501727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501731 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 1, 3]
def baseStart_501731 : Nat := 118140960795 + 501731 * 2 ^ 59
def prefixEnd_501731 : Nat := 4983230072969 + 3 ^ 40 * 501731 * 2
def baseEnd_501731 : Nat := 171752774840721139236725

theorem tailTrace_501731 : CollatzResearch.WordTrace tailWord_501731 prefixEnd_501731 171752774840721139236725 := by
  unfold tailWord_501731
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299632945321750677873047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12199755296881167118582031 18299632945321750677873047)
  ·
    refine ⟨27449449417982626016809571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18299632945321750677873047 27449449417982626016809571)
    ·
      refine ⟨41174174126973939025214357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27449449417982626016809571 41174174126973939025214357)
      ·
        refine ⟨1930039412201903391806923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41174174126973939025214357 1930039412201903391806923)
        ·
          refine ⟨2895059118302855087710385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1930039412201903391806923 2895059118302855087710385)
          ·
            refine ⟨2171294338727141315782789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2895059118302855087710385 2171294338727141315782789)
            ·
              refine ⟨407117688511338996709273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2171294338727141315782789 407117688511338996709273)
              ·
                refine ⟨305338266383504247531955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407117688511338996709273 305338266383504247531955)
                ·
                  refine ⟨458007399575256371297933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305338266383504247531955 458007399575256371297933)
                  ·
                    refine ⟨171752774840721139236725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458007399575256371297933 171752774840721139236725)
                    ·
                      rfl

theorem cell22_501731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 3].length) (baseStart_501731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501731 prefixEnd_501731 := by exact prefixLift 501731
  have htrace : WordTrace (prefixWord ++ tailWord_501731) baseStart_501731 baseEnd_501731 := by
    simpa [prefixWord, tailWord_501731, baseEnd_501731] using wordTrace_append hprefix tailTrace_501731
  have hstable : (prefixWord ++ tailWord_501731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501731).length < 2 ^ (prefixWord ++ tailWord_501731).sum := by decide
  have hdescent : baseEnd_501731 < baseStart_501731 := by decide
  rcases family_descends (prefixWord ++ tailWord_501731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501742 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_501742 : Nat := 118140960795 + 501742 * 2 ^ 59
def prefixEnd_501742 : Nat := 4983230072969 + 3 ^ 40 * 501742 * 2
def baseEnd_501742 : Nat := 171756540365520777211691

theorem tailTrace_501742 : CollatzResearch.WordTrace tailWord_501742 prefixEnd_501742 171756540365520777211691 := by
  unfold tailWord_501742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287504268535237444565435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12200022765521266371015653 2287504268535237444565435)
  ·
    refine ⟨3431256402802856166848153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287504268535237444565435 3431256402802856166848153)
    ·
      refine ⟨2573442302102142125136115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3431256402802856166848153 2573442302102142125136115)
      ·
        refine ⟨3860163453153213187704173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573442302102142125136115 3860163453153213187704173)
        ·
          refine ⟨1447561294932454945389065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3860163453153213187704173 1447561294932454945389065)
          ·
            refine ⟨1085670971199341209041799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1447561294932454945389065 1085670971199341209041799)
            ·
              refine ⟨1628506456799011813562699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085670971199341209041799 1628506456799011813562699)
              ·
                refine ⟨2442759685198517720344049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628506456799011813562699 2442759685198517720344049)
                ·
                  refine ⟨1832069763898888290258037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2442759685198517720344049 1832069763898888290258037)
                  ·
                    refine ⟨171756540365520777211691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1832069763898888290258037 171756540365520777211691)
                    ·
                      rfl

theorem cell22_501742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_501742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501742 prefixEnd_501742 := by exact prefixLift 501742
  have htrace : WordTrace (prefixWord ++ tailWord_501742) baseStart_501742 baseEnd_501742 := by
    simpa [prefixWord, tailWord_501742, baseEnd_501742] using wordTrace_append hprefix tailTrace_501742
  have hstable : (prefixWord ++ tailWord_501742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501742).length < 2 ^ (prefixWord ++ tailWord_501742).sum := by decide
  have hdescent : baseEnd_501742 < baseStart_501742 := by decide
  rcases family_descends (prefixWord ++ tailWord_501742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_501785 : Nat := 118140960795 + 501785 * 2 ^ 59
def prefixEnd_501785 : Nat := 4983230072969 + 3 ^ 40 * 501785 * 2
def baseEnd_501785 : Nat := 171771260144282998386559

theorem tailTrace_501785 : CollatzResearch.WordTrace tailWord_501785 prefixEnd_501785 171771260144282998386559 := by
  unfold tailWord_501785
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301602487126117900338809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201068324750745266892539 18301602487126117900338809)
  ·
    refine ⟨13726201865344588425254107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18301602487126117900338809 13726201865344588425254107)
    ·
      refine ⟨20589302798016882637881161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13726201865344588425254107 20589302798016882637881161)
      ·
        refine ⟨15441977098512661978410871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20589302798016882637881161 15441977098512661978410871)
        ·
          refine ⟨23162965647768992967616307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15441977098512661978410871 23162965647768992967616307)
          ·
            refine ⟨34744448471653489451424461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23162965647768992967616307 34744448471653489451424461)
            ·
              refine ⟨13029168176870058544284173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34744448471653489451424461 13029168176870058544284173)
              ·
                refine ⟨4885938066326271954106565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13029168176870058544284173 4885938066326271954106565)
                ·
                  refine ⟨916113387436175991394981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4885938066326271954106565 916113387436175991394981)
                  ·
                    refine ⟨171771260144282998386559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916113387436175991394981 171771260144282998386559)
                    ·
                      rfl

theorem cell22_501785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_501785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501785 prefixEnd_501785 := by exact prefixLift 501785
  have htrace : WordTrace (prefixWord ++ tailWord_501785) baseStart_501785 baseEnd_501785 := by
    simpa [prefixWord, tailWord_501785, baseEnd_501785] using wordTrace_append hprefix tailTrace_501785
  have hstable : (prefixWord ++ tailWord_501785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501785).length < 2 ^ (prefixWord ++ tailWord_501785).sum := by decide
  have hdescent : baseEnd_501785 < baseStart_501785 := by decide
  rcases family_descends (prefixWord ++ tailWord_501785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501787 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 2, 3]
def baseStart_501787 : Nat := 118140960795 + 501787 * 2 ^ 59
def prefixEnd_501787 : Nat := 4983230072969 + 3 ^ 40 * 501787 * 2
def baseEnd_501787 : Nat := 171771944785155659836553

theorem tailTrace_501787 : CollatzResearch.WordTrace tailWord_501787 prefixEnd_501787 171771944785155659836553 := by
  unfold tailWord_501787
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301675433118872241911615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201116955412581494607743 18301675433118872241911615)
  ·
    refine ⟨27452513149678308362867423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18301675433118872241911615 27452513149678308362867423)
    ·
      refine ⟨41178769724517462544301135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27452513149678308362867423 41178769724517462544301135)
      ·
        refine ⟨61768154586776193816451703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41178769724517462544301135 61768154586776193816451703)
        ·
          refine ⟨92652231880164290724677555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61768154586776193816451703 92652231880164290724677555)
          ·
            refine ⟨138978347820246436087016333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92652231880164290724677555 138978347820246436087016333)
            ·
              refine ⟨52116880432592413532631125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138978347820246436087016333 52116880432592413532631125)
              ·
                refine ⟨610744692569442346085521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52116880432592413532631125 610744692569442346085521)
                ·
                  refine ⟨458058519427081759564141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610744692569442346085521 458058519427081759564141)
                  ·
                    refine ⟨171771944785155659836553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458058519427081759564141 171771944785155659836553)
                    ·
                      rfl

theorem cell22_501787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 3].length) (baseStart_501787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501787 prefixEnd_501787 := by exact prefixLift 501787
  have htrace : WordTrace (prefixWord ++ tailWord_501787) baseStart_501787 baseEnd_501787 := by
    simpa [prefixWord, tailWord_501787, baseEnd_501787] using wordTrace_append hprefix tailTrace_501787
  have hstable : (prefixWord ++ tailWord_501787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501787).length < 2 ^ (prefixWord ++ tailWord_501787).sum := by decide
  have hdescent : baseEnd_501787 < baseStart_501787 := by decide
  rcases family_descends (prefixWord ++ tailWord_501787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501789 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 4]
def baseStart_501789 : Nat := 118140960795 + 501789 * 2 ^ 59
def prefixEnd_501789 : Nat := 4983230072969 + 3 ^ 40 * 501789 * 2
def baseEnd_501789 : Nat := 57257543142009440428849

theorem tailTrace_501789 : CollatzResearch.WordTrace tailWord_501789 prefixEnd_501789 57257543142009440428849 := by
  unfold tailWord_501789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18301748379111626583484421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201165586074417722322947 18301748379111626583484421)
  ·
    refine ⟨3431577821083429984403329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18301748379111626583484421 3431577821083429984403329)
    ·
      refine ⟨2573683365812572488302497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3431577821083429984403329 2573683365812572488302497)
      ·
        refine ⟨1930262524359429366226873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2573683365812572488302497 1930262524359429366226873)
        ·
          refine ⟨1447696893269572024670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930262524359429366226873 1447696893269572024670155)
          ·
            refine ⟨2171545339904358037005233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447696893269572024670155 2171545339904358037005233)
            ·
              refine ⟨1628659004928268527753925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171545339904358037005233 1628659004928268527753925)
              ·
                refine ⟨305373563424050348953861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1628659004928268527753925 305373563424050348953861)
                ·
                  refine ⟨57257543142009440428849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305373563424050348953861 57257543142009440428849)
                  ·
                    rfl

theorem cell22_501789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_501789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501789 prefixEnd_501789 := by exact prefixLift 501789
  have htrace : WordTrace (prefixWord ++ tailWord_501789) baseStart_501789 baseEnd_501789 := by
    simpa [prefixWord, tailWord_501789, baseEnd_501789] using wordTrace_append hprefix tailTrace_501789
  have hstable : (prefixWord ++ tailWord_501789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501789).length < 2 ^ (prefixWord ++ tailWord_501789).sum := by decide
  have hdescent : baseEnd_501789 < baseStart_501789 := by decide
  rcases family_descends (prefixWord ++ tailWord_501789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501802 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_501802 : Nat := 118140960795 + 501802 * 2 ^ 59
def prefixEnd_501802 : Nat := 4983230072969 + 3 ^ 40 * 501802 * 2
def baseEnd_501802 : Nat := 171777079591700620711507

theorem tailTrace_501802 : CollatzResearch.WordTrace tailWord_501802 prefixEnd_501802 171777079591700620711507 := by
  unfold tailWord_501802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575555632016132450926915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12201481685376353202471773 4575555632016132450926915)
  ·
    refine ⟨6863333448024198676390373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4575555632016132450926915 6863333448024198676390373)
    ·
      refine ⟨1286875021504537251823195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6863333448024198676390373 1286875021504537251823195)
      ·
        refine ⟨1930312532256805877734793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286875021504537251823195 1930312532256805877734793)
        ·
          refine ⟨1447734399192604408301095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930312532256805877734793 1447734399192604408301095)
          ·
            refine ⟨2171601598788906612451643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447734399192604408301095 2171601598788906612451643)
            ·
              refine ⟨3257402398183359918677465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171601598788906612451643 3257402398183359918677465)
              ·
                refine ⟨2443051798637519939008099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257402398183359918677465 2443051798637519939008099)
                ·
                  refine ⟨3664577697956279908512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443051798637519939008099 3664577697956279908512149)
                  ·
                    refine ⟨171777079591700620711507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3664577697956279908512149 171777079591700620711507)
                    ·
                      rfl

theorem cell22_501802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_501802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501802 prefixEnd_501802 := by exact prefixLift 501802
  have htrace : WordTrace (prefixWord ++ tailWord_501802) baseStart_501802 baseEnd_501802 := by
    simpa [prefixWord, tailWord_501802, baseEnd_501802] using wordTrace_append hprefix tailTrace_501802
  have hstable : (prefixWord ++ tailWord_501802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501802).length < 2 ^ (prefixWord ++ tailWord_501802).sum := by decide
  have hdescent : baseEnd_501802 < baseStart_501802 := by decide
  rcases family_descends (prefixWord ++ tailWord_501802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501817 : List Nat := [1, 2, 1, 5, 3, 1, 1, 8]
def baseStart_501817 : Nat := 118140960795 + 501817 * 2 ^ 59
def prefixEnd_501817 : Nat := 4983230072969 + 3 ^ 40 * 501817 * 2
def baseEnd_501817 : Nat := 19086912710916175731829

theorem tailTrace_501817 : CollatzResearch.WordTrace tailWord_501817 prefixEnd_501817 19086912710916175731829 := by
  unfold tailWord_501817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302769623010187365503705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201846415340124910335803 18302769623010187365503705)
  ·
    refine ⟨13727077217257640524127779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18302769623010187365503705 13727077217257640524127779)
    ·
      refine ⟨20590615825886460786191669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13727077217257640524127779 20590615825886460786191669)
      ·
        refine ⟨1930370233676855698705469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20590615825886460786191669 1930370233676855698705469)
        ·
          refine ⟨723888837628820887014551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1930370233676855698705469 723888837628820887014551)
          ·
            refine ⟨1085833256443231330521827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723888837628820887014551 1085833256443231330521827)
            ·
              refine ⟨1628749884664846995782741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085833256443231330521827 1628749884664846995782741)
              ·
                refine ⟨19086912710916175731829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1628749884664846995782741 19086912710916175731829)
                ·
                  rfl

theorem cell22_501817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 8].length) (baseStart_501817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501817 prefixEnd_501817 := by exact prefixLift 501817
  have htrace : WordTrace (prefixWord ++ tailWord_501817) baseStart_501817 baseEnd_501817 := by
    simpa [prefixWord, tailWord_501817, baseEnd_501817] using wordTrace_append hprefix tailTrace_501817
  have hstable : (prefixWord ++ tailWord_501817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501817).length < 2 ^ (prefixWord ++ tailWord_501817).sum := by decide
  have hdescent : baseEnd_501817 < baseStart_501817 := by decide
  rcases family_descends (prefixWord ++ tailWord_501817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501924 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_501924 : Nat := 118140960795 + 501924 * 2 ^ 59
def prefixEnd_501924 : Nat := 4983230072969 + 3 ^ 40 * 501924 * 2
def baseEnd_501924 : Nat := 57272947561644323053711

theorem tailTrace_501924 : CollatzResearch.WordTrace tailWord_501924 prefixEnd_501924 57272947561644323053711 := by
  unfold tailWord_501924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153336116811272319824413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12204448155748363093099217 9153336116811272319824413)
  ·
    refine ⟨3432501043804227119934155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9153336116811272319824413 3432501043804227119934155)
    ·
      refine ⟨5148751565706340679901233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432501043804227119934155 5148751565706340679901233)
      ·
        refine ⟨3861563674279755509925925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5148751565706340679901233 3861563674279755509925925)
        ·
          refine ⟨724043188927454158111111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3861563674279755509925925 724043188927454158111111)
          ·
            refine ⟨1086064783391181237166667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724043188927454158111111 1086064783391181237166667)
            ·
              refine ⟨1629097175086771855750001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086064783391181237166667 1629097175086771855750001)
              ·
                refine ⟨1221822881315078891812501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629097175086771855750001 1221822881315078891812501)
                ·
                  refine ⟨57272947561644323053711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1221822881315078891812501 57272947561644323053711)
                  ·
                    rfl

theorem cell22_501924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_501924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501924 prefixEnd_501924 := by exact prefixLift 501924
  have htrace : WordTrace (prefixWord ++ tailWord_501924) baseStart_501924 baseEnd_501924 := by
    simpa [prefixWord, tailWord_501924, baseEnd_501924] using wordTrace_append hprefix tailTrace_501924
  have hstable : (prefixWord ++ tailWord_501924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501924).length < 2 ^ (prefixWord ++ tailWord_501924).sum := by decide
  have hdescent : baseEnd_501924 < baseStart_501924 := by decide
  rcases family_descends (prefixWord ++ tailWord_501924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501952 : List Nat := [2, 1, 1, 2, 5, 2, 9]
def baseStart_501952 : Nat := 118140960795 + 501952 * 2 ^ 59
def prefixEnd_501952 : Nat := 4983230072969 + 3 ^ 40 * 501952 * 2
def baseEnd_501952 : Nat := 6364015839153712202261

theorem tailTrace_501952 : CollatzResearch.WordTrace tailWord_501952 prefixEnd_501952 6364015839153712202261 := by
  unfold tailWord_501952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153846738760552710834055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12205128985014070281112073 9153846738760552710834055)
  ·
    refine ⟨13730770108140829066251083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9153846738760552710834055 13730770108140829066251083)
    ·
      refine ⟨20596155162211243599376625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13730770108140829066251083 20596155162211243599376625)
      ·
        refine ⟨15447116371658432699532469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20596155162211243599376625 15447116371658432699532469)
        ·
          refine ⟨1448167159842978065581169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15447116371658432699532469 1448167159842978065581169)
          ·
            refine ⟨1086125369882233549185877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448167159842978065581169 1086125369882233549185877)
            ·
              refine ⟨6364015839153712202261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1086125369882233549185877 6364015839153712202261)
              ·
                rfl

theorem cell22_501952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 9].length) (baseStart_501952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501952 prefixEnd_501952 := by exact prefixLift 501952
  have htrace : WordTrace (prefixWord ++ tailWord_501952) baseStart_501952 baseEnd_501952 := by
    simpa [prefixWord, tailWord_501952, baseEnd_501952] using wordTrace_append hprefix tailTrace_501952
  have hstable : (prefixWord ++ tailWord_501952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501952).length < 2 ^ (prefixWord ++ tailWord_501952).sum := by decide
  have hdescent : baseEnd_501952 < baseStart_501952 := by decide
  rcases family_descends (prefixWord ++ tailWord_501952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501956 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_501956 : Nat := 118140960795 + 501956 * 2 ^ 59
def prefixEnd_501956 : Nat := 4983230072969 + 3 ^ 40 * 501956 * 2
def baseEnd_501956 : Nat := 171829796938895552361035

theorem tailTrace_501956 : CollatzResearch.WordTrace tailWord_501956 prefixEnd_501956 171829796938895552361035 := by
  unfold tailWord_501956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153919684753307052406861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12205226246337742736542481 9153919684753307052406861)
  ·
    refine ⟨3432719881782490144652573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9153919684753307052406861 3432719881782490144652573)
    ·
      refine ⟨1287269955668433804244715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3432719881782490144652573 1287269955668433804244715)
      ·
        refine ⟨1930904933502650706367073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287269955668433804244715 1930904933502650706367073)
        ·
          refine ⟨1448178700126988029775305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1930904933502650706367073 1448178700126988029775305)
          ·
            refine ⟨1086134025095241022331479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448178700126988029775305 1086134025095241022331479)
            ·
              refine ⟨1629201037642861533497219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086134025095241022331479 1629201037642861533497219)
              ·
                refine ⟨2443801556464292300245829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629201037642861533497219 2443801556464292300245829)
                ·
                  refine ⟨458212791837054806296093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2443801556464292300245829 458212791837054806296093)
                  ·
                    refine ⟨171829796938895552361035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458212791837054806296093 171829796938895552361035)
                    ·
                      rfl

theorem cell22_501956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_501956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501956 prefixEnd_501956 := by exact prefixLift 501956
  have htrace : WordTrace (prefixWord ++ tailWord_501956) baseStart_501956 baseEnd_501956 := by
    simpa [prefixWord, tailWord_501956, baseEnd_501956] using wordTrace_append hprefix tailTrace_501956
  have hstable : (prefixWord ++ tailWord_501956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501956).length < 2 ^ (prefixWord ++ tailWord_501956).sum := by decide
  have hdescent : baseEnd_501956 < baseStart_501956 := by decide
  rcases family_descends (prefixWord ++ tailWord_501956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501973 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_501973 : Nat := 118140960795 + 501973 * 2 ^ 59
def prefixEnd_501973 : Nat := 4983230072969 + 3 ^ 40 * 501973 * 2
def baseEnd_501973 : Nat := 171835616386313174685983

theorem tailTrace_501973 : CollatzResearch.WordTrace tailWord_501973 prefixEnd_501973 171835616386313174685983 := by
  unfold tailWord_501973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308459410445026008182573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205639606963350672121715 18308459410445026008182573)
  ·
    refine ⟨6865672278916884753068465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18308459410445026008182573 6865672278916884753068465)
    ·
      refine ⟨5149254209187663564801349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6865672278916884753068465 5149254209187663564801349)
      ·
        refine ⟨965485164222686918400253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5149254209187663564801349 965485164222686918400253)
        ·
          refine ⟨362056936583507594400095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965485164222686918400253 362056936583507594400095)
          ·
            refine ⟨543085404875261391600143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362056936583507594400095 543085404875261391600143)
            ·
              refine ⟨814628107312892087400215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543085404875261391600143 814628107312892087400215)
              ·
                refine ⟨1221942160969338131100323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814628107312892087400215 1221942160969338131100323)
                ·
                  refine ⟨1832913241454007196650485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221942160969338131100323 1832913241454007196650485)
                  ·
                    refine ⟨171835616386313174685983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1832913241454007196650485 171835616386313174685983)
                    ·
                      rfl

theorem cell22_501973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_501973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501973 prefixEnd_501973 := by exact prefixLift 501973
  have htrace : WordTrace (prefixWord ++ tailWord_501973) baseStart_501973 baseEnd_501973 := by
    simpa [prefixWord, tailWord_501973, baseEnd_501973] using wordTrace_append hprefix tailTrace_501973
  have hstable : (prefixWord ++ tailWord_501973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501973).length < 2 ^ (prefixWord ++ tailWord_501973).sum := by decide
  have hdescent : baseEnd_501973 < baseStart_501973 := by decide
  rcases family_descends (prefixWord ++ tailWord_501973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501984 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_501984 : Nat := 118140960795 + 501984 * 2 ^ 59
def prefixEnd_501984 : Nat := 4983230072969 + 3 ^ 40 * 501984 * 2
def baseEnd_501984 : Nat := 171839381911112812660949

theorem tailTrace_501984 : CollatzResearch.WordTrace tailWord_501984 prefixEnd_501984 171839381911112812660949 := by
  unfold tailWord_501984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154430306702587443416503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12205907075603449924555337 9154430306702587443416503)
  ·
    refine ⟨13731645460053881165124755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9154430306702587443416503 13731645460053881165124755)
    ·
      refine ⟨20597468190080821747687133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731645460053881165124755 20597468190080821747687133)
      ·
        refine ⟨7724050571280308155382675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20597468190080821747687133 7724050571280308155382675)
        ·
          refine ⟨11586075856920462233074013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7724050571280308155382675 11586075856920462233074013)
          ·
            refine ⟨4344778446345173337402755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11586075856920462233074013 4344778446345173337402755)
            ·
              refine ⟨6517167669517760006104133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344778446345173337402755 6517167669517760006104133)
              ·
                refine ⟨1221968938034580001144525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6517167669517760006104133 1221968938034580001144525)
                ·
                  refine ⟨458238351762967500429197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221968938034580001144525 458238351762967500429197)
                  ·
                    refine ⟨171839381911112812660949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458238351762967500429197 171839381911112812660949)
                    ·
                      rfl

theorem cell22_501984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_501984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_501984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_501984 prefixEnd_501984 := by exact prefixLift 501984
  have htrace : WordTrace (prefixWord ++ tailWord_501984) baseStart_501984 baseEnd_501984 := by
    simpa [prefixWord, tailWord_501984, baseEnd_501984] using wordTrace_append hprefix tailTrace_501984
  have hstable : (prefixWord ++ tailWord_501984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501984).length < 2 ^ (prefixWord ++ tailWord_501984).sum := by decide
  have hdescent : baseEnd_501984 < baseStart_501984 := by decide
  rcases family_descends (prefixWord ++ tailWord_501984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502014 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_502014 : Nat := 118140960795 + 502014 * 2 ^ 59
def prefixEnd_502014 : Nat := 4983230072969 + 3 ^ 40 * 502014 * 2
def baseEnd_502014 : Nat := 57283217174734244803619

theorem tailTrace_502014 : CollatzResearch.WordTrace tailWord_502014 prefixEnd_502014 57283217174734244803619 := by
  unfold tailWord_502014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288744350412061251303137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12206636535530993340283397 2288744350412061251303137)
  ·
    refine ⟨1716558262809045938477353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2288744350412061251303137 1716558262809045938477353)
    ·
      refine ⟨1287418697106784453858015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1716558262809045938477353 1287418697106784453858015)
      ·
        refine ⟨1931128045660176680787023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287418697106784453858015 1931128045660176680787023)
        ·
          refine ⟨2896692068490265021180535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931128045660176680787023 2896692068490265021180535)
          ·
            refine ⟨4345038102735397531770803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896692068490265021180535 4345038102735397531770803)
            ·
              refine ⟨6517557154103096297656205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345038102735397531770803 6517557154103096297656205)
              ·
                refine ⟨2444083932788661111621077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6517557154103096297656205 2444083932788661111621077)
                ·
                  refine ⟨57283217174734244803619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2444083932788661111621077 57283217174734244803619)
                  ·
                    rfl

theorem cell22_502014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_502014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502014 prefixEnd_502014 := by exact prefixLift 502014
  have htrace : WordTrace (prefixWord ++ tailWord_502014) baseStart_502014 baseEnd_502014 := by
    simpa [prefixWord, tailWord_502014, baseEnd_502014] using wordTrace_append hprefix tailTrace_502014
  have hstable : (prefixWord ++ tailWord_502014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502014).length < 2 ^ (prefixWord ++ tailWord_502014).sum := by decide
  have hdescent : baseEnd_502014 < baseStart_502014 := by decide
  rcases family_descends (prefixWord ++ tailWord_502014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502018 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_502018 : Nat := 118140960795 + 502018 * 2 ^ 59
def prefixEnd_502018 : Nat := 4983230072969 + 3 ^ 40 * 502018 * 2
def baseEnd_502018 : Nat := 171851020805948057310845

theorem tailTrace_502018 : CollatzResearch.WordTrace tailWord_502018 prefixEnd_502018 171851020805948057310845 := by
  unfold tailWord_502018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577525173820499673392677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12206733796854665795713805 4577525173820499673392677)
  ·
    refine ⟨858285970091343688761127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4577525173820499673392677 858285970091343688761127)
    ·
      refine ⟨1287428955137015533141691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858285970091343688761127 1287428955137015533141691)
      ·
        refine ⟨1931143432705523299712537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287428955137015533141691 1931143432705523299712537)
        ·
          refine ⟨1448357574529142474784403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931143432705523299712537 1448357574529142474784403)
          ·
            refine ⟨2172536361793713712176605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448357574529142474784403 2172536361793713712176605)
            ·
              refine ⟨814701135672642642066227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2172536361793713712176605 814701135672642642066227)
              ·
                refine ⟨1222051703508963963099341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814701135672642642066227 1222051703508963963099341)
                ·
                  refine ⟨458269388815861486162253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222051703508963963099341 458269388815861486162253)
                  ·
                    refine ⟨171851020805948057310845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458269388815861486162253 171851020805948057310845)
                    ·
                      rfl

theorem cell22_502018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_502018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502018 prefixEnd_502018 := by exact prefixLift 502018
  have htrace : WordTrace (prefixWord ++ tailWord_502018) baseStart_502018 baseEnd_502018 := by
    simpa [prefixWord, tailWord_502018, baseEnd_502018] using wordTrace_append hprefix tailTrace_502018
  have hstable : (prefixWord ++ tailWord_502018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502018).length < 2 ^ (prefixWord ++ tailWord_502018).sum := by decide
  have hdescent : baseEnd_502018 < baseStart_502018 := by decide
  rcases family_descends (prefixWord ++ tailWord_502018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502076 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_502076 : Nat := 118140960795 + 502076 * 2 ^ 59
def prefixEnd_502076 : Nat := 4983230072969 + 3 ^ 40 * 502076 * 2
def baseEnd_502076 : Nat := 57290291797085079786889

theorem tailTrace_502076 : CollatzResearch.WordTrace tailWord_502076 prefixEnd_502076 57290291797085079786889 := by
  unfold tailWord_502076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156108064535937299591041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12208144086047916399454721 9156108064535937299591041)
  ·
    refine ⟨6867081048401952974693281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9156108064535937299591041 6867081048401952974693281)
    ·
      refine ⟨5150310786301464731019961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6867081048401952974693281 5150310786301464731019961)
      ·
        refine ⟨3862733089726098548264971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5150310786301464731019961 3862733089726098548264971)
        ·
          refine ⟨5794099634589147822397457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862733089726098548264971 5794099634589147822397457)
          ·
            refine ⟨4345574725941860866798093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5794099634589147822397457 4345574725941860866798093)
            ·
              refine ⟨1629590522228197825049285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4345574725941860866798093 1629590522228197825049285)
              ·
                refine ⟨305548222917787092196741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1629590522228197825049285 305548222917787092196741)
                ·
                  refine ⟨57290291797085079786889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305548222917787092196741 57290291797085079786889)
                  ·
                    rfl

theorem cell22_502076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_502076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502076 prefixEnd_502076 := by exact prefixLift 502076
  have htrace : WordTrace (prefixWord ++ tailWord_502076) baseStart_502076 baseEnd_502076 := by
    simpa [prefixWord, tailWord_502076, baseEnd_502076] using wordTrace_append hprefix tailTrace_502076
  have hstable : (prefixWord ++ tailWord_502076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502076).length < 2 ^ (prefixWord ++ tailWord_502076).sum := by decide
  have hdescent : baseEnd_502076 < baseStart_502076 := by decide
  rcases family_descends (prefixWord ++ tailWord_502076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502170 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_502170 : Nat := 118140960795 + 502170 * 2 ^ 59
def prefixEnd_502170 : Nat := 4983230072969 + 3 ^ 40 * 502170 * 2
def baseEnd_502170 : Nat := 171903053512270327510379

theorem tailTrace_502170 : CollatzResearch.WordTrace tailWord_502170 prefixEnd_502170 171903053512270327510379 := by
  unfold tailWord_502170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578911147682832163275991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12210429727154219102069309 4578911147682832163275991)
  ·
    refine ⟨6868366721524248244913987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578911147682832163275991 6868366721524248244913987)
    ·
      refine ⟨10302550082286372367370981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6868366721524248244913987 10302550082286372367370981)
      ·
        refine ⟨1931728140428694818882059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10302550082286372367370981 1931728140428694818882059)
        ·
          refine ⟨2897592210643042228323089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931728140428694818882059 2897592210643042228323089)
          ·
            refine ⟨2173194157982281671242317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897592210643042228323089 2173194157982281671242317)
            ·
              refine ⟨814947809243355626715869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2173194157982281671242317 814947809243355626715869)
              ·
                refine ⟨305605428466258360018451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814947809243355626715869 305605428466258360018451)
                ·
                  refine ⟨458408142699387540027677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305605428466258360018451 458408142699387540027677)
                  ·
                    refine ⟨171903053512270327510379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458408142699387540027677 171903053512270327510379)
                    ·
                      rfl

theorem cell22_502170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_502170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502170 prefixEnd_502170 := by exact prefixLift 502170
  have htrace : WordTrace (prefixWord ++ tailWord_502170) baseStart_502170 baseEnd_502170 := by
    simpa [prefixWord, tailWord_502170, baseEnd_502170] using wordTrace_append hprefix tailTrace_502170
  have hstable : (prefixWord ++ tailWord_502170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502170).length < 2 ^ (prefixWord ++ tailWord_502170).sum := by decide
  have hdescent : baseEnd_502170 < baseStart_502170 := by decide
  rcases family_descends (prefixWord ++ tailWord_502170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502239 : List Nat := [1, 1, 2, 3, 3, 12]
def baseStart_502239 : Nat := 118140960795 + 502239 * 2 ^ 59
def prefixEnd_502239 : Nat := 4983230072969 + 3 ^ 40 * 502239 * 2
def baseEnd_502239 : Nat := 2122551526202187006607

theorem tailTrace_502239 : CollatzResearch.WordTrace tailWord_502239 prefixEnd_502239 2122551526202187006607 := by
  unfold tailWord_502239
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318161227481353437365771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212107484987568958243847 18318161227481353437365771)
  ·
    refine ⟨27477241841222030156048657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18318161227481353437365771 27477241841222030156048657)
    ·
      refine ⟨20607931380916522617036493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27477241841222030156048657 20607931380916522617036493)
      ·
        refine ⟨7727974267843695981388685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20607931380916522617036493 7727974267843695981388685)
        ·
          refine ⟨2897990350441385993020757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7727974267843695981388685 2897990350441385993020757)
          ·
            refine ⟨2122551526202187006607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2897990350441385993020757 2122551526202187006607)
            ·
              rfl

theorem cell22_502239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 12].length) (baseStart_502239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502239 prefixEnd_502239 := by exact prefixLift 502239
  have htrace : WordTrace (prefixWord ++ tailWord_502239) baseStart_502239 baseEnd_502239 := by
    simpa [prefixWord, tailWord_502239, baseEnd_502239] using wordTrace_append hprefix tailTrace_502239
  have hstable : (prefixWord ++ tailWord_502239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502239).length < 2 ^ (prefixWord ++ tailWord_502239).sum := by decide
  have hdescent : baseEnd_502239 < baseStart_502239 := by decide
  rcases family_descends (prefixWord ++ tailWord_502239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502241 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_502241 : Nat := 118140960795 + 502241 * 2 ^ 59
def prefixEnd_502241 : Nat := 4983230072969 + 3 ^ 40 * 502241 * 2
def baseEnd_502241 : Nat := 171927358263249808985161

theorem tailTrace_502241 : CollatzResearch.WordTrace tailWord_502241 prefixEnd_502241 171927358263249808985161 := by
  unfold tailWord_502241
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318234173474107778938577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212156115649405185959051 18318234173474107778938577)
  ·
    refine ⟨13738675630105580834203933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18318234173474107778938577 13738675630105580834203933)
    ·
      refine ⟨5152003361289592812826475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13738675630105580834203933 5152003361289592812826475)
      ·
        refine ⟨7728005041934389219239713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152003361289592812826475 7728005041934389219239713)
        ·
          refine ⟨5796003781450791914429785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7728005041934389219239713 5796003781450791914429785)
          ·
            refine ⟨4347002836088093935822339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5796003781450791914429785 4347002836088093935822339)
            ·
              refine ⟨6520504254132140903733509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347002836088093935822339 6520504254132140903733509)
              ·
                refine ⟨1222594547649776419450033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6520504254132140903733509 1222594547649776419450033)
                ·
                  refine ⟨916945910737332314587525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222594547649776419450033 916945910737332314587525)
                  ·
                    refine ⟨171927358263249808985161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916945910737332314587525 171927358263249808985161)
                    ·
                      rfl

theorem cell22_502241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_502241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502241 prefixEnd_502241 := by exact prefixLift 502241
  have htrace : WordTrace (prefixWord ++ tailWord_502241) baseStart_502241 baseEnd_502241 := by
    simpa [prefixWord, tailWord_502241, baseEnd_502241] using wordTrace_append hprefix tailTrace_502241
  have hstable : (prefixWord ++ tailWord_502241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502241).length < 2 ^ (prefixWord ++ tailWord_502241).sum := by decide
  have hdescent : baseEnd_502241 < baseStart_502241 := by decide
  rcases family_descends (prefixWord ++ tailWord_502241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502245 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 4]
def baseStart_502245 : Nat := 118140960795 + 502245 * 2 ^ 59
def prefixEnd_502245 : Nat := 4983230072969 + 3 ^ 40 * 502245 * 2
def baseEnd_502245 : Nat := 57309575848331710628383

theorem tailTrace_502245 : CollatzResearch.WordTrace tailWord_502245 prefixEnd_502245 57309575848331710628383 := by
  unfold tailWord_502245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318380065459616462084189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212253376973077641389459 18318380065459616462084189)
  ·
    refine ⟨6869392524547356173281571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18318380065459616462084189 6869392524547356173281571)
    ·
      refine ⟨10304088786821034259922357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869392524547356173281571 10304088786821034259922357)
      ·
        refine ⟨966008323764471961867721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10304088786821034259922357 966008323764471961867721)
        ·
          refine ⟨724506242823353971400791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966008323764471961867721 724506242823353971400791)
          ·
            refine ⟨1086759364235030957101187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724506242823353971400791 1086759364235030957101187)
            ·
              refine ⟨1630139046352546435651781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086759364235030957101187 1630139046352546435651781)
              ·
                refine ⟨305651071191102456684709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1630139046352546435651781 305651071191102456684709)
                ·
                  refine ⟨57309575848331710628383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305651071191102456684709 57309575848331710628383)
                  ·
                    rfl

theorem cell22_502245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_502245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502245 prefixEnd_502245 := by exact prefixLift 502245
  have htrace : WordTrace (prefixWord ++ tailWord_502245) baseStart_502245 baseEnd_502245 := by
    simpa [prefixWord, tailWord_502245, baseEnd_502245] using wordTrace_append hprefix tailTrace_502245
  have hstable : (prefixWord ++ tailWord_502245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502245).length < 2 ^ (prefixWord ++ tailWord_502245).sum := by decide
  have hdescent : baseEnd_502245 < baseStart_502245 := by decide
  rcases family_descends (prefixWord ++ tailWord_502245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502273 : List Nat := [1, 2, 4, 1, 3, 2, 3, 6]
def baseStart_502273 : Nat := 118140960795 + 502273 * 2 ^ 59
def prefixEnd_502273 : Nat := 4983230072969 + 3 ^ 40 * 502273 * 2
def baseEnd_502273 : Nat := 19104256946356932465007

theorem tailTrace_502273 : CollatzResearch.WordTrace tailWord_502273 prefixEnd_502273 19104256946356932465007 := by
  unfold tailWord_502273
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319401309358177244103473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212934206238784829402315 18319401309358177244103473)
  ·
    refine ⟨13739550982018632933077605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18319401309358177244103473 13739550982018632933077605)
    ·
      refine ⟨2576165809128493674952051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13739550982018632933077605 2576165809128493674952051)
      ·
        refine ⟨3864248713692740512428077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576165809128493674952051 3864248713692740512428077)
        ·
          refine ⟨1449093267634777692160529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3864248713692740512428077 1449093267634777692160529)
          ·
            refine ⟨1086819950726083269120397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449093267634777692160529 1086819950726083269120397)
            ·
              refine ⟨407557481522281225920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1086819950726083269120397 407557481522281225920149)
              ·
                refine ⟨19104256946356932465007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407557481522281225920149 19104256946356932465007)
                ·
                  rfl

theorem cell22_502273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 6].length) (baseStart_502273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502273 prefixEnd_502273 := by exact prefixLift 502273
  have htrace : WordTrace (prefixWord ++ tailWord_502273) baseStart_502273 baseEnd_502273 := by
    simpa [prefixWord, tailWord_502273, baseEnd_502273] using wordTrace_append hprefix tailTrace_502273
  have hstable : (prefixWord ++ tailWord_502273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502273).length < 2 ^ (prefixWord ++ tailWord_502273).sum := by decide
  have hdescent : baseEnd_502273 < baseStart_502273 := by decide
  rcases family_descends (prefixWord ++ tailWord_502273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502305 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_502305 : Nat := 118140960795 + 502305 * 2 ^ 59
def prefixEnd_502305 : Nat := 4983230072969 + 3 ^ 40 * 502305 * 2
def baseEnd_502305 : Nat := 171949266771174975384965

theorem tailTrace_502305 : CollatzResearch.WordTrace tailWord_502305 prefixEnd_502305 171949266771174975384965 := by
  unfold tailWord_502305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320568445242246709268369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12213712296828164472845579 18320568445242246709268369)
  ·
    refine ⟨13740426333931685031951277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18320568445242246709268369 13740426333931685031951277)
    ·
      refine ⟨5152659875224381886981729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13740426333931685031951277 5152659875224381886981729)
      ·
        refine ⟨3864494906418286415236297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5152659875224381886981729 3864494906418286415236297)
        ·
          refine ⟨2898371179813714811427223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3864494906418286415236297 2898371179813714811427223)
          ·
            refine ⟨4347556769720572217140835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898371179813714811427223 4347556769720572217140835)
            ·
              refine ⟨6521335154580858325711253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347556769720572217140835 6521335154580858325711253)
              ·
                refine ⟨305687585370977734017715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6521335154580858325711253 305687585370977734017715)
                ·
                  refine ⟨458531378056466601026573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305687585370977734017715 458531378056466601026573)
                  ·
                    refine ⟨171949266771174975384965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458531378056466601026573 171949266771174975384965)
                    ·
                      rfl

theorem cell22_502305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_502305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502305 prefixEnd_502305 := by exact prefixLift 502305
  have htrace : WordTrace (prefixWord ++ tailWord_502305) baseStart_502305 baseEnd_502305 := by
    simpa [prefixWord, tailWord_502305, baseEnd_502305] using wordTrace_append hprefix tailTrace_502305
  have hstable : (prefixWord ++ tailWord_502305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502305).length < 2 ^ (prefixWord ++ tailWord_502305).sum := by decide
  have hdescent : baseEnd_502305 < baseStart_502305 := by decide
  rcases family_descends (prefixWord ++ tailWord_502305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502324 : List Nat := [2, 5, 1, 3, 2, 1, 2, 6]
def baseStart_502324 : Nat := 118140960795 + 502324 * 2 ^ 59
def prefixEnd_502324 : Nat := 4983230072969 + 3 ^ 40 * 502324 * 2
def baseEnd_502324 : Nat := 19106196762162806573323

theorem tailTrace_502324 : CollatzResearch.WordTrace tailWord_502324 prefixEnd_502324 19106196762162806573323 := by
  unfold tailWord_502324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160630716086706477105013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12214174288115608636140017 9160630716086706477105013)
  ·
    refine ⟨858809129633128732228595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9160630716086706477105013 858809129633128732228595)
    ·
      refine ⟨1288213694449693098342893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858809129633128732228595 1288213694449693098342893)
      ·
        refine ⟨483080135418634911878585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1288213694449693098342893 483080135418634911878585)
        ·
          refine ⟨362310101563976183908939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483080135418634911878585 362310101563976183908939)
          ·
            refine ⟨543465152345964275863409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362310101563976183908939 543465152345964275863409)
            ·
              refine ⟨407598864259473206897557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543465152345964275863409 407598864259473206897557)
              ·
                refine ⟨19106196762162806573323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407598864259473206897557 19106196762162806573323)
                ·
                  rfl

theorem cell22_502324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 6].length) (baseStart_502324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502324 prefixEnd_502324 := by exact prefixLift 502324
  have htrace : WordTrace (prefixWord ++ tailWord_502324) baseStart_502324 baseEnd_502324 := by
    simpa [prefixWord, tailWord_502324, baseEnd_502324] using wordTrace_append hprefix tailTrace_502324
  have hstable : (prefixWord ++ tailWord_502324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502324).length < 2 ^ (prefixWord ++ tailWord_502324).sum := by decide
  have hdescent : baseEnd_502324 < baseStart_502324 := by decide
  rcases family_descends (prefixWord ++ tailWord_502324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502348 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_502348 : Nat := 118140960795 + 502348 * 2 ^ 59
def prefixEnd_502348 : Nat := 4983230072969 + 3 ^ 40 * 502348 * 2
def baseEnd_502348 : Nat := 171963986549937196559833

theorem tailTrace_502348 : CollatzResearch.WordTrace tailWord_502348 prefixEnd_502348 171963986549937196559833 := by
  unfold tailWord_502348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161068392043232526541849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12214757856057643368722465 9161068392043232526541849)
  ·
    refine ⟨6870801294032424394906387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9161068392043232526541849 6870801294032424394906387)
    ·
      refine ⟨10306201941048636592359581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870801294032424394906387 10306201941048636592359581)
      ·
        refine ⟨3864825727893238722134843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10306201941048636592359581 3864825727893238722134843)
        ·
          refine ⟨5797238591839858083202265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864825727893238722134843 5797238591839858083202265)
          ·
            refine ⟨4347928943879893562401699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797238591839858083202265 4347928943879893562401699)
            ·
              refine ⟨6521893415819840343602549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347928943879893562401699 6521893415819840343602549)
              ·
                refine ⟨611427507733110032212739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6521893415819840343602549 611427507733110032212739)
                ·
                  refine ⟨917141261599665048319109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611427507733110032212739 917141261599665048319109)
                  ·
                    refine ⟨171963986549937196559833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917141261599665048319109 171963986549937196559833)
                    ·
                      rfl

theorem cell22_502348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_502348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502348 prefixEnd_502348 := by exact prefixLift 502348
  have htrace : WordTrace (prefixWord ++ tailWord_502348) baseStart_502348 baseEnd_502348 := by
    simpa [prefixWord, tailWord_502348, baseEnd_502348] using wordTrace_append hprefix tailTrace_502348
  have hstable : (prefixWord ++ tailWord_502348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502348).length < 2 ^ (prefixWord ++ tailWord_502348).sum := by decide
  have hdescent : baseEnd_502348 < baseStart_502348 := by decide
  rcases family_descends (prefixWord ++ tailWord_502348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502378 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_502378 : Nat := 118140960795 + 502378 * 2 ^ 59
def prefixEnd_502378 : Nat := 4983230072969 + 3 ^ 40 * 502378 * 2
def baseEnd_502378 : Nat := 171974256163027118309741

theorem tailTrace_502378 : CollatzResearch.WordTrace tailWord_502378 prefixEnd_502378 171974256163027118309741 := by
  unfold tailWord_502378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580807743494445044168947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12215487315985186784450525 4580807743494445044168947)
  ·
    refine ⟨6871211615241667566253421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4580807743494445044168947 6871211615241667566253421)
    ·
      refine ⟨2576704355715625337345033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6871211615241667566253421 2576704355715625337345033)
      ·
        refine ⟨1932528266786719003008775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576704355715625337345033 1932528266786719003008775)
        ·
          refine ⟨2898792400180078504513163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932528266786719003008775 2898792400180078504513163)
          ·
            refine ⟨4348188600270117756769745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898792400180078504513163 4348188600270117756769745)
            ·
              refine ⟨3261141450202588317577309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348188600270117756769745 3261141450202588317577309)
              ·
                refine ⟨1222928043825970619091491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3261141450202588317577309 1222928043825970619091491)
                ·
                  refine ⟨1834392065738955928637237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222928043825970619091491 1834392065738955928637237)
                  ·
                    refine ⟨171974256163027118309741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1834392065738955928637237 171974256163027118309741)
                    ·
                      rfl

theorem cell22_502378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_502378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502378 prefixEnd_502378 := by exact prefixLift 502378
  have htrace : WordTrace (prefixWord ++ tailWord_502378) baseStart_502378 baseEnd_502378 := by
    simpa [prefixWord, tailWord_502378, baseEnd_502378] using wordTrace_append hprefix tailTrace_502378
  have hstable : (prefixWord ++ tailWord_502378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502378).length < 2 ^ (prefixWord ++ tailWord_502378).sum := by decide
  have hdescent : baseEnd_502378 < baseStart_502378 := by decide
  rcases family_descends (prefixWord ++ tailWord_502378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502382 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_502382 : Nat := 118140960795 + 502382 * 2 ^ 59
def prefixEnd_502382 : Nat := 4983230072969 + 3 ^ 40 * 502382 * 2
def baseEnd_502382 : Nat := 171975625444772441209729

theorem tailTrace_502382 : CollatzResearch.WordTrace tailWord_502382 prefixEnd_502382 171975625444772441209729 := by
  unfold tailWord_502382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290422108245411107477675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12215584577308859239880933 2290422108245411107477675)
  ·
    refine ⟨3435633162368116661216513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2290422108245411107477675 3435633162368116661216513)
    ·
      refine ⟨2576724871776087495912385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3435633162368116661216513 2576724871776087495912385)
      ·
        refine ⟨1932543653832065621934289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576724871776087495912385 1932543653832065621934289)
        ·
          refine ⟨1449407740374049216450717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932543653832065621934289 1449407740374049216450717)
          ·
            refine ⟨543527902640268456169019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1449407740374049216450717 543527902640268456169019)
            ·
              refine ⟨815291853960402684253529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543527902640268456169019 815291853960402684253529)
              ·
                refine ⟨611468890470302013190147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815291853960402684253529 611468890470302013190147)
                ·
                  refine ⟨917203335705453019785221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611468890470302013190147 917203335705453019785221)
                  ·
                    refine ⟨171975625444772441209729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917203335705453019785221 171975625444772441209729)
                    ·
                      rfl

theorem cell22_502382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_502382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502382 prefixEnd_502382 := by exact prefixLift 502382
  have htrace : WordTrace (prefixWord ++ tailWord_502382) baseStart_502382 baseEnd_502382 := by
    simpa [prefixWord, tailWord_502382, baseEnd_502382] using wordTrace_append hprefix tailTrace_502382
  have hstable : (prefixWord ++ tailWord_502382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502382).length < 2 ^ (prefixWord ++ tailWord_502382).sum := by decide
  have hdescent : baseEnd_502382 < baseStart_502382 := by decide
  rcases family_descends (prefixWord ++ tailWord_502382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502391 : List Nat := [1, 1, 3, 1, 1, 3, 4, 8]
def baseStart_502391 : Nat := 118140960795 + 502391 * 2 ^ 59
def prefixEnd_502391 : Nat := 4983230072969 + 3 ^ 40 * 502391 * 2
def baseEnd_502391 : Nat := 19108745147633268637189

theorem tailTrace_502391 : CollatzResearch.WordTrace tailWord_502391 prefixEnd_502391 19108745147633268637189 := by
  unfold tailWord_502391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323705122930683396899027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12215803415287122264599351 18323705122930683396899027)
  ·
    refine ⟨27485557684396025095348541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323705122930683396899027 27485557684396025095348541)
    ·
      refine ⟨10307084131648509410755703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27485557684396025095348541 10307084131648509410755703)
      ·
        refine ⟨15460626197472764116133555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10307084131648509410755703 15460626197472764116133555)
        ·
          refine ⟨23190939296209146174200333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460626197472764116133555 23190939296209146174200333)
          ·
            refine ⟨8696602236078429815325125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23190939296209146174200333 8696602236078429815325125)
            ·
              refine ⟨1630612919264705590373461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8696602236078429815325125 1630612919264705590373461)
              ·
                refine ⟨19108745147633268637189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1630612919264705590373461 19108745147633268637189)
                ·
                  rfl

theorem cell22_502391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 8].length) (baseStart_502391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502391 prefixEnd_502391 := by exact prefixLift 502391
  have htrace : WordTrace (prefixWord ++ tailWord_502391) baseStart_502391 baseEnd_502391 := by
    simpa [prefixWord, tailWord_502391, baseEnd_502391] using wordTrace_append hprefix tailTrace_502391
  have hstable : (prefixWord ++ tailWord_502391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502391).length < 2 ^ (prefixWord ++ tailWord_502391).sum := by decide
  have hdescent : baseEnd_502391 < baseStart_502391 := by decide
  rcases family_descends (prefixWord ++ tailWord_502391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502393 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_502393 : Nat := 118140960795 + 502393 * 2 ^ 59
def prefixEnd_502393 : Nat := 4983230072969 + 3 ^ 40 * 502393 * 2
def baseEnd_502393 : Nat := 171979390969572079184695

theorem tailTrace_502393 : CollatzResearch.WordTrace tailWord_502393 prefixEnd_502393 171979390969572079184695 := by
  unfold tailWord_502393
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323778068923437738471833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12215852045948958492314555 18323778068923437738471833)
  ·
    refine ⟨13742833551692578303853875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18323778068923437738471833 13742833551692578303853875)
    ·
      refine ⟨20614250327538867455780813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13742833551692578303853875 20614250327538867455780813)
      ·
        refine ⟨7730343872827075295917805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20614250327538867455780813 7730343872827075295917805)
        ·
          refine ⟨2898878952310153235969177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7730343872827075295917805 2898878952310153235969177)
          ·
            refine ⟨2174159214232614926976883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898878952310153235969177 2174159214232614926976883)
            ·
              refine ⟨3261238821348922390465325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174159214232614926976883 3261238821348922390465325)
              ·
                refine ⟨1222964558005845896424497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3261238821348922390465325 1222964558005845896424497)
                ·
                  refine ⟨917223418504384422318373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222964558005845896424497 917223418504384422318373)
                  ·
                    refine ⟨171979390969572079184695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917223418504384422318373 171979390969572079184695)
                    ·
                      rfl

theorem cell22_502393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_502393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502393 prefixEnd_502393 := by exact prefixLift 502393
  have htrace : WordTrace (prefixWord ++ tailWord_502393) baseStart_502393 baseEnd_502393 := by
    simpa [prefixWord, tailWord_502393, baseEnd_502393] using wordTrace_append hprefix tailTrace_502393
  have hstable : (prefixWord ++ tailWord_502393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502393).length < 2 ^ (prefixWord ++ tailWord_502393).sum := by decide
  have hdescent : baseEnd_502393 < baseStart_502393 := by decide
  rcases family_descends (prefixWord ++ tailWord_502393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502500 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_502500 : Nat := 118140960795 + 502500 * 2 ^ 59
def prefixEnd_502500 : Nat := 4983230072969 + 3 ^ 40 * 502500 * 2
def baseEnd_502500 : Nat := 172016019256259466759367

theorem tailTrace_502500 : CollatzResearch.WordTrace tailWord_502500 prefixEnd_502500 172016019256259466759367 := by
  unfold tailWord_502500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163840339767897506308477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12218453786357196675077969 9163840339767897506308477)
  ·
    refine ⟨3436440127412961564865679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9163840339767897506308477 3436440127412961564865679)
    ·
      refine ⟨5154660191119442347298519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3436440127412961564865679 5154660191119442347298519)
      ·
        refine ⟨7731990286679163520947779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5154660191119442347298519 7731990286679163520947779)
        ·
          refine ⟨11597985430018745281421669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731990286679163520947779 11597985430018745281421669)
          ·
            refine ⟨2174622268128514740266563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11597985430018745281421669 2174622268128514740266563)
            ·
              refine ⟨3261933402192772110399845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174622268128514740266563 3261933402192772110399845)
              ·
                refine ⟨611612512911144770699971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3261933402192772110399845 611612512911144770699971)
                ·
                  refine ⟨917418769366717156049957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611612512911144770699971 917418769366717156049957)
                  ·
                    refine ⟨172016019256259466759367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917418769366717156049957 172016019256259466759367)
                    ·
                      rfl

theorem cell22_502500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_502500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502500 prefixEnd_502500 := by exact prefixLift 502500
  have htrace : WordTrace (prefixWord ++ tailWord_502500) baseStart_502500 baseEnd_502500 := by
    simpa [prefixWord, tailWord_502500, baseEnd_502500] using wordTrace_append hprefix tailTrace_502500
  have hstable : (prefixWord ++ tailWord_502500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502500).length < 2 ^ (prefixWord ++ tailWord_502500).sum := by decide
  have hdescent : baseEnd_502500 < baseStart_502500 := by decide
  rcases family_descends (prefixWord ++ tailWord_502500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502513 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_502513 : Nat := 118140960795 + 502513 * 2 ^ 59
def prefixEnd_502513 : Nat := 4983230072969 + 3 ^ 40 * 502513 * 2
def baseEnd_502513 : Nat := 172020469421931766184327

theorem tailTrace_502513 : CollatzResearch.WordTrace tailWord_502513 prefixEnd_502513 172020469421931766184327 := by
  unfold tailWord_502513
  simp only [CollatzResearch.WordTrace]
  refine ⟨18328154828488698232840193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12218769885659132155226795 18328154828488698232840193)
  ·
    refine ⟨13746116121366523674630145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18328154828488698232840193 13746116121366523674630145)
    ·
      refine ⟨10309587091024892755972609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13746116121366523674630145 10309587091024892755972609)
      ·
        refine ⟨7732190318268669566979457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10309587091024892755972609 7732190318268669566979457)
        ·
          refine ⟨5799142738701502175234593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7732190318268669566979457 5799142738701502175234593)
          ·
            refine ⟨4349357054026126631425945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799142738701502175234593 4349357054026126631425945)
            ·
              refine ⟨3262017790519594973569459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349357054026126631425945 3262017790519594973569459)
              ·
                refine ⟨4893026685779392460354189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262017790519594973569459 4893026685779392460354189)
                ·
                  refine ⟨1834885007167272172632821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4893026685779392460354189 1834885007167272172632821)
                  ·
                    refine ⟨172020469421931766184327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1834885007167272172632821 172020469421931766184327)
                    ·
                      rfl

theorem cell22_502513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_502513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502513 prefixEnd_502513 := by exact prefixLift 502513
  have htrace : WordTrace (prefixWord ++ tailWord_502513) baseStart_502513 baseEnd_502513 := by
    simpa [prefixWord, tailWord_502513, baseEnd_502513] using wordTrace_append hprefix tailTrace_502513
  have hstable : (prefixWord ++ tailWord_502513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502513).length < 2 ^ (prefixWord ++ tailWord_502513).sum := by decide
  have hdescent : baseEnd_502513 < baseStart_502513 := by decide
  rcases family_descends (prefixWord ++ tailWord_502513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502543 : List Nat := [1, 1, 2, 1, 1, 1, 8, 7]
def baseStart_502543 : Nat := 118140960795 + 502543 * 2 ^ 59
def prefixEnd_502543 : Nat := 4983230072969 + 3 ^ 40 * 502543 * 2
def baseEnd_502543 : Nat := 19114526559446854214915

theorem tailTrace_502543 : CollatzResearch.WordTrace tailWord_502543 prefixEnd_502543 19114526559446854214915 := by
  unfold tailWord_502543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329249018380013356432283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12219499345586675570954855 18329249018380013356432283)
  ·
    refine ⟨27493873527570020034648425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18329249018380013356432283 27493873527570020034648425)
    ·
      refine ⟨20620405145677515025986319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27493873527570020034648425 20620405145677515025986319)
      ·
        refine ⟨30930607718516272538979479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620405145677515025986319 30930607718516272538979479)
        ·
          refine ⟨46395911577774408808469219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30930607718516272538979479 46395911577774408808469219)
          ·
            refine ⟨69593867366661613212703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46395911577774408808469219 69593867366661613212703829)
            ·
              refine ⟨815553133203065779836373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69593867366661613212703829 815553133203065779836373)
              ·
                refine ⟨19114526559446854214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 815553133203065779836373 19114526559446854214915)
                ·
                  rfl

theorem cell22_502543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 7].length) (baseStart_502543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502543 prefixEnd_502543 := by exact prefixLift 502543
  have htrace : WordTrace (prefixWord ++ tailWord_502543) baseStart_502543 baseEnd_502543 := by
    simpa [prefixWord, tailWord_502543, baseEnd_502543] using wordTrace_append hprefix tailTrace_502543
  have hstable : (prefixWord ++ tailWord_502543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502543).length < 2 ^ (prefixWord ++ tailWord_502543).sum := by decide
  have hdescent : baseEnd_502543 < baseStart_502543 := by decide
  rcases family_descends (prefixWord ++ tailWord_502543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502562 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_502562 : Nat := 118140960795 + 502562 * 2 ^ 59
def prefixEnd_502562 : Nat := 4983230072969 + 3 ^ 40 * 502562 * 2
def baseEnd_502562 : Nat := 172037243123311971709177

theorem tailTrace_502562 : CollatzResearch.WordTrace tailWord_502562 prefixEnd_502562 172037243123311971709177 := by
  unfold tailWord_502562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582485501327794900343485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12219961336874119734249293 4582485501327794900343485)
  ·
    refine ⟨1718432062997923087628807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4582485501327794900343485 1718432062997923087628807)
    ·
      refine ⟨2577648094496884631443211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718432062997923087628807 2577648094496884631443211)
      ·
        refine ⟨3866472141745326947164817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577648094496884631443211 3866472141745326947164817)
        ·
          refine ⟨2899854106308995210373613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866472141745326947164817 2899854106308995210373613)
          ·
            refine ⟨1087445289865873203890105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2899854106308995210373613 1087445289865873203890105)
            ·
              refine ⟨815583967399404902917579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087445289865873203890105 815583967399404902917579)
              ·
                refine ⟨1223375951099107354376369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815583967399404902917579 1223375951099107354376369)
                ·
                  refine ⟨917531963324330515782277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223375951099107354376369 917531963324330515782277)
                  ·
                    refine ⟨172037243123311971709177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917531963324330515782277 172037243123311971709177)
                    ·
                      rfl

theorem cell22_502562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_502562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502562 prefixEnd_502562 := by exact prefixLift 502562
  have htrace : WordTrace (prefixWord ++ tailWord_502562) baseStart_502562 baseEnd_502562 := by
    simpa [prefixWord, tailWord_502562, baseEnd_502562] using wordTrace_append hprefix tailTrace_502562
  have hstable : (prefixWord ++ tailWord_502562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502562).length < 2 ^ (prefixWord ++ tailWord_502562).sum := by decide
  have hdescent : baseEnd_502562 < baseStart_502562 := by decide
  rcases family_descends (prefixWord ++ tailWord_502562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502701 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 6]
def baseStart_502701 : Nat := 118140960795 + 502701 * 2 ^ 59
def prefixEnd_502701 : Nat := 4983230072969 + 3 ^ 40 * 502701 * 2
def baseEnd_502701 : Nat := 57361608554653980827917

theorem tailTrace_502701 : CollatzResearch.WordTrace tailWord_502701 prefixEnd_502701 57361608554653980827917 := by
  unfold tailWord_502701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18335011751807606340683957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12223341167871737560455971 18335011751807606340683957)
  ·
    refine ⟨1718907351731963094439121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18335011751807606340683957 1718907351731963094439121)
    ·
      refine ⟨1289180513798972320829341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1718907351731963094439121 1289180513798972320829341)
      ·
        refine ⟨483442692674614620311003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1289180513798972320829341 483442692674614620311003)
        ·
          refine ⟨725164039011921930466505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483442692674614620311003 725164039011921930466505)
          ·
            refine ⟨543873029258941447849879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725164039011921930466505 543873029258941447849879)
            ·
              refine ⟨815809543888412171774819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543873029258941447849879 815809543888412171774819)
              ·
                refine ⟨1223714315832618257662229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815809543888412171774819 1223714315832618257662229)
                ·
                  refine ⟨57361608554653980827917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1223714315832618257662229 57361608554653980827917)
                  ·
                    rfl

theorem cell22_502701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_502701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502701 prefixEnd_502701 := by exact prefixLift 502701
  have htrace : WordTrace (prefixWord ++ tailWord_502701) baseStart_502701 baseEnd_502701 := by
    simpa [prefixWord, tailWord_502701, baseEnd_502701] using wordTrace_append hprefix tailTrace_502701
  have hstable : (prefixWord ++ tailWord_502701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502701).length < 2 ^ (prefixWord ++ tailWord_502701).sum := by decide
  have hdescent : baseEnd_502701 < baseStart_502701 := by decide
  rcases family_descends (prefixWord ++ tailWord_502701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502727 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 3, 3]
def baseStart_502727 : Nat := 118140960795 + 502727 * 2 ^ 59
def prefixEnd_502727 : Nat := 4983230072969 + 3 ^ 40 * 502727 * 2
def baseEnd_502727 : Nat := 172093725995306541333671

theorem tailTrace_502727 : CollatzResearch.WordTrace tailWord_502727 prefixEnd_502727 172093725995306541333671 := by
  unfold tailWord_502727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18335960049713412781130435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12223973366475608520753623 18335960049713412781130435)
  ·
    refine ⟨27503940074570119171695653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18335960049713412781130435 27503940074570119171695653)
    ·
      refine ⟨5156988763981897344692935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27503940074570119171695653 5156988763981897344692935)
      ·
        refine ⟨7735483145972846017039403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156988763981897344692935 7735483145972846017039403)
        ·
          refine ⟨11603224718959269025559105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735483145972846017039403 11603224718959269025559105)
          ·
            refine ⟨8702418539219451769169329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603224718959269025559105 8702418539219451769169329)
            ·
              refine ⟨6526813904414588826876997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702418539219451769169329 6526813904414588826876997)
              ·
                refine ⟨1223777607077735405039437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6526813904414588826876997 1223777607077735405039437)
                ·
                  refine ⟨458916602654150776889789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223777607077735405039437 458916602654150776889789)
                  ·
                    refine ⟨172093725995306541333671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458916602654150776889789 172093725995306541333671)
                    ·
                      rfl

theorem cell22_502727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_502727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502727 prefixEnd_502727 := by exact prefixLift 502727
  have htrace : WordTrace (prefixWord ++ tailWord_502727) baseStart_502727 baseEnd_502727 := by
    simpa [prefixWord, tailWord_502727, baseEnd_502727] using wordTrace_append hprefix tailTrace_502727
  have hstable : (prefixWord ++ tailWord_502727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502727).length < 2 ^ (prefixWord ++ tailWord_502727).sum := by decide
  have hdescent : baseEnd_502727 < baseStart_502727 := by decide
  rcases family_descends (prefixWord ++ tailWord_502727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502733 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_502733 : Nat := 118140960795 + 502733 * 2 ^ 59
def prefixEnd_502733 : Nat := 4983230072969 + 3 ^ 40 * 502733 * 2
def baseEnd_502733 : Nat := 172095779917924525683653

theorem tailTrace_502733 : CollatzResearch.WordTrace tailWord_502733 prefixEnd_502733 172095779917924525683653 := by
  unfold tailWord_502733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336178887691675805848853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12224119258461117203899235 18336178887691675805848853)
  ·
    refine ⟨859508385360547303399165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18336178887691675805848853 859508385360547303399165)
    ·
      refine ⟨322315644510205238774687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 859508385360547303399165 322315644510205238774687)
      ·
        refine ⟨483473466765307858162031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322315644510205238774687 483473466765307858162031)
        ·
          refine ⟨725210200147961787243047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483473466765307858162031 725210200147961787243047)
          ·
            refine ⟨1087815300221942680864571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725210200147961787243047 1087815300221942680864571)
            ·
              refine ⟨1631722950332914021296857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087815300221942680864571 1631722950332914021296857)
              ·
                refine ⟨1223792212749685515972643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631722950332914021296857 1223792212749685515972643)
                ·
                  refine ⟨1835688319124528273958965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223792212749685515972643 1835688319124528273958965)
                  ·
                    refine ⟨172095779917924525683653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1835688319124528273958965 172095779917924525683653)
                    ·
                      rfl

theorem cell22_502733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_502733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502733 prefixEnd_502733 := by exact prefixLift 502733
  have htrace : WordTrace (prefixWord ++ tailWord_502733) baseStart_502733 baseEnd_502733 := by
    simpa [prefixWord, tailWord_502733, baseEnd_502733] using wordTrace_append hprefix tailTrace_502733
  have hstable : (prefixWord ++ tailWord_502733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502733).length < 2 ^ (prefixWord ++ tailWord_502733).sum := by decide
  have hdescent : baseEnd_502733 < baseStart_502733 := by decide
  rcases family_descends (prefixWord ++ tailWord_502733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502774 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_502774 : Nat := 118140960795 + 502774 * 2 ^ 59
def prefixEnd_502774 : Nat := 4983230072969 + 3 ^ 40 * 502774 * 2
def baseEnd_502774 : Nat := 57369938351938028469509

theorem tailTrace_502774 : CollatzResearch.WordTrace tailWord_502774 prefixEnd_502774 57369938351938028469509 := by
  unfold tailWord_502774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146104642533946238005711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12225116187028759872060917 1146104642533946238005711)
  ·
    refine ⟨1719156963800919357008567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146104642533946238005711 1719156963800919357008567)
    ·
      refine ⟨2578735445701379035512851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1719156963800919357008567 2578735445701379035512851)
      ·
        refine ⟨3868103168552068553269277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578735445701379035512851 3868103168552068553269277)
        ·
          refine ⟨1450538688207025707475979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3868103168552068553269277 1450538688207025707475979)
          ·
            refine ⟨2175808032310538561213969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450538688207025707475979 2175808032310538561213969)
            ·
              refine ⟨1631856024232903920910477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175808032310538561213969 1631856024232903920910477)
              ·
                refine ⟨611946009087338970341429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631856024232903920910477 611946009087338970341429)
                ·
                  refine ⟨57369938351938028469509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611946009087338970341429 57369938351938028469509)
                  ·
                    rfl

theorem cell22_502774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_502774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502774 prefixEnd_502774 := by exact prefixLift 502774
  have htrace : WordTrace (prefixWord ++ tailWord_502774) baseStart_502774 baseEnd_502774 := by
    simpa [prefixWord, tailWord_502774, baseEnd_502774] using wordTrace_append hprefix tailTrace_502774
  have hstable : (prefixWord ++ tailWord_502774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502774).length < 2 ^ (prefixWord ++ tailWord_502774).sum := by decide
  have hdescent : baseEnd_502774 < baseStart_502774 := by decide
  rcases family_descends (prefixWord ++ tailWord_502774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502819 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 4]
def baseStart_502819 : Nat := 118140960795 + 502819 * 2 ^ 59
def prefixEnd_502819 : Nat := 4983230072969 + 3 ^ 40 * 502819 * 2
def baseEnd_502819 : Nat := 57375073158482989344463

theorem tailTrace_502819 : CollatzResearch.WordTrace tailWord_502819 prefixEnd_502819 57375073158482989344463 := by
  unfold tailWord_502819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18339315565380112493479511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12226210376920074995653007 18339315565380112493479511)
  ·
    refine ⟨27508973348070168740219267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18339315565380112493479511 27508973348070168740219267)
    ·
      refine ⟨41263460022105253110328901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27508973348070168740219267 41263460022105253110328901)
      ·
        refine ⟨7736898754144734958186669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41263460022105253110328901 7736898754144734958186669)
        ·
          refine ⟨2901337032804275609320001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7736898754144734958186669 2901337032804275609320001)
          ·
            refine ⟨2176002774603206706990001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901337032804275609320001 2176002774603206706990001)
            ·
              refine ⟨1632002080952405030242501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176002774603206706990001 1632002080952405030242501)
              ·
                refine ⟨306000390178575943170469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1632002080952405030242501 306000390178575943170469)
                ·
                  refine ⟨57375073158482989344463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306000390178575943170469 57375073158482989344463)
                  ·
                    rfl

theorem cell22_502819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 4].length) (baseStart_502819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_502819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_502819 prefixEnd_502819 := by exact prefixLift 502819
  have htrace : WordTrace (prefixWord ++ tailWord_502819) baseStart_502819 baseEnd_502819 := by
    simpa [prefixWord, tailWord_502819, baseEnd_502819] using wordTrace_append hprefix tailTrace_502819
  have hstable : (prefixWord ++ tailWord_502819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502819).length < 2 ^ (prefixWord ++ tailWord_502819).sum := by decide
  have hdescent : baseEnd_502819 < baseStart_502819 := by decide
  rcases family_descends (prefixWord ++ tailWord_502819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
