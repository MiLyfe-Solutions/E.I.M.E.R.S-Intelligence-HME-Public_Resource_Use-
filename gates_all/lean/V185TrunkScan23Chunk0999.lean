import V185TrunkScan23Chunk0998

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5916000 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 8]
def baseStart_5916000 : Nat := 118140960795 + 5916000 * 2 ^ 59
def prefixEnd_5916000 : Nat := 4983230072969 + 3 ^ 40 * 5916000 * 2
def baseEnd_5916000 : Nat := 337527950222106539610313

theorem tailTrace_5916000 : CollatzResearch.WordTrace tailWord_5916000 prefixEnd_5916000 337527950222106539610313 := by
  unfold tailWord_5916000
  simp only [CollatzResearch.WordTrace]
  refine ⟨107887123283674923602628727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143849497711566564803504969 107887123283674923602628727)
  ·
    refine ⟨161830684925512385403943091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107887123283674923602628727 161830684925512385403943091)
    ·
      refine ⟨242746027388268578105914637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161830684925512385403943091 242746027388268578105914637)
      ·
        refine ⟨91029760270600716789717989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242746027388268578105914637 91029760270600716789717989)
        ·
          refine ⟨17068080050737634398072123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91029760270600716789717989 17068080050737634398072123)
          ·
            refine ⟨25602120076106451597108185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17068080050737634398072123 25602120076106451597108185)
            ·
              refine ⟨19201590057079838697831139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25602120076106451597108185 19201590057079838697831139)
              ·
                refine ⟨28802385085619758046746709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19201590057079838697831139 28802385085619758046746709)
                ·
                  refine ⟨337527950222106539610313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28802385085619758046746709 337527950222106539610313)
                  ·
                    rfl

theorem cell23_5916000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_5916000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916000 prefixEnd_5916000 := by exact prefixLift 5916000
  have htrace : WordTrace (prefixWord ++ tailWord_5916000) baseStart_5916000 baseEnd_5916000 := by
    simpa [prefixWord, tailWord_5916000, baseEnd_5916000] using wordTrace_append hprefix tailTrace_5916000
  have hstable : (prefixWord ++ tailWord_5916000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916000).length < 2 ^ (prefixWord ++ tailWord_5916000).sum := by decide
  have hdescent : baseEnd_5916000 < baseStart_5916000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916004 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_5916004 : Nat := 118140960795 + 5916004 * 2 ^ 59
def prefixEnd_5916004 : Nat := 4983230072969 + 3 ^ 40 * 5916004 * 2
def baseEnd_5916004 : Nat := 1012584535307192280280933

theorem tailTrace_5916004 : CollatzResearch.WordTrace tailWord_5916004 prefixEnd_5916004 1012584535307192280280933 := by
  unfold tailWord_5916004
  simp only [CollatzResearch.WordTrace]
  refine ⟨107887196229667677944201533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143849594972890237258935377 107887196229667677944201533)
  ·
    refine ⟨40457698586125379229075575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107887196229667677944201533 40457698586125379229075575)
    ·
      refine ⟨60686547879188068843613363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40457698586125379229075575 60686547879188068843613363)
      ·
        refine ⟨91029821818782103265420045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60686547879188068843613363 91029821818782103265420045)
        ·
          refine ⟨34136183182043288724532517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91029821818782103265420045 34136183182043288724532517)
          ·
            refine ⟨6400534346633116635849847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34136183182043288724532517 6400534346633116635849847)
            ·
              refine ⟨9600801519949674953774771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400534346633116635849847 9600801519949674953774771)
              ·
                refine ⟨14401202279924512430662157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9600801519949674953774771 14401202279924512430662157)
                ·
                  refine ⟨5400450854971692161498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14401202279924512430662157 5400450854971692161498309)
                  ·
                    refine ⟨1012584535307192280280933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400450854971692161498309 1012584535307192280280933)
                    ·
                      rfl

theorem cell23_5916004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_5916004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916004 prefixEnd_5916004 := by exact prefixLift 5916004
  have htrace : WordTrace (prefixWord ++ tailWord_5916004) baseStart_5916004 baseEnd_5916004 := by
    simpa [prefixWord, tailWord_5916004, baseEnd_5916004] using wordTrace_append hprefix tailTrace_5916004
  have hstable : (prefixWord ++ tailWord_5916004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916004).length < 2 ^ (prefixWord ++ tailWord_5916004).sum := by decide
  have hdescent : baseEnd_5916004 < baseStart_5916004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916017 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 6]
def baseStart_5916017 : Nat := 118140960795 + 5916017 * 2 ^ 59
def prefixEnd_5916017 : Nat := 4983230072969 + 3 ^ 40 * 5916017 * 2
def baseEnd_5916017 : Nat := 337528920130009476664471

theorem tailTrace_5916017 : CollatzResearch.WordTrace tailWord_5916017 prefixEnd_5916017 337528920130009476664471 := by
  unfold tailWord_5916017
  simp only [CollatzResearch.WordTrace]
  refine ⟨215774866608288259108626305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143849911072192172739084203 215774866608288259108626305)
  ·
    refine ⟨161831149956216194331469729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215774866608288259108626305 161831149956216194331469729)
    ·
      refine ⟨121373362467162145748602297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161831149956216194331469729 121373362467162145748602297)
      ·
        refine ⟨91030021850371609311451723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121373362467162145748602297 91030021850371609311451723)
        ·
          refine ⟨136545032775557413967177585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91030021850371609311451723 136545032775557413967177585)
          ·
            refine ⟨102408774581668060475383189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136545032775557413967177585 102408774581668060475383189)
            ·
              refine ⟨4800411308515690334783587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102408774581668060475383189 4800411308515690334783587)
              ·
                refine ⟨7200616962773535502175381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800411308515690334783587 7200616962773535502175381)
                ·
                  refine ⟨337528920130009476664471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7200616962773535502175381 337528920130009476664471)
                  ·
                    rfl

theorem cell23_5916017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_5916017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916017 prefixEnd_5916017 := by exact prefixLift 5916017
  have htrace : WordTrace (prefixWord ++ tailWord_5916017) baseStart_5916017 baseEnd_5916017 := by
    simpa [prefixWord, tailWord_5916017, baseEnd_5916017] using wordTrace_append hprefix tailTrace_5916017
  have hstable : (prefixWord ++ tailWord_5916017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916017).length < 2 ^ (prefixWord ++ tailWord_5916017).sum := by decide
  have hdescent : baseEnd_5916017 < baseStart_5916017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916027 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 3]
def baseStart_5916027 : Nat := 118140960795 + 5916027 * 2 ^ 59
def prefixEnd_5916027 : Nat := 4983230072969 + 3 ^ 40 * 5916027 * 2
def baseEnd_5916027 : Nat := 3037765415976630250855193

theorem tailTrace_5916027 : CollatzResearch.WordTrace tailWord_5916027 prefixEnd_5916027 3037765415976630250855193 := by
  unfold tailWord_5916027
  simp only [CollatzResearch.WordTrace]
  refine ⟨215775231338252030816490335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143850154225501353877660223 215775231338252030816490335)
  ·
    refine ⟨323662847007378046224735503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215775231338252030816490335 323662847007378046224735503)
    ·
      refine ⟨485494270511067069337103255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323662847007378046224735503 485494270511067069337103255)
      ·
        refine ⟨728241405766600604005654883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485494270511067069337103255 728241405766600604005654883)
        ·
          refine ⟨1092362108649900906008482325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728241405766600604005654883 1092362108649900906008482325)
          ·
            refine ⟨51204473842964104969147609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1092362108649900906008482325 51204473842964104969147609)
            ·
              refine ⟨38403355382223078726860707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51204473842964104969147609 38403355382223078726860707)
              ·
                refine ⟨57605033073334618090291061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38403355382223078726860707 57605033073334618090291061)
                ·
                  refine ⟨5400471850625120445964787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57605033073334618090291061 5400471850625120445964787)
                  ·
                    refine ⟨8100707775937680668947181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400471850625120445964787 8100707775937680668947181)
                    ·
                      refine ⟨3037765415976630250855193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8100707775937680668947181 3037765415976630250855193)
                      ·
                        rfl

theorem cell23_5916027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 1, 3].length) (baseStart_5916027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916027 prefixEnd_5916027 := by exact prefixLift 5916027
  have htrace : WordTrace (prefixWord ++ tailWord_5916027) baseStart_5916027 baseEnd_5916027 := by
    simpa [prefixWord, tailWord_5916027, baseEnd_5916027] using wordTrace_append hprefix tailTrace_5916027
  have hstable : (prefixWord ++ tailWord_5916027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916027).length < 2 ^ (prefixWord ++ tailWord_5916027).sum := by decide
  have hdescent : baseEnd_5916027 < baseStart_5916027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916037 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_5916037 : Nat := 118140960795 + 5916037 * 2 ^ 59
def prefixEnd_5916037 : Nat := 4983230072969 + 3 ^ 40 * 5916037 * 2
def baseEnd_5916037 : Nat := 3037770550783175211730147

theorem tailTrace_5916037 : CollatzResearch.WordTrace tailWord_5916037 prefixEnd_5916037 3037770550783175211730147 := by
  unfold tailWord_5916037
  simp only [CollatzResearch.WordTrace]
  refine ⟨215775596068215802524354365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143850397378810535016236243 215775596068215802524354365)
  ·
    refine ⟨80915848525580925946632887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215775596068215802524354365 80915848525580925946632887)
    ·
      refine ⟨121373772788371388919949331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80915848525580925946632887 121373772788371388919949331)
      ·
        refine ⟨182060659182557083379923997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121373772788371388919949331 182060659182557083379923997)
        ·
          refine ⟨68272747193458906267471499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182060659182557083379923997 68272747193458906267471499)
          ·
            refine ⟨102409120790188359401207249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68272747193458906267471499 102409120790188359401207249)
            ·
              refine ⟨76806840592641269550905437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102409120790188359401207249 76806840592641269550905437)
              ·
                refine ⟨28802565222240476081589539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76806840592641269550905437 28802565222240476081589539)
                ·
                  refine ⟨43203847833360714122384309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28802565222240476081589539 43203847833360714122384309)
                  ·
                    refine ⟨4050360734377566948973529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43203847833360714122384309 4050360734377566948973529)
                    ·
                      refine ⟨3037770550783175211730147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050360734377566948973529 3037770550783175211730147)
                      ·
                        rfl

theorem cell23_5916037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_5916037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916037 prefixEnd_5916037 := by exact prefixLift 5916037
  have htrace : WordTrace (prefixWord ++ tailWord_5916037) baseStart_5916037 baseEnd_5916037 := by
    simpa [prefixWord, tailWord_5916037, baseEnd_5916037] using wordTrace_append hprefix tailTrace_5916037
  have hstable : (prefixWord ++ tailWord_5916037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916037).length < 2 ^ (prefixWord ++ tailWord_5916037).sum := by decide
  have hdescent : baseEnd_5916037 < baseStart_5916037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916087 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_5916087 : Nat := 118140960795 + 5916087 * 2 ^ 59
def prefixEnd_5916087 : Nat := 4983230072969 + 3 ^ 40 * 5916087 * 2
def baseEnd_5916087 : Nat := 3037796224815900016104917

theorem tailTrace_5916087 : CollatzResearch.WordTrace tailWord_5916087 prefixEnd_5916087 3037796224815900016104917 := by
  unfold tailWord_5916087
  simp only [CollatzResearch.WordTrace]
  refine ⟨215777419718034661063674515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143851613145356440709116343 215777419718034661063674515)
  ·
    refine ⟨323666129577051991595511773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215777419718034661063674515 323666129577051991595511773)
    ·
      refine ⟨121374798591394496848316915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323666129577051991595511773 121374798591394496848316915)
      ·
        refine ⟨182062197887091745272475373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121374798591394496848316915 182062197887091745272475373)
        ·
          refine ⟨68273324207659404477178265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182062197887091745272475373 68273324207659404477178265)
          ·
            refine ⟨51204993155744553357883699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68273324207659404477178265 51204993155744553357883699)
            ·
              refine ⟨76807489733616830036825549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51204993155744553357883699 76807489733616830036825549)
              ·
                refine ⟨28802808650106311263809581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76807489733616830036825549 28802808650106311263809581)
                ·
                  refine ⟨10801053243789866723928593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28802808650106311263809581 10801053243789866723928593)
                  ·
                    refine ⟨8100789932842400042946445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10801053243789866723928593 8100789932842400042946445)
                    ·
                      refine ⟨3037796224815900016104917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8100789932842400042946445 3037796224815900016104917)
                      ·
                        rfl

theorem cell23_5916087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_5916087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916087 prefixEnd_5916087 := by exact prefixLift 5916087
  have htrace : WordTrace (prefixWord ++ tailWord_5916087) baseStart_5916087 baseEnd_5916087 := by
    simpa [prefixWord, tailWord_5916087, baseEnd_5916087] using wordTrace_append hprefix tailTrace_5916087
  have hstable : (prefixWord ++ tailWord_5916087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916087).length < 2 ^ (prefixWord ++ tailWord_5916087).sum := by decide
  have hdescent : baseEnd_5916087 < baseStart_5916087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916104 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_5916104 : Nat := 118140960795 + 5916104 * 2 ^ 59
def prefixEnd_5916104 : Nat := 4983230072969 + 3 ^ 40 * 5916104 * 2
def baseEnd_5916104 : Nat := 3037804953987026449592339

theorem tailTrace_5916104 : CollatzResearch.WordTrace tailWord_5916104 prefixEnd_5916104 3037804953987026449592339 := by
  unfold tailWord_5916104
  simp only [CollatzResearch.WordTrace]
  refine ⟨107889019879486536483521683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143852026505982048644695577 107889019879486536483521683)
  ·
    refine ⟨161833529819229804725282525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107889019879486536483521683 161833529819229804725282525)
    ·
      refine ⟨60687573682211176771980947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161833529819229804725282525 60687573682211176771980947)
      ·
        refine ⟨91031360523316765157971421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60687573682211176771980947 91031360523316765157971421)
        ·
          refine ⟨34136760196243786934239283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91031360523316765157971421 34136760196243786934239283)
          ·
            refine ⟨51205140294365680401358925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34136760196243786934239283 51205140294365680401358925)
            ·
              refine ⟨19201927610387130150509597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51205140294365680401358925 19201927610387130150509597)
              ·
                refine ⟨7200722853895173806441099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19201927610387130150509597 7200722853895173806441099)
                ·
                  refine ⟨10801084280842760709661649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200722853895173806441099 10801084280842760709661649)
                  ·
                    refine ⟨8100813210632070532246237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10801084280842760709661649 8100813210632070532246237)
                    ·
                      refine ⟨3037804953987026449592339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8100813210632070532246237 3037804953987026449592339)
                      ·
                        rfl

theorem cell23_5916104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_5916104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916104 prefixEnd_5916104 := by exact prefixLift 5916104
  have htrace : WordTrace (prefixWord ++ tailWord_5916104) baseStart_5916104 baseEnd_5916104 := by
    simpa [prefixWord, tailWord_5916104, baseEnd_5916104] using wordTrace_append hprefix tailTrace_5916104
  have hstable : (prefixWord ++ tailWord_5916104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916104).length < 2 ^ (prefixWord ++ tailWord_5916104).sum := by decide
  have hdescent : baseEnd_5916104 < baseStart_5916104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916118 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5916118 : Nat := 118140960795 + 5916118 * 2 ^ 59
def prefixEnd_5916118 : Nat := 4983230072969 + 3 ^ 40 * 5916118 * 2
def baseEnd_5916118 : Nat := 3037812142716189394817275

theorem tailTrace_5916118 : CollatzResearch.WordTrace tailWord_5916118 prefixEnd_5916118 3037812142716189394817275 := by
  unfold tailWord_5916118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486159398807647084878313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143852366920614902238702005 13486159398807647084878313)
  ·
    refine ⟨10114619549105735313658735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13486159398807647084878313 10114619549105735313658735)
    ·
      refine ⟨15171929323658602970488103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114619549105735313658735 15171929323658602970488103)
      ·
        refine ⟨22757893985487904455732155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15171929323658602970488103 22757893985487904455732155)
        ·
          refine ⟨34136840978231856683598233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22757893985487904455732155 34136840978231856683598233)
          ·
            refine ⟨25602630733673892512698675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34136840978231856683598233 25602630733673892512698675)
            ·
              refine ⟨38403946100510838769048013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25602630733673892512698675 38403946100510838769048013)
              ·
                refine ⟨14401479787691564538393005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38403946100510838769048013 14401479787691564538393005)
                ·
                  refine ⟨5400554920384336701897377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14401479787691564538393005 5400554920384336701897377)
                  ·
                    refine ⟨4050416190288252526423033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400554920384336701897377 4050416190288252526423033)
                    ·
                      refine ⟨3037812142716189394817275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050416190288252526423033 3037812142716189394817275)
                      ·
                        rfl

theorem cell23_5916118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5916118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916118 prefixEnd_5916118 := by exact prefixLift 5916118
  have htrace : WordTrace (prefixWord ++ tailWord_5916118) baseStart_5916118 baseEnd_5916118 := by
    simpa [prefixWord, tailWord_5916118, baseEnd_5916118] using wordTrace_append hprefix tailTrace_5916118
  have hstable : (prefixWord ++ tailWord_5916118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916118).length < 2 ^ (prefixWord ++ tailWord_5916118).sum := by decide
  have hdescent : baseEnd_5916118 < baseStart_5916118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916120 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_5916120 : Nat := 118140960795 + 5916120 * 2 ^ 59
def prefixEnd_5916120 : Nat := 4983230072969 + 3 ^ 40 * 5916120 * 2
def baseEnd_5916120 : Nat := 1012604389892499462330755

theorem tailTrace_5916120 : CollatzResearch.WordTrace tailWord_5916120 prefixEnd_5916120 1012604389892499462330755 := by
  unfold tailWord_5916120
  simp only [CollatzResearch.WordTrace]
  refine ⟨107889311663457553849812907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143852415551276738466417209 107889311663457553849812907)
  ·
    refine ⟨161833967495186330774719361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107889311663457553849812907 161833967495186330774719361)
    ·
      refine ⟨121375475621389748081039521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161833967495186330774719361 121375475621389748081039521)
      ·
        refine ⟨91031606716042311060779641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121375475621389748081039521 91031606716042311060779641)
        ·
          refine ⟨68273705037031733295584731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91031606716042311060779641 68273705037031733295584731)
          ·
            refine ⟨102410557555547599943377097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68273705037031733295584731 102410557555547599943377097)
            ·
              refine ⟨76807918166660699957532823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102410557555547599943377097 76807918166660699957532823)
              ·
                refine ⟨115211877249991049936299235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76807918166660699957532823 115211877249991049936299235)
                ·
                  refine ⟨172817815874986574904448853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115211877249991049936299235 172817815874986574904448853)
                  ·
                    refine ⟨1012604389892499462330755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 172817815874986574904448853 1012604389892499462330755)
                    ·
                      rfl

theorem cell23_5916120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_5916120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916120 prefixEnd_5916120 := by exact prefixLift 5916120
  have htrace : WordTrace (prefixWord ++ tailWord_5916120) baseStart_5916120 baseEnd_5916120 := by
    simpa [prefixWord, tailWord_5916120, baseEnd_5916120] using wordTrace_append hprefix tailTrace_5916120
  have hstable : (prefixWord ++ tailWord_5916120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916120).length < 2 ^ (prefixWord ++ tailWord_5916120).sum := by decide
  have hdescent : baseEnd_5916120 < baseStart_5916120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916140 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_5916140 : Nat := 118140960795 + 5916140 * 2 ^ 59
def prefixEnd_5916140 : Nat := 4983230072969 + 3 ^ 40 * 5916140 * 2
def baseEnd_5916140 : Nat := 3037823439290588308742173

theorem tailTrace_5916140 : CollatzResearch.WordTrace tailWord_5916140 prefixEnd_5916140 3037823439290588308742173 := by
  unfold tailWord_5916140
  simp only [CollatzResearch.WordTrace]
  refine ⟨107889676393421325557676937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143852901857895100743569249 107889676393421325557676937)
  ·
    refine ⟨80917257295065994168257703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107889676393421325557676937 80917257295065994168257703)
    ·
      refine ⟨121375885942598991252386555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80917257295065994168257703 121375885942598991252386555)
      ·
        refine ⟨182063828913898486878579833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121375885942598991252386555 182063828913898486878579833)
        ·
          refine ⟨136547871685423865158934875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182063828913898486878579833 136547871685423865158934875)
          ·
            refine ⟨204821807528135797738402313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136547871685423865158934875 204821807528135797738402313)
            ·
              refine ⟨153616355646101848303801735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204821807528135797738402313 153616355646101848303801735)
              ·
                refine ⟨230424533469152772455702603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153616355646101848303801735 230424533469152772455702603)
                ·
                  refine ⟨345636800203729158683553905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230424533469152772455702603 345636800203729158683553905)
                  ·
                    refine ⟨259227600152796869012665429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345636800203729158683553905 259227600152796869012665429)
                    ·
                      refine ⟨3037823439290588308742173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 259227600152796869012665429 3037823439290588308742173)
                      ·
                        rfl

theorem cell23_5916140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_5916140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916140 prefixEnd_5916140 := by exact prefixLift 5916140
  have htrace : WordTrace (prefixWord ++ tailWord_5916140) baseStart_5916140 baseEnd_5916140 := by
    simpa [prefixWord, tailWord_5916140, baseEnd_5916140] using wordTrace_append hprefix tailTrace_5916140
  have hstable : (prefixWord ++ tailWord_5916140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916140).length < 2 ^ (prefixWord ++ tailWord_5916140).sum := by decide
  have hdescent : baseEnd_5916140 < baseStart_5916140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916141 : List Nat := [1, 5, 1, 3, 2, 2, 2, 7]
def baseStart_5916141 : Nat := 118140960795 + 5916141 * 2 ^ 59
def prefixEnd_5916141 : Nat := 4983230072969 + 3 ^ 40 * 5916141 * 2
def baseEnd_5916141 : Nat := 112511998250786770549247

theorem tailTrace_5916141 : CollatzResearch.WordTrace tailWord_5916141 prefixEnd_5916141 112511998250786770549247 := by
  unfold tailWord_5916141
  simp only [CollatzResearch.WordTrace]
  refine ⟨215779389259839028286140277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143852926173226018857426851 215779389259839028286140277)
  ·
    refine ⟨20229317743109908901825651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215779389259839028286140277 20229317743109908901825651)
    ·
      refine ⟨30343976614664863352738477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20229317743109908901825651 30343976614664863352738477)
      ·
        refine ⟨11378991230499323757276929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30343976614664863352738477 11378991230499323757276929)
        ·
          refine ⟨8534243422874492817957697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11378991230499323757276929 8534243422874492817957697)
          ·
            refine ⟨6400682567155869613468273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8534243422874492817957697 6400682567155869613468273)
            ·
              refine ⟨4800511925366902210101205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6400682567155869613468273 4800511925366902210101205)
              ·
                refine ⟨112511998250786770549247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4800511925366902210101205 112511998250786770549247)
                ·
                  rfl

theorem cell23_5916141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 7].length) (baseStart_5916141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916141 prefixEnd_5916141 := by exact prefixLift 5916141
  have htrace : WordTrace (prefixWord ++ tailWord_5916141) baseStart_5916141 baseEnd_5916141 := by
    simpa [prefixWord, tailWord_5916141, baseEnd_5916141] using wordTrace_append hprefix tailTrace_5916141
  have hstable : (prefixWord ++ tailWord_5916141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916141).length < 2 ^ (prefixWord ++ tailWord_5916141).sum := by decide
  have hdescent : baseEnd_5916141 < baseStart_5916141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916177 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_5916177 : Nat := 118140960795 + 5916177 * 2 ^ 59
def prefixEnd_5916177 : Nat := 4983230072969 + 3 ^ 40 * 5916177 * 2
def baseEnd_5916177 : Nat := 3037842438074804663979503

theorem tailTrace_5916177 : CollatzResearch.WordTrace tailWord_5916177 prefixEnd_5916177 3037842438074804663979503 := by
  unfold tailWord_5916177
  simp only [CollatzResearch.WordTrace]
  refine ⟨215780702287708606434450785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143853801525139070956300523 215780702287708606434450785)
  ·
    refine ⟨161835526715781454825838089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215780702287708606434450785 161835526715781454825838089)
    ·
      refine ⟨121376645036836091119378567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161835526715781454825838089 121376645036836091119378567)
      ·
        refine ⟨182064967555254136679067851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121376645036836091119378567 182064967555254136679067851)
        ·
          refine ⟨273097451332881205018601777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182064967555254136679067851 273097451332881205018601777)
          ·
            refine ⟨204823088499660903763951333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273097451332881205018601777 204823088499660903763951333)
            ·
              refine ⟨38404329093686419455740875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204823088499660903763951333 38404329093686419455740875)
              ·
                refine ⟨57606493640529629183611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38404329093686419455740875 57606493640529629183611313)
                ·
                  refine ⟨43204870230397221887708485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57606493640529629183611313 43204870230397221887708485)
                  ·
                    refine ⟨8100913168199479103945341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43204870230397221887708485 8100913168199479103945341)
                    ·
                      refine ⟨3037842438074804663979503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8100913168199479103945341 3037842438074804663979503)
                      ·
                        rfl

theorem cell23_5916177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_5916177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916177 prefixEnd_5916177 := by exact prefixLift 5916177
  have htrace : WordTrace (prefixWord ++ tailWord_5916177) baseStart_5916177 baseEnd_5916177 := by
    simpa [prefixWord, tailWord_5916177, baseEnd_5916177] using wordTrace_append hprefix tailTrace_5916177
  have hstable : (prefixWord ++ tailWord_5916177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916177).length < 2 ^ (prefixWord ++ tailWord_5916177).sum := by decide
  have hdescent : baseEnd_5916177 < baseStart_5916177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916195 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 1, 3, 2]
def baseStart_5916195 : Nat := 118140960795 + 5916195 * 2 ^ 59
def prefixEnd_5916195 : Nat := 4983230072969 + 3 ^ 40 * 5916195 * 2
def baseEnd_5916195 : Nat := 3037851680726585593554421

theorem tailTrace_5916195 : CollatzResearch.WordTrace tailWord_5916195 prefixEnd_5916195 3037851680726585593554421 := by
  unfold tailWord_5916195
  simp only [CollatzResearch.WordTrace]
  refine ⟨215781358801643395508606039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143854239201095597005737359 215781358801643395508606039)
  ·
    refine ⟨323672038202465093262909059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215781358801643395508606039 323672038202465093262909059)
    ·
      refine ⟨485508057303697639894363589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323672038202465093262909059 485508057303697639894363589)
      ·
        refine ⟨91032760744443307480193173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 485508057303697639894363589 91032760744443307480193173)
        ·
          refine ⟨4267160659895780038134055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91032760744443307480193173 4267160659895780038134055)
          ·
            refine ⟨6400740989843670057201083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267160659895780038134055 6400740989843670057201083)
            ·
              refine ⟨9601111484765505085801625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400740989843670057201083 9601111484765505085801625)
              ·
                refine ⟨7200833613574128814351219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9601111484765505085801625 7200833613574128814351219)
                ·
                  refine ⟨10801250420361193221526829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200833613574128814351219 10801250420361193221526829)
                  ·
                    refine ⟨4050468907635447458072561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10801250420361193221526829 4050468907635447458072561)
                    ·
                      refine ⟨3037851680726585593554421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050468907635447458072561 3037851680726585593554421)
                      ·
                        rfl

theorem cell23_5916195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_5916195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916195 prefixEnd_5916195 := by exact prefixLift 5916195
  have htrace : WordTrace (prefixWord ++ tailWord_5916195) baseStart_5916195 baseEnd_5916195 := by
    simpa [prefixWord, tailWord_5916195, baseEnd_5916195] using wordTrace_append hprefix tailTrace_5916195
  have hstable : (prefixWord ++ tailWord_5916195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916195).length < 2 ^ (prefixWord ++ tailWord_5916195).sum := by decide
  have hdescent : baseEnd_5916195 < baseStart_5916195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916231 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 5]
def baseStart_5916231 : Nat := 118140960795 + 5916231 * 2 ^ 59
def prefixEnd_5916231 : Nat := 4983230072969 + 3 ^ 40 * 5916231 * 2
def baseEnd_5916231 : Nat := 337541129558905272522695

theorem tailTrace_5916231 : CollatzResearch.WordTrace tailWord_5916231 prefixEnd_5916231 337541129558905272522695 := by
  unfold tailWord_5916231
  simp only [CollatzResearch.WordTrace]
  refine ⟨215782671829512973656916547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143855114553008649104611031 215782671829512973656916547)
  ·
    refine ⟨323674007744269460485374821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215782671829512973656916547 323674007744269460485374821)
    ·
      refine ⟨60688876452050523841007779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323674007744269460485374821 60688876452050523841007779)
      ·
        refine ⟨91033314678075785761511669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60688876452050523841007779 91033314678075785761511669)
        ·
          refine ⟨8534373251069604915141719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91033314678075785761511669 8534373251069604915141719)
          ·
            refine ⟨12801559876604407372712579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8534373251069604915141719 12801559876604407372712579)
            ·
              refine ⟨19202339814906611059068869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12801559876604407372712579 19202339814906611059068869)
              ·
                refine ⟨3600438715294989573575413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19202339814906611059068869 3600438715294989573575413)
                ·
                  refine ⟨337541129558905272522695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600438715294989573575413 337541129558905272522695)
                  ·
                    rfl

theorem cell23_5916231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 5].length) (baseStart_5916231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916231 prefixEnd_5916231 := by exact prefixLift 5916231
  have htrace : WordTrace (prefixWord ++ tailWord_5916231) baseStart_5916231 baseEnd_5916231 := by
    simpa [prefixWord, tailWord_5916231, baseEnd_5916231] using wordTrace_append hprefix tailTrace_5916231
  have hstable : (prefixWord ++ tailWord_5916231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916231).length < 2 ^ (prefixWord ++ tailWord_5916231).sum := by decide
  have hdescent : baseEnd_5916231 < baseStart_5916231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916234 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_5916234 : Nat := 118140960795 + 5916234 * 2 ^ 59
def prefixEnd_5916234 : Nat := 4983230072969 + 3 ^ 40 * 5916234 * 2
def baseEnd_5916234 : Nat := 3037871706472110940966741

theorem tailTrace_5916234 : CollatzResearch.WordTrace tailWord_5916234 prefixEnd_5916234 3037871706472110940966741 := by
  unfold tailWord_5916234
  simp only [CollatzResearch.WordTrace]
  refine ⟨53945695312125526292318939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143855187499001403446183837 53945695312125526292318939)
  ·
    refine ⟨80918542968188289438478409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53945695312125526292318939 80918542968188289438478409)
    ·
      refine ⟨60688907226141217078858807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80918542968188289438478409 60688907226141217078858807)
      ·
        refine ⟨91033360839211825618288211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60688907226141217078858807 91033360839211825618288211)
        ·
          refine ⟨136550041258817738427432317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91033360839211825618288211 136550041258817738427432317)
          ·
            refine ⟨51206265472056651910287119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136550041258817738427432317 51206265472056651910287119)
            ·
              refine ⟨76809398208084977865430679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51206265472056651910287119 76809398208084977865430679)
              ·
                refine ⟨115214097312127466798146019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76809398208084977865430679 115214097312127466798146019)
                ·
                  refine ⟨172821145968191200197219029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115214097312127466798146019 172821145968191200197219029)
                  ·
                    refine ⟨4050495608629481254622321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 172821145968191200197219029 4050495608629481254622321)
                    ·
                      refine ⟨3037871706472110940966741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050495608629481254622321 3037871706472110940966741)
                      ·
                        rfl

theorem cell23_5916234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_5916234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916234 prefixEnd_5916234 := by exact prefixLift 5916234
  have htrace : WordTrace (prefixWord ++ tailWord_5916234) baseStart_5916234 baseEnd_5916234 := by
    simpa [prefixWord, tailWord_5916234, baseEnd_5916234] using wordTrace_append hprefix tailTrace_5916234
  have hstable : (prefixWord ++ tailWord_5916234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916234).length < 2 ^ (prefixWord ++ tailWord_5916234).sum := by decide
  have hdescent : baseEnd_5916234 < baseStart_5916234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916261 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_5916261 : Nat := 118140960795 + 5916261 * 2 ^ 59
def prefixEnd_5916261 : Nat := 4983230072969 + 3 ^ 40 * 5916261 * 2
def baseEnd_5916261 : Nat := 1012628523483260778443039

theorem tailTrace_5916261 : CollatzResearch.WordTrace tailWord_5916261 prefixEnd_5916261 1012628523483260778443039 := by
  unfold tailWord_5916261
  simp only [CollatzResearch.WordTrace]
  refine ⟨215783766019404288780508637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143855844012936192520339091 215783766019404288780508637)
  ·
    refine ⟨80918912257276608292690739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215783766019404288780508637 80918912257276608292690739)
    ·
      refine ⟨121378368385914912439036109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80918912257276608292690739 121378368385914912439036109)
      ·
        refine ⟨45516888144718092164638541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121378368385914912439036109 45516888144718092164638541)
        ·
          refine ⟨17068833054269284561739453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45516888144718092164638541 17068833054269284561739453)
          ·
            refine ⟨6400812395350981710652295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17068833054269284561739453 6400812395350981710652295)
            ·
              refine ⟨9601218593026472565978443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400812395350981710652295 9601218593026472565978443)
              ·
                refine ⟨14401827889539708848967665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601218593026472565978443 14401827889539708848967665)
                ·
                  refine ⟨10801370917154781636725749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14401827889539708848967665 10801370917154781636725749)
                  ·
                    refine ⟨1012628523483260778443039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10801370917154781636725749 1012628523483260778443039)
                    ·
                      rfl

theorem cell23_5916261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_5916261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916261 prefixEnd_5916261 := by exact prefixLift 5916261
  have htrace : WordTrace (prefixWord ++ tailWord_5916261) baseStart_5916261 baseEnd_5916261 := by
    simpa [prefixWord, tailWord_5916261, baseEnd_5916261] using wordTrace_append hprefix tailTrace_5916261
  have hstable : (prefixWord ++ tailWord_5916261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916261).length < 2 ^ (prefixWord ++ tailWord_5916261).sum := by decide
  have hdescent : baseEnd_5916261 < baseStart_5916261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916284 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_5916284 : Nat := 118140960795 + 5916284 * 2 ^ 59
def prefixEnd_5916284 : Nat := 4983230072969 + 3 ^ 40 * 5916284 * 2
def baseEnd_5916284 : Nat := 3037897380504835745341511

theorem tailTrace_5916284 : CollatzResearch.WordTrace tailWord_5916284 prefixEnd_5916284 3037897380504835745341511 := by
  unfold tailWord_5916284
  simp only [CollatzResearch.WordTrace]
  refine ⟨107892302449160481854297953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143856403265547309139063937 107892302449160481854297953)
  ·
    refine ⟨80919226836870361390723465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107892302449160481854297953 80919226836870361390723465)
    ·
      refine ⟨60689420127652771043042599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80919226836870361390723465 60689420127652771043042599)
      ·
        refine ⟨91034130191479156564563899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60689420127652771043042599 91034130191479156564563899)
        ·
          refine ⟨136551195287218734846845849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91034130191479156564563899 136551195287218734846845849)
          ·
            refine ⟨102413396465414051135134387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136551195287218734846845849 102413396465414051135134387)
            ·
              refine ⟨153620094698121076702701581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102413396465414051135134387 153620094698121076702701581)
              ·
                refine ⟨57607535511795403763513093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153620094698121076702701581 57607535511795403763513093)
                ·
                  refine ⟨10801412908461638205658705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57607535511795403763513093 10801412908461638205658705)
                  ·
                    refine ⟨8101059681346228654244029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10801412908461638205658705 8101059681346228654244029)
                    ·
                      refine ⟨3037897380504835745341511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101059681346228654244029 3037897380504835745341511)
                      ·
                        rfl

theorem cell23_5916284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_5916284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916284 prefixEnd_5916284 := by exact prefixLift 5916284
  have htrace : WordTrace (prefixWord ++ tailWord_5916284) baseStart_5916284 baseEnd_5916284 := by
    simpa [prefixWord, tailWord_5916284, baseEnd_5916284] using wordTrace_append hprefix tailTrace_5916284
  have hstable : (prefixWord ++ tailWord_5916284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916284).length < 2 ^ (prefixWord ++ tailWord_5916284).sum := by decide
  have hdescent : baseEnd_5916284 < baseStart_5916284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916348 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5916348 : Nat := 118140960795 + 5916348 * 2 ^ 59
def prefixEnd_5916348 : Nat := 4983230072969 + 3 ^ 40 * 5916348 * 2
def baseEnd_5916348 : Nat := 3037930243266723494941217

theorem tailTrace_5916348 : CollatzResearch.WordTrace tailWord_5916348 prefixEnd_5916348 3037930243266723494941217 := by
  unfold tailWord_5916348
  simp only [CollatzResearch.WordTrace]
  refine ⟨107893469585044551319462849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143857959446726068425950465 107893469585044551319462849)
  ·
    refine ⟨80920102188783413489597137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107893469585044551319462849 80920102188783413489597137)
    ·
      refine ⟨60690076641587560117197853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80920102188783413489597137 60690076641587560117197853)
      ·
        refine ⟨22758778740595335043949195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60690076641587560117197853 22758778740595335043949195)
        ·
          refine ⟨34138168110893002565923793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22758778740595335043949195 34138168110893002565923793)
          ·
            refine ⟨25603626083169751924442845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34138168110893002565923793 25603626083169751924442845)
            ·
              refine ⟨9601359781188656971666067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25603626083169751924442845 9601359781188656971666067)
              ·
                refine ⟨14402039671782985457499101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601359781188656971666067 14402039671782985457499101)
                ·
                  refine ⟨5400764876918619546562163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14402039671782985457499101 5400764876918619546562163)
                  ·
                    refine ⟨8101147315377929319843245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400764876918619546562163 8101147315377929319843245)
                    ·
                      refine ⟨3037930243266723494941217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101147315377929319843245 3037930243266723494941217)
                      ·
                        rfl

theorem cell23_5916348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5916348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916348 prefixEnd_5916348 := by exact prefixLift 5916348
  have htrace : WordTrace (prefixWord ++ tailWord_5916348) baseStart_5916348 baseEnd_5916348 := by
    simpa [prefixWord, tailWord_5916348, baseEnd_5916348] using wordTrace_append hprefix tailTrace_5916348
  have hstable : (prefixWord ++ tailWord_5916348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916348).length < 2 ^ (prefixWord ++ tailWord_5916348).sum := by decide
  have hdescent : baseEnd_5916348 < baseStart_5916348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916384 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_5916384 : Nat := 118140960795 + 5916384 * 2 ^ 59
def prefixEnd_5916384 : Nat := 4983230072969 + 3 ^ 40 * 5916384 * 2
def baseEnd_5916384 : Nat := 3037948728570285354091051

theorem tailTrace_5916384 : CollatzResearch.WordTrace tailWord_5916384 prefixEnd_5916384 3037948728570285354091051 := by
  unfold tailWord_5916384
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894126098979340393618103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143858834798639120524824137 107894126098979340393618103)
  ·
    refine ⟨161841189148469010590427155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107894126098979340393618103 161841189148469010590427155)
    ·
      refine ⟨242761783722703515885640733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161841189148469010590427155 242761783722703515885640733)
      ·
        refine ⟨91035668896013818457115275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242761783722703515885640733 91035668896013818457115275)
        ·
          refine ⟨136553503344020727685672913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91035668896013818457115275 136553503344020727685672913)
          ·
            refine ⟨102415127508015545764254685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136553503344020727685672913 102415127508015545764254685)
            ·
              refine ⟨38405672815505829661595507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102415127508015545764254685 38405672815505829661595507)
              ·
                refine ⟨57608509223258744492393261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38405672815505829661595507 57608509223258744492393261)
                ·
                  refine ⟨21603190958722029184647473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57608509223258744492393261 21603190958722029184647473)
                  ·
                    refine ⟨16202393219041521888485605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21603190958722029184647473 16202393219041521888485605)
                    ·
                      refine ⟨3037948728570285354091051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16202393219041521888485605 3037948728570285354091051)
                      ·
                        rfl

theorem cell23_5916384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_5916384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916384 prefixEnd_5916384 := by exact prefixLift 5916384
  have htrace : WordTrace (prefixWord ++ tailWord_5916384) baseStart_5916384 baseEnd_5916384 := by
    simpa [prefixWord, tailWord_5916384, baseEnd_5916384] using wordTrace_append hprefix tailTrace_5916384
  have hstable : (prefixWord ++ tailWord_5916384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916384).length < 2 ^ (prefixWord ++ tailWord_5916384).sum := by decide
  have hdescent : baseEnd_5916384 < baseStart_5916384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916388 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_5916388 : Nat := 118140960795 + 5916388 * 2 ^ 59
def prefixEnd_5916388 : Nat := 4983230072969 + 3 ^ 40 * 5916388 * 2
def baseEnd_5916388 : Nat := 3037950782492903338441033

theorem tailTrace_5916388 : CollatzResearch.WordTrace tailWord_5916388 prefixEnd_5916388 3037950782492903338441033 := by
  unfold tailWord_5916388
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894199044972094735190909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143858932059962792980254545 107894199044972094735190909)
  ·
    refine ⟨40460324641864535525696591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107894199044972094735190909 40460324641864535525696591)
    ·
      refine ⟨60690486962796803288544887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40460324641864535525696591 60690486962796803288544887)
      ·
        refine ⟨91035730444195204932817331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60690486962796803288544887 91035730444195204932817331)
        ·
          refine ⟨136553595666292807399225997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91035730444195204932817331 136553595666292807399225997)
          ·
            refine ⟨51207598374859802774709749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136553595666292807399225997 51207598374859802774709749)
            ·
              refine ⟨4800712347643106510129039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51207598374859802774709749 4800712347643106510129039)
              ·
                refine ⟨7201068521464659765193559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800712347643106510129039 7201068521464659765193559)
                ·
                  refine ⟨10801602782196989647790339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201068521464659765193559 10801602782196989647790339)
                  ·
                    refine ⟨16202404173295484471685509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10801602782196989647790339 16202404173295484471685509)
                    ·
                      refine ⟨3037950782492903338441033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16202404173295484471685509 3037950782492903338441033)
                      ·
                        rfl

theorem cell23_5916388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_5916388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916388 prefixEnd_5916388 := by exact prefixLift 5916388
  have htrace : WordTrace (prefixWord ++ tailWord_5916388) baseStart_5916388 baseEnd_5916388 := by
    simpa [prefixWord, tailWord_5916388, baseEnd_5916388] using wordTrace_append hprefix tailTrace_5916388
  have hstable : (prefixWord ++ tailWord_5916388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916388).length < 2 ^ (prefixWord ++ tailWord_5916388).sum := by decide
  have hdescent : baseEnd_5916388 < baseStart_5916388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916398 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_5916398 : Nat := 118140960795 + 5916398 * 2 ^ 59
def prefixEnd_5916398 : Nat := 4983230072969 + 3 ^ 40 * 5916398 * 2
def baseEnd_5916398 : Nat := 1012651972433149433105329

theorem tailTrace_5916398 : CollatzResearch.WordTrace tailWord_5916398 prefixEnd_5916398 1012651972433149433105329 := by
  unfold tailWord_5916398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973595352488495147280731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143859175213271974118830565 26973595352488495147280731)
  ·
    refine ⟨40460393028732742720921097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26973595352488495147280731 40460393028732742720921097)
    ·
      refine ⟨30345294771549557040690823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40460393028732742720921097 30345294771549557040690823)
      ·
        refine ⟨45517942157324335561036235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30345294771549557040690823 45517942157324335561036235)
        ·
          refine ⟨68276913235986503341554353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45517942157324335561036235 68276913235986503341554353)
          ·
            refine ⟨51207684926989877506165765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68276913235986503341554353 51207684926989877506165765)
            ·
              refine ⟨9601440923810602032406081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51207684926989877506165765 9601440923810602032406081)
              ·
                refine ⟨7201080692857951524304561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9601440923810602032406081 7201080692857951524304561)
                ·
                  refine ⟨5400810519643463643228421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7201080692857951524304561 5400810519643463643228421)
                  ·
                    refine ⟨1012651972433149433105329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400810519643463643228421 1012651972433149433105329)
                    ·
                      rfl

theorem cell23_5916398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_5916398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916398 prefixEnd_5916398 := by exact prefixLift 5916398
  have htrace : WordTrace (prefixWord ++ tailWord_5916398) baseStart_5916398 baseEnd_5916398 := by
    simpa [prefixWord, tailWord_5916398, baseEnd_5916398] using wordTrace_append hprefix tailTrace_5916398
  have hstable : (prefixWord ++ tailWord_5916398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916398).length < 2 ^ (prefixWord ++ tailWord_5916398).sum := by decide
  have hdescent : baseEnd_5916398 < baseStart_5916398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916418 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_5916418 : Nat := 118140960795 + 5916418 * 2 ^ 59
def prefixEnd_5916418 : Nat := 4983230072969 + 3 ^ 40 * 5916418 * 2
def baseEnd_5916418 : Nat := 3037966186912538221065895

theorem tailTrace_5916418 : CollatzResearch.WordTrace tailWord_5916418 prefixEnd_5916418 3037966186912538221065895 := by
  unfold tailWord_5916418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53947373069958876148493477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143859661519890336395982605 53947373069958876148493477)
  ·
    refine ⟨10115132450617289277842527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53947373069958876148493477 10115132450617289277842527)
    ·
      refine ⟨15172698675925933916763791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10115132450617289277842527 15172698675925933916763791)
      ·
        refine ⟨22759048013888900875145687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15172698675925933916763791 22759048013888900875145687)
        ·
          refine ⟨34138572020833351312718531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22759048013888900875145687 34138572020833351312718531)
          ·
            refine ⟨51207858031250026969077797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34138572020833351312718531 51207858031250026969077797)
            ·
              refine ⟨9601473380859380056702087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51207858031250026969077797 9601473380859380056702087)
              ·
                refine ⟨14402210071289070085053131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601473380859380056702087 14402210071289070085053131)
                ·
                  refine ⟨21603315106933605127579697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14402210071289070085053131 21603315106933605127579697)
                  ·
                    refine ⟨16202486330200203845684773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21603315106933605127579697 16202486330200203845684773)
                    ·
                      refine ⟨3037966186912538221065895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16202486330200203845684773 3037966186912538221065895)
                      ·
                        rfl

theorem cell23_5916418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_5916418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916418 prefixEnd_5916418 := by exact prefixLift 5916418
  have htrace : WordTrace (prefixWord ++ tailWord_5916418) baseStart_5916418 baseEnd_5916418 := by
    simpa [prefixWord, tailWord_5916418, baseEnd_5916418] using wordTrace_append hprefix tailTrace_5916418
  have hstable : (prefixWord ++ tailWord_5916418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916418).length < 2 ^ (prefixWord ++ tailWord_5916418).sum := by decide
  have hdescent : baseEnd_5916418 < baseStart_5916418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916421 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_5916421 : Nat := 118140960795 + 5916421 * 2 ^ 59
def prefixEnd_5916421 : Nat := 4983230072969 + 3 ^ 40 * 5916421 * 2
def baseEnd_5916421 : Nat := 3037967727354501709328381

theorem tailTrace_5916421 : CollatzResearch.WordTrace tailWord_5916421 prefixEnd_5916421 3037967727354501709328381 := by
  unfold tailWord_5916421
  simp only [CollatzResearch.WordTrace]
  refine ⟨215789601698824636106333117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143859734465883090737555411 215789601698824636106333117)
  ·
    refine ⟨80921100637059238539874919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215789601698824636106333117 80921100637059238539874919)
    ·
      refine ⟨121381650955588857809812379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80921100637059238539874919 121381650955588857809812379)
      ·
        refine ⟨182072476433383286714718569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121381650955588857809812379 182072476433383286714718569)
        ·
          refine ⟨136554357325037465036038927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182072476433383286714718569 136554357325037465036038927)
          ·
            refine ⟨204831535987556197554058391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136554357325037465036038927 204831535987556197554058391)
            ·
              refine ⟨307247303981334296331087587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204831535987556197554058391 307247303981334296331087587)
              ·
                refine ⟨460870955972001444496631381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307247303981334296331087587 460870955972001444496631381)
                ·
                  refine ⟨5400831515296891927694899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 460870955972001444496631381 5400831515296891927694899)
                  ·
                    refine ⟨8101247272945337891542349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400831515296891927694899 8101247272945337891542349)
                    ·
                      refine ⟨3037967727354501709328381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101247272945337891542349 3037967727354501709328381)
                      ·
                        rfl

theorem cell23_5916421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_5916421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916421 prefixEnd_5916421 := by exact prefixLift 5916421
  have htrace : WordTrace (prefixWord ++ tailWord_5916421) baseStart_5916421 baseEnd_5916421 := by
    simpa [prefixWord, tailWord_5916421, baseEnd_5916421] using wordTrace_append hprefix tailTrace_5916421
  have hstable : (prefixWord ++ tailWord_5916421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916421).length < 2 ^ (prefixWord ++ tailWord_5916421).sum := by decide
  have hdescent : baseEnd_5916421 < baseStart_5916421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916424 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_5916424 : Nat := 118140960795 + 5916424 * 2 ^ 59
def prefixEnd_5916424 : Nat := 4983230072969 + 3 ^ 40 * 5916424 * 2
def baseEnd_5916424 : Nat := 1012656422598821732530289

theorem tailTrace_5916424 : CollatzResearch.WordTrace tailWord_5916424 prefixEnd_5916424 1012656422598821732530289 := by
  unfold tailWord_5916424
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894855558906883809346163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143859807411875845079128217 107894855558906883809346163)
  ·
    refine ⟨161842283338360325714019245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107894855558906883809346163 161842283338360325714019245)
    ·
      refine ⟨60690856251885122142757217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161842283338360325714019245 60690856251885122142757217)
      ·
        refine ⟨45518142188913841607067913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60690856251885122142757217 45518142188913841607067913)
        ·
          refine ⟨34138606641685381205300935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45518142188913841607067913 34138606641685381205300935)
          ·
            refine ⟨51207909962528071807951403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34138606641685381205300935 51207909962528071807951403)
            ·
              refine ⟨76811864943792107711927105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51207909962528071807951403 76811864943792107711927105)
              ·
                refine ⟨57608898707844080783945329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76811864943792107711927105 57608898707844080783945329)
                ·
                  refine ⟨43206674030883060587958997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57608898707844080783945329 43206674030883060587958997)
                  ·
                    refine ⟨1012656422598821732530289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43206674030883060587958997 1012656422598821732530289)
                    ·
                      rfl

theorem cell23_5916424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_5916424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916424 prefixEnd_5916424 := by exact prefixLift 5916424
  have htrace : WordTrace (prefixWord ++ tailWord_5916424) baseStart_5916424 baseEnd_5916424 := by
    simpa [prefixWord, tailWord_5916424, baseEnd_5916424] using wordTrace_append hprefix tailTrace_5916424
  have hstable : (prefixWord ++ tailWord_5916424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916424).length < 2 ^ (prefixWord ++ tailWord_5916424).sum := by decide
  have hdescent : baseEnd_5916424 < baseStart_5916424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916436 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5916436 : Nat := 118140960795 + 5916436 * 2 ^ 59
def prefixEnd_5916436 : Nat := 4983230072969 + 3 ^ 40 * 5916436 * 2
def baseEnd_5916436 : Nat := 1012658476521439716880271

theorem tailTrace_5916436 : CollatzResearch.WordTrace tailWord_5916436 prefixEnd_5916436 1012658476521439716880271 := by
  unfold tailWord_5916436
  simp only [CollatzResearch.WordTrace]
  refine ⟨107895074396885146834064581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143860099195846862445419441 107895074396885146834064581)
  ·
    refine ⟨20230326449415965031387109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107895074396885146834064581 20230326449415965031387109)
    ·
      refine ⟨3793186209265493443385083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20230326449415965031387109 3793186209265493443385083)
      ·
        refine ⟨5689779313898240165077625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793186209265493443385083 5689779313898240165077625)
        ·
          refine ⟨4267334485423680123808219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5689779313898240165077625 4267334485423680123808219)
          ·
            refine ⟨6401001728135520185712329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267334485423680123808219 6401001728135520185712329)
            ·
              refine ⟨4800751296101640139284247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401001728135520185712329 4800751296101640139284247)
              ·
                refine ⟨7201126944152460208926371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800751296101640139284247 7201126944152460208926371)
                ·
                  refine ⟨10801690416228690313389557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201126944152460208926371 10801690416228690313389557)
                  ·
                    refine ⟨1012658476521439716880271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10801690416228690313389557 1012658476521439716880271)
                    ·
                      rfl

theorem cell23_5916436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5916436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916436 prefixEnd_5916436 := by exact prefixLift 5916436
  have htrace : WordTrace (prefixWord ++ tailWord_5916436) baseStart_5916436 baseEnd_5916436 := by
    simpa [prefixWord, tailWord_5916436, baseEnd_5916436] using wordTrace_append hprefix tailTrace_5916436
  have hstable : (prefixWord ++ tailWord_5916436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916436).length < 2 ^ (prefixWord ++ tailWord_5916436).sum := by decide
  have hdescent : baseEnd_5916436 < baseStart_5916436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916464 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_5916464 : Nat := 118140960795 + 5916464 * 2 ^ 59
def prefixEnd_5916464 : Nat := 4983230072969 + 3 ^ 40 * 5916464 * 2
def baseEnd_5916464 : Nat := 3037989807022645041090683

theorem tailTrace_5916464 : CollatzResearch.WordTrace tailWord_5916464 prefixEnd_5916464 3037989807022645041090683 := by
  unfold tailWord_5916464
  simp only [CollatzResearch.WordTrace]
  refine ⟨107895585018834427225074223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143860780025112569633432297 107895585018834427225074223)
  ·
    refine ⟨161843377528251640837611335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107895585018834427225074223 161843377528251640837611335)
    ·
      refine ⟨242765066292377461256417003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161843377528251640837611335 242765066292377461256417003)
      ·
        refine ⟨364147599438566191884625505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242765066292377461256417003 364147599438566191884625505)
        ·
          refine ⟨273110699578924643913469129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364147599438566191884625505 273110699578924643913469129)
          ·
            refine ⟨204833024684193482935101847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273110699578924643913469129 204833024684193482935101847)
            ·
              refine ⟨307249537026290224402652771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204833024684193482935101847 307249537026290224402652771)
              ·
                refine ⟨460874305539435336603979157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307249537026290224402652771 460874305539435336603979157)
                ·
                  refine ⟨21603483072161031403311523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 460874305539435336603979157 21603483072161031403311523)
                  ·
                    refine ⟨32405224608241547104967285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21603483072161031403311523 32405224608241547104967285)
                    ·
                      refine ⟨3037989807022645041090683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32405224608241547104967285 3037989807022645041090683)
                      ·
                        rfl

theorem cell23_5916464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_5916464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916464 prefixEnd_5916464 := by exact prefixLift 5916464
  have htrace : WordTrace (prefixWord ++ tailWord_5916464) baseStart_5916464 baseEnd_5916464 := by
    simpa [prefixWord, tailWord_5916464, baseEnd_5916464] using wordTrace_append hprefix tailTrace_5916464
  have hstable : (prefixWord ++ tailWord_5916464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916464).length < 2 ^ (prefixWord ++ tailWord_5916464).sum := by decide
  have hdescent : baseEnd_5916464 < baseStart_5916464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916504 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5916504 : Nat := 118140960795 + 5916504 * 2 ^ 59
def prefixEnd_5916504 : Nat := 4983230072969 + 3 ^ 40 * 5916504 * 2
def baseEnd_5916504 : Nat := 3038010346248824884590499

theorem tailTrace_5916504 : CollatzResearch.WordTrace tailWord_5916504 prefixEnd_5916504 3038010346248824884590499 := by
  unfold tailWord_5916504
  simp only [CollatzResearch.WordTrace]
  refine ⟨107896314478761970640802283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143861752638349294187736377 107896314478761970640802283)
  ·
    refine ⟨161844471718142955961203425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107896314478761970640802283 161844471718142955961203425)
    ·
      refine ⟨121383353788607216970902569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161844471718142955961203425 121383353788607216970902569)
      ·
        refine ⟨91037515341455412728176927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121383353788607216970902569 91037515341455412728176927)
        ·
          refine ⟨136556273012183119092265391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91037515341455412728176927 136556273012183119092265391)
          ·
            refine ⟨204834409518274678638398087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136556273012183119092265391 204834409518274678638398087)
            ·
              refine ⟨307251614277412017957597131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204834409518274678638398087 307251614277412017957597131)
              ·
                refine ⟨460877421416118026936395697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307251614277412017957597131 460877421416118026936395697)
                ·
                  refine ⟨345658066062088520202296773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460877421416118026936395697 345658066062088520202296773)
                  ·
                    refine ⟨64810887386641597537930645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345658066062088520202296773 64810887386641597537930645)
                    ·
                      refine ⟨3038010346248824884590499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64810887386641597537930645 3038010346248824884590499)
                      ·
                        rfl

theorem cell23_5916504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5916504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916504 prefixEnd_5916504 := by exact prefixLift 5916504
  have htrace : WordTrace (prefixWord ++ tailWord_5916504) baseStart_5916504 baseEnd_5916504 := by
    simpa [prefixWord, tailWord_5916504, baseEnd_5916504] using wordTrace_append hprefix tailTrace_5916504
  have hstable : (prefixWord ++ tailWord_5916504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916504).length < 2 ^ (prefixWord ++ tailWord_5916504).sum := by decide
  have hdescent : baseEnd_5916504 < baseStart_5916504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916591 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 6]
def baseStart_5916591 : Nat := 118140960795 + 5916591 * 2 ^ 59
def prefixEnd_5916591 : Nat := 4983230072969 + 3 ^ 40 * 5916591 * 2
def baseEnd_5916591 : Nat := 337561668785085116022511

theorem tailTrace_5916591 : CollatzResearch.WordTrace tailWord_5916591 prefixEnd_5916591 337561668785085116022511 := by
  unfold tailWord_5916591
  simp only [CollatzResearch.WordTrace]
  refine ⟨215795802108208755140021627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143863868072139170093347751 215795802108208755140021627)
  ·
    refine ⟨323693703162313132710032441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215795802108208755140021627 323693703162313132710032441)
    ·
      refine ⟨242770277371734849532524331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323693703162313132710032441 242770277371734849532524331)
      ·
        refine ⟨364155416057602274298786497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242770277371734849532524331 364155416057602274298786497)
        ·
          refine ⟨273116562043201705724089873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364155416057602274298786497 273116562043201705724089873)
          ·
            refine ⟨204837421532401279293067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273116562043201705724089873 204837421532401279293067405)
            ·
              refine ⟨76814033074650479734900277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204837421532401279293067405 76814033074650479734900277)
              ·
                refine ⟨7201315600748482475146901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76814033074650479734900277 7201315600748482475146901)
                ·
                  refine ⟨337561668785085116022511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7201315600748482475146901 337561668785085116022511)
                  ·
                    rfl

theorem cell23_5916591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 6].length) (baseStart_5916591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916591 prefixEnd_5916591 := by exact prefixLift 5916591
  have htrace : WordTrace (prefixWord ++ tailWord_5916591) baseStart_5916591 baseEnd_5916591 := by
    simpa [prefixWord, tailWord_5916591, baseEnd_5916591] using wordTrace_append hprefix tailTrace_5916591
  have hstable : (prefixWord ++ tailWord_5916591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916591).length < 2 ^ (prefixWord ++ tailWord_5916591).sum := by decide
  have hdescent : baseEnd_5916591 < baseStart_5916591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916605 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5916605 : Nat := 118140960795 + 5916605 * 2 ^ 59
def prefixEnd_5916605 : Nat := 4983230072969 + 3 ^ 40 * 5916605 * 2
def baseEnd_5916605 : Nat := 3038062207794928989427535

theorem tailTrace_5916605 : CollatzResearch.WordTrace tailWord_5916605 prefixEnd_5916605 3038062207794928989427535 := by
  unfold tailWord_5916605
  simp only [CollatzResearch.WordTrace]
  refine ⟨215796312730158035531031269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143864208486772023687354179 215796312730158035531031269)
  ·
    refine ⟨40461808636904631662068363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215796312730158035531031269 40461808636904631662068363)
    ·
      refine ⟨60692712955356947493102545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40461808636904631662068363 60692712955356947493102545)
      ·
        refine ⟨45519534716517710619826909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60692712955356947493102545 45519534716517710619826909)
        ·
          refine ⟨17069825518694141482435091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45519534716517710619826909 17069825518694141482435091)
          ·
            refine ⟨25604738278041212223652637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17069825518694141482435091 25604738278041212223652637)
            ·
              refine ⟨9601776854265454583869739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25604738278041212223652637 9601776854265454583869739)
              ·
                refine ⟨14402665281398181875804609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601776854265454583869739 14402665281398181875804609)
                ·
                  refine ⟨10801998961048636406853457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14402665281398181875804609 10801998961048636406853457)
                  ·
                    refine ⟨8101499220786477305140093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10801998961048636406853457 8101499220786477305140093)
                    ·
                      refine ⟨3038062207794928989427535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101499220786477305140093 3038062207794928989427535)
                      ·
                        rfl

theorem cell23_5916605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5916605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916605 prefixEnd_5916605 := by exact prefixLift 5916605
  have htrace : WordTrace (prefixWord ++ tailWord_5916605) baseStart_5916605 baseEnd_5916605 := by
    simpa [prefixWord, tailWord_5916605, baseEnd_5916605] using wordTrace_append hprefix tailTrace_5916605
  have hstable : (prefixWord ++ tailWord_5916605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916605).length < 2 ^ (prefixWord ++ tailWord_5916605).sum := by decide
  have hdescent : baseEnd_5916605 < baseStart_5916605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916668 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_5916668 : Nat := 118140960795 + 5916668 * 2 ^ 59
def prefixEnd_5916668 : Nat := 4983230072969 + 3 ^ 40 * 5916668 * 2
def baseEnd_5916668 : Nat := 1012698185692054080979915

theorem tailTrace_5916668 : CollatzResearch.WordTrace tailWord_5916668 prefixEnd_5916668 1012698185692054080979915 := by
  unfold tailWord_5916668
  simp only [CollatzResearch.WordTrace]
  refine ⟨107899305264464898645287329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143865740352619864860383105 107899305264464898645287329)
  ·
    refine ⟨80924478948348673983965497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107899305264464898645287329 80924478948348673983965497)
    ·
      refine ⟨60693359211261505487974123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80924478948348673983965497 60693359211261505487974123)
      ·
        refine ⟨91040038816892258231961185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60693359211261505487974123 91040038816892258231961185)
        ·
          refine ⟨68280029112669193673970889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91040038816892258231961185 68280029112669193673970889)
          ·
            refine ⟨51210021834501895255478167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68280029112669193673970889 51210021834501895255478167)
            ·
              refine ⟨76815032751752842883217251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51210021834501895255478167 76815032751752842883217251)
              ·
                refine ⟨115222549127629264324825877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76815032751752842883217251 115222549127629264324825877)
                ·
                  refine ⟨5401056990357621765226213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115222549127629264324825877 5401056990357621765226213)
                  ·
                    refine ⟨1012698185692054080979915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401056990357621765226213 1012698185692054080979915)
                    ·
                      rfl

theorem cell23_5916668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_5916668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916668 prefixEnd_5916668 := by exact prefixLift 5916668
  have htrace : WordTrace (prefixWord ++ tailWord_5916668) baseStart_5916668 baseEnd_5916668 := by
    simpa [prefixWord, tailWord_5916668, baseEnd_5916668] using wordTrace_append hprefix tailTrace_5916668
  have hstable : (prefixWord ++ tailWord_5916668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916668).length < 2 ^ (prefixWord ++ tailWord_5916668).sum := by decide
  have hdescent : baseEnd_5916668 < baseStart_5916668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916675 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 5, 2, 2]
def baseStart_5916675 : Nat := 118140960795 + 5916675 * 2 ^ 59
def prefixEnd_5916675 : Nat := 4983230072969 + 3 ^ 40 * 5916675 * 2
def baseEnd_5916675 : Nat := 3038098151440743715552213

theorem tailTrace_5916675 : CollatzResearch.WordTrace tailWord_5916675 prefixEnd_5916675 3038098151440743715552213 := by
  unfold tailWord_5916675
  simp only [CollatzResearch.WordTrace]
  refine ⟨215798865839904437486079479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143865910559936291657386319 215798865839904437486079479)
  ·
    refine ⟨323698298759856656229119219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215798865839904437486079479 323698298759856656229119219)
    ·
      refine ⟨485547448139784984343678829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323698298759856656229119219 485547448139784984343678829)
      ·
        refine ⟨182080293052419369128879561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485547448139784984343678829 182080293052419369128879561)
        ·
          refine ⟨136560219789314526846659671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182080293052419369128879561 136560219789314526846659671)
          ·
            refine ⟨204840329683971790269989507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136560219789314526846659671 204840329683971790269989507)
            ·
              refine ⟨307260494525957685404984261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204840329683971790269989507 307260494525957685404984261)
              ·
                refine ⟨57611342723617066013434549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307260494525957685404984261 57611342723617066013434549)
                ·
                  refine ⟨5401063380339099938759489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57611342723617066013434549 5401063380339099938759489)
                  ·
                    refine ⟨4050797535254324954069617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401063380339099938759489 4050797535254324954069617)
                    ·
                      refine ⟨3038098151440743715552213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050797535254324954069617 3038098151440743715552213)
                      ·
                        rfl

theorem cell23_5916675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_5916675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916675 prefixEnd_5916675 := by exact prefixLift 5916675
  have htrace : WordTrace (prefixWord ++ tailWord_5916675) baseStart_5916675 baseEnd_5916675 := by
    simpa [prefixWord, tailWord_5916675, baseEnd_5916675] using wordTrace_append hprefix tailTrace_5916675
  have hstable : (prefixWord ++ tailWord_5916675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916675).length < 2 ^ (prefixWord ++ tailWord_5916675).sum := by decide
  have hdescent : baseEnd_5916675 < baseStart_5916675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916698 : List Nat := [3, 1, 1, 3, 1, 4, 2, 8]
def baseStart_5916698 : Nat := 118140960795 + 5916698 * 2 ^ 59
def prefixEnd_5916698 : Nat := 4983230072969 + 3 ^ 40 * 5916698 * 2
def baseEnd_5916698 : Nat := 112522591166511004650541

theorem tailTrace_5916698 : CollatzResearch.WordTrace tailWord_5916698 prefixEnd_5916698 112522591166511004650541 := by
  unfold tailWord_5916698
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949926179705278103541687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143866469812547408276111165 53949926179705278103541687)
  ·
    refine ⟨80924889269557917155312531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53949926179705278103541687 80924889269557917155312531)
    ·
      refine ⟨121387333904336875732968797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80924889269557917155312531 121387333904336875732968797)
      ·
        refine ⟨45520250214126328399863299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121387333904336875732968797 45520250214126328399863299)
        ·
          refine ⟨68280375321189492599794949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45520250214126328399863299 68280375321189492599794949)
          ·
            refine ⟨12802570372723029862461553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68280375321189492599794949 12802570372723029862461553)
            ·
              refine ⟨9601927779542272396846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12802570372723029862461553 9601927779542272396846165)
              ·
                refine ⟨112522591166511004650541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9601927779542272396846165 112522591166511004650541)
                ·
                  rfl

theorem cell23_5916698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_5916698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916698 prefixEnd_5916698 := by exact prefixLift 5916698
  have htrace : WordTrace (prefixWord ++ tailWord_5916698) baseStart_5916698 baseEnd_5916698 := by
    simpa [prefixWord, tailWord_5916698, baseEnd_5916698] using wordTrace_append hprefix tailTrace_5916698
  have hstable : (prefixWord ++ tailWord_5916698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916698).length < 2 ^ (prefixWord ++ tailWord_5916698).sum := by decide
  have hdescent : baseEnd_5916698 < baseStart_5916698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916725 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_5916725 : Nat := 118140960795 + 5916725 * 2 ^ 59
def prefixEnd_5916725 : Nat := 4983230072969 + 3 ^ 40 * 5916725 * 2
def baseEnd_5916725 : Nat := 3038123825473468519926983

theorem tailTrace_5916725 : CollatzResearch.WordTrace tailWord_5916725 prefixEnd_5916725 3038123825473468519926983 := by
  unfold tailWord_5916725
  simp only [CollatzResearch.WordTrace]
  refine ⟨215800689489723296025399629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143867126326482197350266419 215800689489723296025399629)
  ·
    refine ⟨80925258558646236009524861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215800689489723296025399629 80925258558646236009524861)
    ·
      refine ⟨30346971959492338503571823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80925258558646236009524861 30346971959492338503571823)
      ·
        refine ⟨45520457939238507755357735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30346971959492338503571823 45520457939238507755357735)
        ·
          refine ⟨68280686908857761633036603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45520457939238507755357735 68280686908857761633036603)
          ·
            refine ⟨102421030363286642449554905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68280686908857761633036603 102421030363286642449554905)
            ·
              refine ⟨76815772772464981837166179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102421030363286642449554905 76815772772464981837166179)
              ·
                refine ⟨115223659158697472755749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76815772772464981837166179 115223659158697472755749269)
                ·
                  refine ⟨5401109023063944035425747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115223659158697472755749269 5401109023063944035425747)
                  ·
                    refine ⟨8101663534595916053138621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401109023063944035425747 8101663534595916053138621)
                    ·
                      refine ⟨3038123825473468519926983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101663534595916053138621 3038123825473468519926983)
                      ·
                        rfl

theorem cell23_5916725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_5916725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916725 prefixEnd_5916725 := by exact prefixLift 5916725
  have htrace : WordTrace (prefixWord ++ tailWord_5916725) baseStart_5916725 baseEnd_5916725 := by
    simpa [prefixWord, tailWord_5916725, baseEnd_5916725] using wordTrace_append hprefix tailTrace_5916725
  have hstable : (prefixWord ++ tailWord_5916725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916725).length < 2 ^ (prefixWord ++ tailWord_5916725).sum := by decide
  have hdescent : baseEnd_5916725 < baseStart_5916725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916726 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_5916726 : Nat := 118140960795 + 5916726 * 2 ^ 59
def prefixEnd_5916726 : Nat := 4983230072969 + 3 ^ 40 * 5916726 * 2
def baseEnd_5916726 : Nat := 3038124338954123016014479

theorem tailTrace_5916726 : CollatzResearch.WordTrace tailWord_5916726 prefixEnd_5916726 3038124338954123016014479 := by
  unfold tailWord_5916726
  simp only [CollatzResearch.WordTrace]
  refine ⟨13487545372669979574761627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143867150641813115464124021 13487545372669979574761627)
  ·
    refine ⟨20231318059004969362142441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13487545372669979574761627 20231318059004969362142441)
    ·
      refine ⟨15173488544253727021606831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20231318059004969362142441 15173488544253727021606831)
      ·
        refine ⟨22760232816380590532410247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15173488544253727021606831 22760232816380590532410247)
        ·
          refine ⟨34140349224570885798615371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22760232816380590532410247 34140349224570885798615371)
          ·
            refine ⟨51210523836856328697923057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34140349224570885798615371 51210523836856328697923057)
            ·
              refine ⟨38407892877642246523442293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51210523836856328697923057 38407892877642246523442293)
              ·
                refine ⟨3600739957278960611572715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38407892877642246523442293 3600739957278960611572715)
                ·
                  refine ⟨5401109935918440917359073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600739957278960611572715 5401109935918440917359073)
                  ·
                    refine ⟨4050832451938830688019305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401109935918440917359073 4050832451938830688019305)
                    ·
                      refine ⟨3038124338954123016014479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050832451938830688019305 3038124338954123016014479)
                      ·
                        rfl

theorem cell23_5916726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_5916726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916726 prefixEnd_5916726 := by exact prefixLift 5916726
  have htrace : WordTrace (prefixWord ++ tailWord_5916726) baseStart_5916726 baseEnd_5916726 := by
    simpa [prefixWord, tailWord_5916726, baseEnd_5916726] using wordTrace_append hprefix tailTrace_5916726
  have hstable : (prefixWord ++ tailWord_5916726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916726).length < 2 ^ (prefixWord ++ tailWord_5916726).sum := by decide
  have hdescent : baseEnd_5916726 < baseStart_5916726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916729 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5916729 : Nat := 118140960795 + 5916729 * 2 ^ 59
def prefixEnd_5916729 : Nat := 4983230072969 + 3 ^ 40 * 5916729 * 2
def baseEnd_5916729 : Nat := 3038125879396086504276965

theorem tailTrace_5916729 : CollatzResearch.WordTrace tailWord_5916729 prefixEnd_5916729 3038125879396086504276965 := by
  unfold tailWord_5916729
  simp only [CollatzResearch.WordTrace]
  refine ⟨215800835381708804708545241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143867223587805869805696827 215800835381708804708545241)
  ·
    refine ⟨161850626536281603531408931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215800835381708804708545241 161850626536281603531408931)
    ·
      refine ⟨242775939804422405297113397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161850626536281603531408931 242775939804422405297113397)
      ·
        refine ⟨22760244356664600496604381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242775939804422405297113397 22760244356664600496604381)
        ·
          refine ⟨8535091633749225186226643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22760244356664600496604381 8535091633749225186226643)
          ·
            refine ⟨12802637450623837779339965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535091633749225186226643 12802637450623837779339965)
            ·
              refine ⟨4800989043983939167252487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12802637450623837779339965 4800989043983939167252487)
              ·
                refine ⟨7201483565975908750878731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800989043983939167252487 7201483565975908750878731)
                ·
                  refine ⟨10802225348963863126318097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201483565975908750878731 10802225348963863126318097)
                  ·
                    refine ⟨8101669011722897344738573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10802225348963863126318097 8101669011722897344738573)
                    ·
                      refine ⟨3038125879396086504276965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101669011722897344738573 3038125879396086504276965)
                      ·
                        rfl

theorem cell23_5916729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5916729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916729 prefixEnd_5916729 := by exact prefixLift 5916729
  have htrace : WordTrace (prefixWord ++ tailWord_5916729) baseStart_5916729 baseEnd_5916729 := by
    simpa [prefixWord, tailWord_5916729, baseEnd_5916729] using wordTrace_append hprefix tailTrace_5916729
  have hstable : (prefixWord ++ tailWord_5916729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916729).length < 2 ^ (prefixWord ++ tailWord_5916729).sum := by decide
  have hdescent : baseEnd_5916729 < baseStart_5916729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916731 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8]
def baseStart_5916731 : Nat := 118140960795 + 5916731 * 2 ^ 59
def prefixEnd_5916731 : Nat := 4983230072969 + 3 ^ 40 * 5916731 * 2
def baseEnd_5916731 : Nat := 3038126906357395496451955

theorem tailTrace_5916731 : CollatzResearch.WordTrace tailWord_5916731 prefixEnd_5916731 3038126906357395496451955 := by
  unfold tailWord_5916731
  simp only [CollatzResearch.WordTrace]
  refine ⟨215800908327701559050118047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143867272218467706033412031 215800908327701559050118047)
  ·
    refine ⟨323701362491552338575177071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215800908327701559050118047 323701362491552338575177071)
    ·
      refine ⟨485552043737328507862765607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323701362491552338575177071 485552043737328507862765607)
      ·
        refine ⟨728328065605992761794148411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485552043737328507862765607 728328065605992761794148411)
        ·
          refine ⟨1092492098408989142691222617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728328065605992761794148411 1092492098408989142691222617)
          ·
            refine ⟨819369073806741857018416963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092492098408989142691222617 819369073806741857018416963)
            ·
              refine ⟨1229053610710112785527625445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819369073806741857018416963 1229053610710112785527625445)
              ·
                refine ⟨230447552008146147286429771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1229053610710112785527625445 230447552008146147286429771)
                ·
                  refine ⟨345671328012219220929644657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230447552008146147286429771 345671328012219220929644657)
                  ·
                    refine ⟨259253496009164415697233493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345671328012219220929644657 259253496009164415697233493)
                    ·
                      refine ⟨3038126906357395496451955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 259253496009164415697233493 3038126906357395496451955)
                      ·
                        rfl

theorem cell23_5916731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_5916731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916731 prefixEnd_5916731 := by exact prefixLift 5916731
  have htrace : WordTrace (prefixWord ++ tailWord_5916731) baseStart_5916731 baseEnd_5916731 := by
    simpa [prefixWord, tailWord_5916731, baseEnd_5916731] using wordTrace_append hprefix tailTrace_5916731
  have hstable : (prefixWord ++ tailWord_5916731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916731).length < 2 ^ (prefixWord ++ tailWord_5916731).sum := by decide
  have hdescent : baseEnd_5916731 < baseStart_5916731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916742 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5916742 : Nat := 118140960795 + 5916742 * 2 ^ 59
def prefixEnd_5916742 : Nat := 4983230072969 + 3 ^ 40 * 5916742 * 2
def baseEnd_5916742 : Nat := 3038132554644594953414405

theorem tailTrace_5916742 : CollatzResearch.WordTrace tailWord_5916742 prefixEnd_5916742 3038132554644594953414405 := by
  unfold tailWord_5916742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743790922833178372774015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143867539687107805285845653 6743790922833178372774015)
  ·
    refine ⟨10115686384249767559161023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6743790922833178372774015 10115686384249767559161023)
    ·
      refine ⟨15173529576374651338741535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10115686384249767559161023 15173529576374651338741535)
      ·
        refine ⟨22760294364561977008112303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15173529576374651338741535 22760294364561977008112303)
        ·
          refine ⟨34140441546842965512168455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22760294364561977008112303 34140441546842965512168455)
          ·
            refine ⟨51210662320264448268252683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34140441546842965512168455 51210662320264448268252683)
            ·
              refine ⟨76815993480396672402379025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51210662320264448268252683 76815993480396672402379025)
              ·
                refine ⟨57611995110297504301784269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76815993480396672402379025 57611995110297504301784269)
                ·
                  refine ⟨21604498166361564113169101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57611995110297504301784269 21604498166361564113169101)
                  ·
                    refine ⟨8101686812385586542438413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21604498166361564113169101 8101686812385586542438413)
                    ·
                      refine ⟨3038132554644594953414405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101686812385586542438413 3038132554644594953414405)
                      ·
                        rfl

theorem cell23_5916742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5916742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916742 prefixEnd_5916742 := by exact prefixLift 5916742
  have htrace : WordTrace (prefixWord ++ tailWord_5916742) baseStart_5916742 baseEnd_5916742 := by
    simpa [prefixWord, tailWord_5916742, baseEnd_5916742] using wordTrace_append hprefix tailTrace_5916742
  have hstable : (prefixWord ++ tailWord_5916742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916742).length < 2 ^ (prefixWord ++ tailWord_5916742).sum := by decide
  have hdescent : baseEnd_5916742 < baseStart_5916742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916748 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5916748 : Nat := 118140960795 + 5916748 * 2 ^ 59
def prefixEnd_5916748 : Nat := 4983230072969 + 3 ^ 40 * 5916748 * 2
def baseEnd_5916748 : Nat := 3038135635528521929939377

theorem tailTrace_5916748 : CollatzResearch.WordTrace tailWord_5916748 prefixEnd_5916748 3038135635528521929939377 := by
  unfold tailWord_5916748
  simp only [CollatzResearch.WordTrace]
  refine ⟨107900764184319985476743449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143867685579093313968991265 107900764184319985476743449)
  ·
    refine ⟨80925573138239989107557587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107900764184319985476743449 80925573138239989107557587)
    ·
      refine ⟨121388359707359983661336381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80925573138239989107557587 121388359707359983661336381)
      ·
        refine ⟨45520634890259993873001143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121388359707359983661336381 45520634890259993873001143)
        ·
          refine ⟨68280952335389990809501715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45520634890259993873001143 68280952335389990809501715)
          ·
            refine ⟨102421428503084986214252573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68280952335389990809501715 102421428503084986214252573)
            ·
              refine ⟨38408035688656869830344715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102421428503084986214252573 38408035688656869830344715)
              ·
                refine ⟨57612053532985304745517073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38408035688656869830344715 57612053532985304745517073)
                ·
                  refine ⟨43209040149738978559137805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57612053532985304745517073 43209040149738978559137805)
                  ·
                    refine ⟨16203390056152116959676677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43209040149738978559137805 16203390056152116959676677)
                    ·
                      refine ⟨3038135635528521929939377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16203390056152116959676677 3038135635528521929939377)
                      ·
                        rfl

theorem cell23_5916748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5916748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916748 prefixEnd_5916748 := by exact prefixLift 5916748
  have htrace : WordTrace (prefixWord ++ tailWord_5916748) baseStart_5916748 baseEnd_5916748 := by
    simpa [prefixWord, tailWord_5916748, baseEnd_5916748] using wordTrace_append hprefix tailTrace_5916748
  have hstable : (prefixWord ++ tailWord_5916748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916748).length < 2 ^ (prefixWord ++ tailWord_5916748).sum := by decide
  have hdescent : baseEnd_5916748 < baseStart_5916748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916782 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_5916782 : Nat := 118140960795 + 5916782 * 2 ^ 59
def prefixEnd_5916782 : Nat := 4983230072969 + 3 ^ 40 * 5916782 * 2
def baseEnd_5916782 : Nat := 3038153093870774796914221

theorem tailTrace_5916782 : CollatzResearch.WordTrace tailWord_5916782 prefixEnd_5916782 3038153093870774796914221 := by
  unfold tailWord_5916782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26975346056314599345028075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143868512300344529840149733 26975346056314599345028075)
  ·
    refine ⟨40463019084471899017542113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26975346056314599345028075 40463019084471899017542113)
    ·
      refine ⟨30347264313353924263156585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40463019084471899017542113 30347264313353924263156585)
      ·
        refine ⟨22760448235015443197367439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30347264313353924263156585 22760448235015443197367439)
        ·
          refine ⟨34140672352523164796051159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22760448235015443197367439 34140672352523164796051159)
          ·
            refine ⟨51211008528784747194076739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34140672352523164796051159 51211008528784747194076739)
            ·
              refine ⟨76816512793177120791115109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51211008528784747194076739 76816512793177120791115109)
              ·
                refine ⟨14403096148720710148334083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76816512793177120791115109 14403096148720710148334083)
                ·
                  refine ⟨21604644223081065222501125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14403096148720710148334083 21604644223081065222501125)
                  ·
                    refine ⟨4050870791827699729218961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21604644223081065222501125 4050870791827699729218961)
                    ·
                      refine ⟨3038153093870774796914221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050870791827699729218961 3038153093870774796914221)
                      ·
                        rfl

theorem cell23_5916782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_5916782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916782 prefixEnd_5916782 := by exact prefixLift 5916782
  have htrace : WordTrace (prefixWord ++ tailWord_5916782) baseStart_5916782 baseEnd_5916782 := by
    simpa [prefixWord, tailWord_5916782, baseEnd_5916782] using wordTrace_append hprefix tailTrace_5916782
  have hstable : (prefixWord ++ tailWord_5916782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916782).length < 2 ^ (prefixWord ++ tailWord_5916782).sum := by decide
  have hdescent : baseEnd_5916782 < baseStart_5916782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916786 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_5916786 : Nat := 118140960795 + 5916786 * 2 ^ 59
def prefixEnd_5916786 : Nat := 4983230072969 + 3 ^ 40 * 5916786 * 2
def baseEnd_5916786 : Nat := 3038155147793392781264203

theorem tailTrace_5916786 : CollatzResearch.WordTrace tailWord_5916786 prefixEnd_5916786 3038155147793392781264203 := by
  unfold tailWord_5916786
  simp only [CollatzResearch.WordTrace]
  refine ⟨53950728585625575860842553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143868609561668202295580141 53950728585625575860842553)
  ·
    refine ⟨40463046439219181895631915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53950728585625575860842553 40463046439219181895631915)
    ·
      refine ⟨60694569658828772843447873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40463046439219181895631915 60694569658828772843447873)
      ·
        refine ⟨45520927244121579632585905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60694569658828772843447873 45520927244121579632585905)
        ·
          refine ⟨34140695433091184724439429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45520927244121579632585905 34140695433091184724439429)
          ·
            refine ⟨6401380393704597135832393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34140695433091184724439429 6401380393704597135832393)
            ·
              refine ⟨4801035295278447851874295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401380393704597135832393 4801035295278447851874295)
              ·
                refine ⟨7201552942917671777811443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801035295278447851874295 7201552942917671777811443)
                ·
                  refine ⟨10802329414376507666717165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201552942917671777811443 10802329414376507666717165)
                  ·
                    refine ⟨4050873530391190375018937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10802329414376507666717165 4050873530391190375018937)
                    ·
                      refine ⟨3038155147793392781264203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050873530391190375018937 3038155147793392781264203)
                      ·
                        rfl

theorem cell23_5916786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_5916786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916786 prefixEnd_5916786 := by exact prefixLift 5916786
  have htrace : WordTrace (prefixWord ++ tailWord_5916786) baseStart_5916786 baseEnd_5916786 := by
    simpa [prefixWord, tailWord_5916786, baseEnd_5916786] using wordTrace_append hprefix tailTrace_5916786
  have hstable : (prefixWord ++ tailWord_5916786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916786).length < 2 ^ (prefixWord ++ tailWord_5916786).sum := by decide
  have hdescent : baseEnd_5916786 < baseStart_5916786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916805 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 7]
def baseStart_5916805 : Nat := 118140960795 + 5916805 * 2 ^ 59
def prefixEnd_5916805 : Nat := 4983230072969 + 3 ^ 40 * 5916805 * 2
def baseEnd_5916805 : Nat := 337573878213980911880735

theorem tailTrace_5916805 : CollatzResearch.WordTrace tailWord_5916805 prefixEnd_5916805 337573878213980911880735 := by
  unfold tailWord_5916805
  simp only [CollatzResearch.WordTrace]
  refine ⟨215803607329433469688311869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143869071552955646458874579 215803607329433469688311869)
  ·
    refine ⟨80926352748537551133116951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215803607329433469688311869 80926352748537551133116951)
    ·
      refine ⟨121389529122806326699675427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80926352748537551133116951 121389529122806326699675427)
      ·
        refine ⟨182084293684209490049513141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121389529122806326699675427 182084293684209490049513141)
        ·
          refine ⟨17070402532894639692141857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182084293684209490049513141 17070402532894639692141857)
          ·
            refine ⟨12802801899670979769106393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17070402532894639692141857 12802801899670979769106393)
            ·
              refine ⟨9602101424753234826829795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12802801899670979769106393 9602101424753234826829795)
              ·
                refine ⟨14403152137129852240244693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9602101424753234826829795 14403152137129852240244693)
                ·
                  refine ⟨337573878213980911880735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14403152137129852240244693 337573878213980911880735)
                  ·
                    rfl

theorem cell23_5916805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_5916805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916805 prefixEnd_5916805 := by exact prefixLift 5916805
  have htrace : WordTrace (prefixWord ++ tailWord_5916805) baseStart_5916805 baseEnd_5916805 := by
    simpa [prefixWord, tailWord_5916805, baseEnd_5916805] using wordTrace_append hprefix tailTrace_5916805
  have hstable : (prefixWord ++ tailWord_5916805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916805).length < 2 ^ (prefixWord ++ tailWord_5916805).sum := by decide
  have hdescent : baseEnd_5916805 < baseStart_5916805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916825 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 5, 2]
def baseStart_5916825 : Nat := 118140960795 + 5916825 * 2 ^ 59
def prefixEnd_5916825 : Nat := 4983230072969 + 3 ^ 40 * 5916825 * 2
def baseEnd_5916825 : Nat := 3038175173538918128676523

theorem tailTrace_5916825 : CollatzResearch.WordTrace tailWord_5916825 prefixEnd_5916825 3038175173538918128676523 := by
  unfold tailWord_5916825
  simp only [CollatzResearch.WordTrace]
  refine ⟨215804336789361013104039929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143869557859574008736026619 215804336789361013104039929)
  ·
    refine ⟨161853252592020759828029947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215804336789361013104039929 161853252592020759828029947)
    ·
      refine ⟨242779878888031139742044921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161853252592020759828029947 242779878888031139742044921)
      ·
        refine ⟨182084909166023354806533691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242779878888031139742044921 182084909166023354806533691)
        ·
          refine ⟨273127363749035032209800537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182084909166023354806533691 273127363749035032209800537)
          ·
            refine ⟨204845522811776274157350403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273127363749035032209800537 204845522811776274157350403)
            ·
              refine ⟨307268284217664411236025605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204845522811776274157350403 307268284217664411236025605)
              ·
                refine ⟨57612803290812077106754801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307268284217664411236025605 57612803290812077106754801)
                ·
                  refine ⟨43209602468109057830066101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57612803290812077106754801 43209602468109057830066101)
                  ·
                    refine ⟨4050900231385224171568697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43209602468109057830066101 4050900231385224171568697)
                    ·
                      refine ⟨3038175173538918128676523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050900231385224171568697 3038175173538918128676523)
                      ·
                        rfl

theorem cell23_5916825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_5916825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916825 prefixEnd_5916825 := by exact prefixLift 5916825
  have htrace : WordTrace (prefixWord ++ tailWord_5916825) baseStart_5916825 baseEnd_5916825 := by
    simpa [prefixWord, tailWord_5916825, baseEnd_5916825] using wordTrace_append hprefix tailTrace_5916825
  have hstable : (prefixWord ++ tailWord_5916825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916825).length < 2 ^ (prefixWord ++ tailWord_5916825).sum := by decide
  have hdescent : baseEnd_5916825 < baseStart_5916825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916855 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_5916855 : Nat := 118140960795 + 5916855 * 2 ^ 59
def prefixEnd_5916855 : Nat := 4983230072969 + 3 ^ 40 * 5916855 * 2
def baseEnd_5916855 : Nat := 3038190577958553011301385

theorem tailTrace_5916855 : CollatzResearch.WordTrace tailWord_5916855 prefixEnd_5916855 3038190577958553011301385 := by
  unfold tailWord_5916855
  simp only [CollatzResearch.WordTrace]
  refine ⟨215805430979252328227632019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143870287319501552151754679 215805430979252328227632019)
  ·
    refine ⟨323708146468878492341448029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215805430979252328227632019 323708146468878492341448029)
    ·
      refine ⟨121390554925829434628043011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323708146468878492341448029 121390554925829434628043011)
      ·
        refine ⟨182085832388744151942064517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121390554925829434628043011 182085832388744151942064517)
        ·
          refine ⟨34141093572889528489137097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182085832388744151942064517 34141093572889528489137097)
          ·
            refine ⟨25605820179667146366852823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34141093572889528489137097 25605820179667146366852823)
            ·
              refine ⟨38408730269500719550279235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25605820179667146366852823 38408730269500719550279235)
              ·
                refine ⟨57613095404251079325418853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38408730269500719550279235 57613095404251079325418853)
                ·
                  refine ⟨10802455388297077373516035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57613095404251079325418853 10802455388297077373516035)
                  ·
                    refine ⟨16203683082445616060274053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10802455388297077373516035 16203683082445616060274053)
                    ·
                      refine ⟨3038190577958553011301385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16203683082445616060274053 3038190577958553011301385)
                      ·
                        rfl

theorem cell23_5916855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_5916855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916855 prefixEnd_5916855 := by exact prefixLift 5916855
  have htrace : WordTrace (prefixWord ++ tailWord_5916855) baseStart_5916855 baseEnd_5916855 := by
    simpa [prefixWord, tailWord_5916855, baseEnd_5916855] using wordTrace_append hprefix tailTrace_5916855
  have hstable : (prefixWord ++ tailWord_5916855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916855).length < 2 ^ (prefixWord ++ tailWord_5916855).sum := by decide
  have hdescent : baseEnd_5916855 < baseStart_5916855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916862 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_5916862 : Nat := 118140960795 + 5916862 * 2 ^ 59
def prefixEnd_5916862 : Nat := 4983230072969 + 3 ^ 40 * 5916862 * 2
def baseEnd_5916862 : Nat := 3038194172323134483913853

theorem tailTrace_5916862 : CollatzResearch.WordTrace tailWord_5916862 prefixEnd_5916862 3038194172323134483913853 := by
  unfold tailWord_5916862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26975710786278371052892105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143870457526817978948757893 26975710786278371052892105)
  ·
    refine ⟨20231783089708778289669079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26975710786278371052892105 20231783089708778289669079)
    ·
      refine ⟨30347674634563167434503619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20231783089708778289669079 30347674634563167434503619)
      ·
        refine ⟨45521511951844751151755429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30347674634563167434503619 45521511951844751151755429)
        ·
          refine ⟨8535283490970890840954143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45521511951844751151755429 8535283490970890840954143)
          ·
            refine ⟨12802925236456336261431215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535283490970890840954143 12802925236456336261431215)
            ·
              refine ⟨19204387854684504392146823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12802925236456336261431215 19204387854684504392146823)
              ·
                refine ⟨28806581782026756588220235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19204387854684504392146823 28806581782026756588220235)
                ·
                  refine ⟨43209872673040134882330353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28806581782026756588220235 43209872673040134882330353)
                  ·
                    refine ⟨32407404504780101161747765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43209872673040134882330353 32407404504780101161747765)
                    ·
                      refine ⟨3038194172323134483913853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32407404504780101161747765 3038194172323134483913853)
                      ·
                        rfl

theorem cell23_5916862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_5916862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916862 prefixEnd_5916862 := by exact prefixLift 5916862
  have htrace : WordTrace (prefixWord ++ tailWord_5916862) baseStart_5916862 baseEnd_5916862 := by
    simpa [prefixWord, tailWord_5916862, baseEnd_5916862] using wordTrace_append hprefix tailTrace_5916862
  have hstable : (prefixWord ++ tailWord_5916862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916862).length < 2 ^ (prefixWord ++ tailWord_5916862).sum := by decide
  have hdescent : baseEnd_5916862 < baseStart_5916862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916875 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3]
def baseStart_5916875 : Nat := 118140960795 + 5916875 * 2 ^ 59
def prefixEnd_5916875 : Nat := 4983230072969 + 3 ^ 40 * 5916875 * 2
def baseEnd_5916875 : Nat := 3038200847571642933051293

theorem tailTrace_5916875 : CollatzResearch.WordTrace tailWord_5916875 prefixEnd_5916875 3038200847571642933051293 := by
  unfold tailWord_5916875
  simp only [CollatzResearch.WordTrace]
  refine ⟨215806160439179871643360079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143870773626119914428906719 215806160439179871643360079)
  ·
    refine ⟨323709240658769807465040119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215806160439179871643360079 323709240658769807465040119)
    ·
      refine ⟨485563860988154711197560179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323709240658769807465040119 485563860988154711197560179)
      ·
        refine ⟨728345791482232066796340269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485563860988154711197560179 728345791482232066796340269)
        ·
          refine ⟨273129671805837025048627601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728345791482232066796340269 273129671805837025048627601)
          ·
            refine ⟨204847253854377768786470701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273129671805837025048627601 204847253854377768786470701)
            ·
              refine ⟨76817720195391663294926513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204847253854377768786470701 76817720195391663294926513)
              ·
                refine ⟨57613290146543747471194885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76817720195391663294926513 57613290146543747471194885)
                ·
                  refine ⟨10802491902476952650849041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57613290146543747471194885 10802491902476952650849041)
                  ·
                    refine ⟨8101868926857714488136781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10802491902476952650849041 8101868926857714488136781)
                    ·
                      refine ⟨3038200847571642933051293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8101868926857714488136781 3038200847571642933051293)
                      ·
                        rfl

theorem cell23_5916875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 3].length) (baseStart_5916875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916875 prefixEnd_5916875 := by exact prefixLift 5916875
  have htrace : WordTrace (prefixWord ++ tailWord_5916875) baseStart_5916875 baseEnd_5916875 := by
    simpa [prefixWord, tailWord_5916875, baseEnd_5916875] using wordTrace_append hprefix tailTrace_5916875
  have hstable : (prefixWord ++ tailWord_5916875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916875).length < 2 ^ (prefixWord ++ tailWord_5916875).sum := by decide
  have hdescent : baseEnd_5916875 < baseStart_5916875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916942 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_5916942 : Nat := 118140960795 + 5916942 * 2 ^ 59
def prefixEnd_5916942 : Nat := 4983230072969 + 3 ^ 40 * 5916942 * 2
def baseEnd_5916942 : Nat := 1012745083591831390304495

theorem tailTrace_5916942 : CollatzResearch.WordTrace tailWord_5916942 prefixEnd_5916942 1012745083591831390304495 := by
  unfold tailWord_5916942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26976075516242142760756135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143872402753291428057366053 26976075516242142760756135)
  ·
    refine ⟨40464113274363214141134203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26976075516242142760756135 40464113274363214141134203)
    ·
      refine ⟨60696169911544821211701305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40464113274363214141134203 60696169911544821211701305)
      ·
        refine ⟨45522127433658615908775979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60696169911544821211701305 45522127433658615908775979)
        ·
          refine ⟨68283191150487923863163969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45522127433658615908775979 68283191150487923863163969)
          ·
            refine ⟨51212393362865942897372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68283191150487923863163969 51212393362865942897372977)
            ·
              refine ⟨38409295022149457173029733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51212393362865942897372977 38409295022149457173029733)
              ·
                refine ⟨7201742816653023219943075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38409295022149457173029733 7201742816653023219943075)
                ·
                  refine ⟨10802614224979534829914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201742816653023219943075 10802614224979534829914613)
                  ·
                    refine ⟨1012745083591831390304495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10802614224979534829914613 1012745083591831390304495)
                    ·
                      rfl

theorem cell23_5916942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_5916942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916942 prefixEnd_5916942 := by exact prefixLift 5916942
  have htrace : WordTrace (prefixWord ++ tailWord_5916942) baseStart_5916942 baseEnd_5916942 := by
    simpa [prefixWord, tailWord_5916942, baseEnd_5916942] using wordTrace_append hprefix tailTrace_5916942
  have hstable : (prefixWord ++ tailWord_5916942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916942).length < 2 ^ (prefixWord ++ tailWord_5916942).sum := by decide
  have hdescent : baseEnd_5916942 < baseStart_5916942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916949 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_5916949 : Nat := 118140960795 + 5916949 * 2 ^ 59
def prefixEnd_5916949 : Nat := 4983230072969 + 3 ^ 40 * 5916949 * 2
def baseEnd_5916949 : Nat := 3038238845140075643525953

theorem tailTrace_5916949 : CollatzResearch.WordTrace tailWord_5916949 prefixEnd_5916949 3038238845140075643525953 := by
  unfold tailWord_5916949
  simp only [CollatzResearch.WordTrace]
  refine ⟨215808859440911782281553901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143872572960607854854369267 215808859440911782281553901)
  ·
    refine ⟨80928322290341918355582713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215808859440911782281553901 80928322290341918355582713)
    ·
      refine ⟨60696241717756438766687035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80928322290341918355582713 60696241717756438766687035)
      ·
        refine ⟨91044362576634658150030553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60696241717756438766687035 91044362576634658150030553)
        ·
          refine ⟨68283271932475993612522915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91044362576634658150030553 68283271932475993612522915)
          ·
            refine ⟨102424907898713990418784373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68283271932475993612522915 102424907898713990418784373)
            ·
              refine ⟨9602335115504436601761035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102424907898713990418784373 9602335115504436601761035)
              ·
                refine ⟨14403502673256654902641553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9602335115504436601761035 14403502673256654902641553)
                ·
                  refine ⟨10802627004942491176981165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14403502673256654902641553 10802627004942491176981165)
                  ·
                    refine ⟨4050985126853434191367937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10802627004942491176981165 4050985126853434191367937)
                    ·
                      refine ⟨3038238845140075643525953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050985126853434191367937 3038238845140075643525953)
                      ·
                        rfl

theorem cell23_5916949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_5916949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916949 prefixEnd_5916949 := by exact prefixLift 5916949
  have htrace : WordTrace (prefixWord ++ tailWord_5916949) baseStart_5916949 baseEnd_5916949 := by
    simpa [prefixWord, tailWord_5916949, baseEnd_5916949] using wordTrace_append hprefix tailTrace_5916949
  have hstable : (prefixWord ++ tailWord_5916949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916949).length < 2 ^ (prefixWord ++ tailWord_5916949).sum := by decide
  have hdescent : baseEnd_5916949 < baseStart_5916949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916955 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 6]
def baseStart_5916955 : Nat := 118140960795 + 5916955 * 2 ^ 59
def prefixEnd_5916955 : Nat := 4983230072969 + 3 ^ 40 * 5916955 * 2
def baseEnd_5916955 : Nat := 1012747308674667540016975

theorem tailTrace_5916955 : CollatzResearch.WordTrace tailWord_5916955 prefixEnd_5916955 1012747308674667540016975 := by
  unfold tailWord_5916955
  simp only [CollatzResearch.WordTrace]
  refine ⟨215809078278890045306272319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143872718852593363537514879 215809078278890045306272319)
  ·
    refine ⟨323713617418335067959408479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215809078278890045306272319 323713617418335067959408479)
    ·
      refine ⟨485570426127502601939112719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323713617418335067959408479 485570426127502601939112719)
      ·
        refine ⟨728355639191253902908669079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485570426127502601939112719 728355639191253902908669079)
        ·
          refine ⟨1092533458786880854363003619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728355639191253902908669079 1092533458786880854363003619)
          ·
            refine ⟨1638800188180321281544505429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092533458786880854363003619 1638800188180321281544505429)
            ·
              refine ⟨19204689705238140018099673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1638800188180321281544505429 19204689705238140018099673)
              ·
                refine ⟨14403517278928605013574755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19204689705238140018099673 14403517278928605013574755)
                ·
                  refine ⟨21605275918392907520362133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14403517278928605013574755 21605275918392907520362133)
                  ·
                    refine ⟨1012747308674667540016975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21605275918392907520362133 1012747308674667540016975)
                    ·
                      rfl

theorem cell23_5916955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 6].length) (baseStart_5916955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916955 prefixEnd_5916955 := by exact prefixLift 5916955
  have htrace : WordTrace (prefixWord ++ tailWord_5916955) baseStart_5916955 baseEnd_5916955 := by
    simpa [prefixWord, tailWord_5916955, baseEnd_5916955] using wordTrace_append hprefix tailTrace_5916955
  have hstable : (prefixWord ++ tailWord_5916955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916955).length < 2 ^ (prefixWord ++ tailWord_5916955).sum := by decide
  have hdescent : baseEnd_5916955 < baseStart_5916955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916959 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 1, 5]
def baseStart_5916959 : Nat := 118140960795 + 5916959 * 2 ^ 59
def prefixEnd_5916959 : Nat := 4983230072969 + 3 ^ 40 * 5916959 * 2
def baseEnd_5916959 : Nat := 1012747993315540201466969

theorem tailTrace_5916959 : CollatzResearch.WordTrace tailWord_5916959 prefixEnd_5916959 1012747993315540201466969 := by
  unfold tailWord_5916959
  simp only [CollatzResearch.WordTrace]
  refine ⟨215809224170875553989417931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143872816113917035992945287 215809224170875553989417931)
  ·
    refine ⟨323713836256313330984126897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215809224170875553989417931 323713836256313330984126897)
    ·
      refine ⟨242785377192234998238095173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323713836256313330984126897 242785377192234998238095173)
      ·
        refine ⟨45522258223544062169642845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242785377192234998238095173 45522258223544062169642845)
        ·
          refine ⟨17070846833829023313616067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45522258223544062169642845 17070846833829023313616067)
          ·
            refine ⟨25606270250743534970424101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17070846833829023313616067 25606270250743534970424101)
            ·
              refine ⟨4801175672014412806954519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25606270250743534970424101 4801175672014412806954519)
              ·
                refine ⟨7201763508021619210431779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801175672014412806954519 7201763508021619210431779)
                ·
                  refine ⟨10802645262032428815647669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201763508021619210431779 10802645262032428815647669)
                  ·
                    refine ⟨1012747993315540201466969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10802645262032428815647669 1012747993315540201466969)
                    ·
                      rfl

theorem cell23_5916959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_5916959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916959 prefixEnd_5916959 := by exact prefixLift 5916959
  have htrace : WordTrace (prefixWord ++ tailWord_5916959) baseStart_5916959 baseEnd_5916959 := by
    simpa [prefixWord, tailWord_5916959, baseEnd_5916959] using wordTrace_append hprefix tailTrace_5916959
  have hstable : (prefixWord ++ tailWord_5916959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916959).length < 2 ^ (prefixWord ++ tailWord_5916959).sum := by decide
  have hdescent : baseEnd_5916959 < baseStart_5916959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916973 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5916973 : Nat := 118140960795 + 5916973 * 2 ^ 59
def prefixEnd_5916973 : Nat := 4983230072969 + 3 ^ 40 * 5916973 * 2
def baseEnd_5916973 : Nat := 3038251168675783549625843

theorem tailTrace_5916973 : CollatzResearch.WordTrace tailWord_5916973 prefixEnd_5916973 3038251168675783549625843 := by
  unfold tailWord_5916973
  simp only [CollatzResearch.WordTrace]
  refine ⟨215809734792824834380427573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143873156528549889586951715 215809734792824834380427573)
  ·
    refine ⟨20232162636827328223165085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215809734792824834380427573 20232162636827328223165085)
    ·
      refine ⟨7587060988810248083686907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20232162636827328223165085 7587060988810248083686907)
      ·
        refine ⟨11380591483215372125530361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587060988810248083686907 11380591483215372125530361)
        ·
          refine ⟨8535443612411529094147771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11380591483215372125530361 8535443612411529094147771)
          ·
            refine ⟨12803165418617293641221657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535443612411529094147771 12803165418617293641221657)
            ·
              refine ⟨9602374063962970230916243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12803165418617293641221657 9602374063962970230916243)
              ·
                refine ⟨14403561095944455346374365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9602374063962970230916243 14403561095944455346374365)
                ·
                  refine ⟨5401335410979170754890387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14403561095944455346374365 5401335410979170754890387)
                  ·
                    refine ⟨8102003116468756132335581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401335410979170754890387 8102003116468756132335581)
                    ·
                      refine ⟨3038251168675783549625843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102003116468756132335581 3038251168675783549625843)
                      ·
                        rfl

theorem cell23_5916973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5916973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916973 prefixEnd_5916973 := by exact prefixLift 5916973
  have htrace : WordTrace (prefixWord ++ tailWord_5916973) baseStart_5916973 baseEnd_5916973 := by
    simpa [prefixWord, tailWord_5916973, baseEnd_5916973] using wordTrace_append hprefix tailTrace_5916973
  have hstable : (prefixWord ++ tailWord_5916973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916973).length < 2 ^ (prefixWord ++ tailWord_5916973).sum := by decide
  have hdescent : baseEnd_5916973 < baseStart_5916973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916975 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_5916975 : Nat := 118140960795 + 5916975 * 2 ^ 59
def prefixEnd_5916975 : Nat := 4983230072969 + 3 ^ 40 * 5916975 * 2
def baseEnd_5916975 : Nat := 3038252195637092541800833

theorem tailTrace_5916975 : CollatzResearch.WordTrace tailWord_5916975 prefixEnd_5916975 3038252195637092541800833 := by
  unfold tailWord_5916975
  simp only [CollatzResearch.WordTrace]
  refine ⟨215809807738817588722000379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143873205159211725814666919 215809807738817588722000379)
  ·
    refine ⟨323714711608226383083000569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215809807738817588722000379 323714711608226383083000569)
    ·
      refine ⟨242786033706169787312250427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323714711608226383083000569 242786033706169787312250427)
      ·
        refine ⟨364179050559254680968375641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242786033706169787312250427 364179050559254680968375641)
        ·
          refine ⟨273134287919441010726281731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364179050559254680968375641 273134287919441010726281731)
          ·
            refine ⟨409701431879161516089422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273134287919441010726281731 409701431879161516089422597)
            ·
              refine ⟨76819018477342784266766737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409701431879161516089422597 76819018477342784266766737)
              ·
                refine ⟨57614263858007088200075053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76819018477342784266766737 57614263858007088200075053)
                ·
                  refine ⟨21605348946752658075028145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57614263858007088200075053 21605348946752658075028145)
                  ·
                    refine ⟨16204011710064493556271109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21605348946752658075028145 16204011710064493556271109)
                    ·
                      refine ⟨3038252195637092541800833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16204011710064493556271109 3038252195637092541800833)
                      ·
                        rfl

theorem cell23_5916975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_5916975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916975 prefixEnd_5916975 := by exact prefixLift 5916975
  have htrace : WordTrace (prefixWord ++ tailWord_5916975) baseStart_5916975 baseEnd_5916975 := by
    simpa [prefixWord, tailWord_5916975, baseEnd_5916975] using wordTrace_append hprefix tailTrace_5916975
  have hstable : (prefixWord ++ tailWord_5916975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916975).length < 2 ^ (prefixWord ++ tailWord_5916975).sum := by decide
  have hdescent : baseEnd_5916975 < baseStart_5916975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5916999 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_5916999 : Nat := 118140960795 + 5916999 * 2 ^ 59
def prefixEnd_5916999 : Nat := 4983230072969 + 3 ^ 40 * 5916999 * 2
def baseEnd_5916999 : Nat := 3038264519172800447900723

theorem tailTrace_5916999 : CollatzResearch.WordTrace tailWord_5916999 prefixEnd_5916999 3038264519172800447900723 := by
  unfold tailWord_5916999
  simp only [CollatzResearch.WordTrace]
  refine ⟨215810683090730640820874051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143873788727153760547249367 215810683090730640820874051)
  ·
    refine ⟨323716024636095961231311077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215810683090730640820874051 323716024636095961231311077)
    ·
      refine ⟨60696754619267992730870827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323716024636095961231311077 60696754619267992730870827)
      ·
        refine ⟨91045131928901989096306241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60696754619267992730870827 91045131928901989096306241)
        ·
          refine ⟨68283848946676491822229681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91045131928901989096306241 68283848946676491822229681)
          ·
            refine ⟨51212886710007368866672261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68283848946676491822229681 51212886710007368866672261)
            ·
              refine ⟨9602416258126381662501049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51212886710007368866672261 9602416258126381662501049)
              ·
                refine ⟨7201812193594786246875787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9602416258126381662501049 7201812193594786246875787)
                ·
                  refine ⟨10802718290392179370313681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7201812193594786246875787 10802718290392179370313681)
                  ·
                    refine ⟨8102038717794134527735261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10802718290392179370313681 8102038717794134527735261)
                    ·
                      refine ⟨3038264519172800447900723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102038717794134527735261 3038264519172800447900723)
                      ·
                        rfl

theorem cell23_5916999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_5916999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5916999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5916999 prefixEnd_5916999 := by exact prefixLift 5916999
  have htrace : WordTrace (prefixWord ++ tailWord_5916999) baseStart_5916999 baseEnd_5916999 := by
    simpa [prefixWord, tailWord_5916999, baseEnd_5916999] using wordTrace_append hprefix tailTrace_5916999
  have hstable : (prefixWord ++ tailWord_5916999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5916999).length < 2 ^ (prefixWord ++ tailWord_5916999).sum := by decide
  have hdescent : baseEnd_5916999 < baseStart_5916999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5916999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917029 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_5917029 : Nat := 118140960795 + 5917029 * 2 ^ 59
def prefixEnd_5917029 : Nat := 4983230072969 + 3 ^ 40 * 5917029 * 2
def baseEnd_5917029 : Nat := 3038279923592435330525585

theorem tailTrace_5917029 : CollatzResearch.WordTrace tailWord_5917029 prefixEnd_5917029 3038279923592435330525585 := by
  unfold tailWord_5917029
  simp only [CollatzResearch.WordTrace]
  refine ⟨215811777280621955944466141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143874518187081303962977427 215811777280621955944466141)
  ·
    refine ⟨80929416480233233479174803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215811777280621955944466141 80929416480233233479174803)
    ·
      refine ⟨121394124720349850218762205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80929416480233233479174803 121394124720349850218762205)
      ·
        refine ⟨45522796770131193832035827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121394124720349850218762205 45522796770131193832035827)
        ·
          refine ⟨68284195155196790748053741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45522796770131193832035827 68284195155196790748053741)
          ·
            refine ⟨25606573183198796530520153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68284195155196790748053741 25606573183198796530520153)
            ·
              refine ⟨19204929887399097397890115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25606573183198796530520153 19204929887399097397890115)
              ·
                refine ⟨28807394831098646096835173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19204929887399097397890115 28807394831098646096835173)
                ·
                  refine ⟨5401386530830996143156595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28807394831098646096835173 5401386530830996143156595)
                  ·
                    refine ⟨8102079796246494214734893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401386530830996143156595 8102079796246494214734893)
                    ·
                      refine ⟨3038279923592435330525585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102079796246494214734893 3038279923592435330525585)
                      ·
                        rfl

theorem cell23_5917029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_5917029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917029 prefixEnd_5917029 := by exact prefixLift 5917029
  have htrace : WordTrace (prefixWord ++ tailWord_5917029) baseStart_5917029 baseEnd_5917029 := by
    simpa [prefixWord, tailWord_5917029, baseEnd_5917029] using wordTrace_append hprefix tailTrace_5917029
  have hstable : (prefixWord ++ tailWord_5917029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917029).length < 2 ^ (prefixWord ++ tailWord_5917029).sum := by decide
  have hdescent : baseEnd_5917029 < baseStart_5917029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917035 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4]
def baseStart_5917035 : Nat := 118140960795 + 5917035 * 2 ^ 59
def prefixEnd_5917035 : Nat := 4983230072969 + 3 ^ 40 * 5917035 * 2
def baseEnd_5917035 : Nat := 3038283004476362307050557

theorem tailTrace_5917035 : CollatzResearch.WordTrace tailWord_5917035 prefixEnd_5917035 3038283004476362307050557 := by
  unfold tailWord_5917035
  simp only [CollatzResearch.WordTrace]
  refine ⟨215811996118600218969184559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143874664079066812646123039 215811996118600218969184559)
  ·
    refine ⟨323717994177900328453776839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215811996118600218969184559 323717994177900328453776839)
    ·
      refine ⟨485576991266850492680665259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323717994177900328453776839 485576991266850492680665259)
      ·
        refine ⟨728365486900275739020997889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485576991266850492680665259 728365486900275739020997889)
        ·
          refine ⟨546274115175206804265748417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728365486900275739020997889 546274115175206804265748417)
          ·
            refine ⟨409705586381405103199311313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546274115175206804265748417 409705586381405103199311313)
            ·
              refine ⟨307279189786053827399483485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409705586381405103199311313 307279189786053827399483485)
              ·
                refine ⟨115229696169770185274806307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307279189786053827399483485 115229696169770185274806307)
                ·
                  refine ⟨172844544254655277912209461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115229696169770185274806307 172844544254655277912209461)
                  ·
                    refine ⟨16204176023873932304269637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172844544254655277912209461 16204176023873932304269637)
                    ·
                      refine ⟨3038283004476362307050557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16204176023873932304269637 3038283004476362307050557)
                      ·
                        rfl

theorem cell23_5917035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_5917035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917035 prefixEnd_5917035 := by exact prefixLift 5917035
  have htrace : WordTrace (prefixWord ++ tailWord_5917035) baseStart_5917035 baseEnd_5917035 := by
    simpa [prefixWord, tailWord_5917035, baseEnd_5917035] using wordTrace_append hprefix tailTrace_5917035
  have hstable : (prefixWord ++ tailWord_5917035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917035).length < 2 ^ (prefixWord ++ tailWord_5917035).sum := by decide
  have hdescent : baseEnd_5917035 < baseStart_5917035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917055 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_5917055 : Nat := 118140960795 + 5917055 * 2 ^ 59
def prefixEnd_5917055 : Nat := 4983230072969 + 3 ^ 40 * 5917055 * 2
def baseEnd_5917055 : Nat := 3038293274089452228800465

theorem tailTrace_5917055 : CollatzResearch.WordTrace tailWord_5917055 prefixEnd_5917055 3038293274089452228800465 := by
  unfold tailWord_5917055
  simp only [CollatzResearch.WordTrace]
  refine ⟨215812725578527762384912619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143875150385685174923275079 215812725578527762384912619)
  ·
    refine ⟨323719088367791643577368929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215812725578527762384912619 323719088367791643577368929)
    ·
      refine ⟨242789316275843732683026697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323719088367791643577368929 242789316275843732683026697)
      ·
        refine ⟨182091987206882799512270023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242789316275843732683026697 182091987206882799512270023)
        ·
          refine ⟨273137980810324199268405035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182091987206882799512270023 273137980810324199268405035)
          ·
            refine ⟨409706971215486298902607553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273137980810324199268405035 409706971215486298902607553)
            ·
              refine ⟨307280228411614724176955665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409706971215486298902607553 307280228411614724176955665)
              ·
                refine ⟨230460171308711043132716749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307280228411614724176955665 230460171308711043132716749)
                ·
                  refine ⟨86422564240766641174768781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230460171308711043132716749 86422564240766641174768781)
                  ·
                    refine ⟨32408461590287490440538293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86422564240766641174768781 32408461590287490440538293)
                    ·
                      refine ⟨3038293274089452228800465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32408461590287490440538293 3038293274089452228800465)
                      ·
                        rfl

theorem cell23_5917055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_5917055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917055 prefixEnd_5917055 := by exact prefixLift 5917055
  have htrace : WordTrace (prefixWord ++ tailWord_5917055) baseStart_5917055 baseEnd_5917055 := by
    simpa [prefixWord, tailWord_5917055, baseEnd_5917055] using wordTrace_append hprefix tailTrace_5917055
  have hstable : (prefixWord ++ tailWord_5917055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917055).length < 2 ^ (prefixWord ++ tailWord_5917055).sum := by decide
  have hdescent : baseEnd_5917055 < baseStart_5917055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917109 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 7]
def baseStart_5917109 : Nat := 118140960795 + 5917109 * 2 ^ 59
def prefixEnd_5917109 : Nat := 4983230072969 + 3 ^ 40 * 5917109 * 2
def baseEnd_5917109 : Nat := 337591222449421668613913

theorem tailTrace_5917109 : CollatzResearch.WordTrace tailWord_5917109 prefixEnd_5917109 337591222449421668613913 := by
  unfold tailWord_5917109
  simp only [CollatzResearch.WordTrace]
  refine ⟨215814695120332129607378381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143876463413554753071585587 215814695120332129607378381)
  ·
    refine ⟨80930510670124548602766893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215814695120332129607378381 80930510670124548602766893)
    ·
      refine ⟨30348941501296705726037585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80930510670124548602766893 30348941501296705726037585)
      ·
        refine ⟨22761706125972529294528189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30348941501296705726037585 22761706125972529294528189)
        ·
          refine ⟨8535639797239698485448071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22761706125972529294528189 8535639797239698485448071)
          ·
            refine ⟨12803459695859547728172107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535639797239698485448071 12803459695859547728172107)
            ·
              refine ⟨19205189543789321592258161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803459695859547728172107 19205189543789321592258161)
              ·
                refine ⟨14403892157841991194193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19205189543789321592258161 14403892157841991194193621)
                ·
                  refine ⟨337591222449421668613913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14403892157841991194193621 337591222449421668613913)
                  ·
                    rfl

theorem cell23_5917109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_5917109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917109 prefixEnd_5917109 := by exact prefixLift 5917109
  have htrace : WordTrace (prefixWord ++ tailWord_5917109) baseStart_5917109 baseEnd_5917109 := by
    simpa [prefixWord, tailWord_5917109, baseEnd_5917109] using wordTrace_append hprefix tailTrace_5917109
  have hstable : (prefixWord ++ tailWord_5917109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917109).length < 2 ^ (prefixWord ++ tailWord_5917109).sum := by decide
  have hdescent : baseEnd_5917109 < baseStart_5917109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917154 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5917154 : Nat := 118140960795 + 5917154 * 2 ^ 59
def prefixEnd_5917154 : Nat := 4983230072969 + 3 ^ 40 * 5917154 * 2
def baseEnd_5917154 : Nat := 3038344108674247341462511

theorem tailTrace_5917154 : CollatzResearch.WordTrace tailWord_5917154 prefixEnd_5917154 3038344108674247341462511 := by
  unfold tailWord_5917154
  simp only [CollatzResearch.WordTrace]
  refine ⟨53954084101292275573191629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143877557603446068195177677 53954084101292275573191629)
  ·
    refine ⟨20232781537984603339946861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53954084101292275573191629 20232781537984603339946861)
    ·
      refine ⟨7587293076744226252480073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20232781537984603339946861 7587293076744226252480073)
      ·
        refine ⟨5690469807558169689360055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587293076744226252480073 5690469807558169689360055)
        ·
          refine ⟨8535704711337254534040083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690469807558169689360055 8535704711337254534040083)
          ·
            refine ⟨12803557067005881801060125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535704711337254534040083 12803557067005881801060125)
            ·
              refine ⟨4801333900127205675397547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12803557067005881801060125 4801333900127205675397547)
              ·
                refine ⟨7202000850190808513096321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801333900127205675397547 7202000850190808513096321)
                ·
                  refine ⟨5401500637643106384822241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7202000850190808513096321 5401500637643106384822241)
                  ·
                    refine ⟨4051125478232329788616681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401500637643106384822241 4051125478232329788616681)
                    ·
                      refine ⟨3038344108674247341462511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051125478232329788616681 3038344108674247341462511)
                      ·
                        rfl

theorem cell23_5917154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5917154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917154 prefixEnd_5917154 := by exact prefixLift 5917154
  have htrace : WordTrace (prefixWord ++ tailWord_5917154) baseStart_5917154 baseEnd_5917154 := by
    simpa [prefixWord, tailWord_5917154, baseEnd_5917154] using wordTrace_append hprefix tailTrace_5917154
  have hstable : (prefixWord ++ tailWord_5917154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917154).length < 2 ^ (prefixWord ++ tailWord_5917154).sum := by decide
  have hdescent : baseEnd_5917154 < baseStart_5917154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917169 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_5917169 : Nat := 118140960795 + 5917169 * 2 ^ 59
def prefixEnd_5917169 : Nat := 4983230072969 + 3 ^ 40 * 5917169 * 2
def baseEnd_5917169 : Nat := 1012783936961354927591647

theorem tailTrace_5917169 : CollatzResearch.WordTrace tailWord_5917169 prefixEnd_5917169 1012783936961354927591647 := by
  unfold tailWord_5917169
  simp only [CollatzResearch.WordTrace]
  refine ⟨215816883500114759854562561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143877922333409839903041707 215816883500114759854562561)
  ·
    refine ⟨161862662625086069890921921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215816883500114759854562561 161862662625086069890921921)
    ·
      refine ⟨121396996968814552418191441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161862662625086069890921921 121396996968814552418191441)
      ·
        refine ⟨91047747726610914313643581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121396996968814552418191441 91047747726610914313643581)
        ·
          refine ⟨34142905397479092867616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91047747726610914313643581 34142905397479092867616343)
          ·
            refine ⟨51214358096218639301424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34142905397479092867616343 51214358096218639301424515)
            ·
              refine ⟨76821537144327958952136773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51214358096218639301424515 76821537144327958952136773)
              ·
                refine ⟨14404038214561492303525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76821537144327958952136773 14404038214561492303525645)
                ·
                  refine ⟨5401514330460559613822117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14404038214561492303525645 5401514330460559613822117)
                  ·
                    refine ⟨1012783936961354927591647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401514330460559613822117 1012783936961354927591647)
                    ·
                      rfl

theorem cell23_5917169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_5917169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917169 prefixEnd_5917169 := by exact prefixLift 5917169
  have htrace : WordTrace (prefixWord ++ tailWord_5917169) baseStart_5917169 baseEnd_5917169 := by
    simpa [prefixWord, tailWord_5917169, baseEnd_5917169] using wordTrace_append hprefix tailTrace_5917169
  have hstable : (prefixWord ++ tailWord_5917169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917169).length < 2 ^ (prefixWord ++ tailWord_5917169).sum := by decide
  have hdescent : baseEnd_5917169 < baseStart_5917169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917190 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5917190 : Nat := 118140960795 + 5917190 * 2 ^ 59
def prefixEnd_5917190 : Nat := 4983230072969 + 3 ^ 40 * 5917190 * 2
def baseEnd_5917190 : Nat := 1012787531325936400204115

theorem tailTrace_5917190 : CollatzResearch.WordTrace tailWord_5917190 prefixEnd_5917190 1012787531325936400204115 := by
  unfold tailWord_5917190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744301544782458763783657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143878432955359120294051349 6744301544782458763783657)
  ·
    refine ⟨5058226158586844072837743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6744301544782458763783657 5058226158586844072837743)
    ·
      refine ⟨7587339237880266109256615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058226158586844072837743 7587339237880266109256615)
      ·
        refine ⟨11381008856820399163884923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587339237880266109256615 11381008856820399163884923)
        ·
          refine ⟨17071513285230598745827385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381008856820399163884923 17071513285230598745827385)
          ·
            refine ⟨12803634963922949059370539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17071513285230598745827385 12803634963922949059370539)
            ·
              refine ⟨19205452445884423589055809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803634963922949059370539 19205452445884423589055809)
              ·
                refine ⟨14404089334413317691791857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19205452445884423589055809 14404089334413317691791857)
                ·
                  refine ⟨10803067000809988268843893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14404089334413317691791857 10803067000809988268843893)
                  ·
                    refine ⟨1012787531325936400204115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10803067000809988268843893 1012787531325936400204115)
                    ·
                      rfl

theorem cell23_5917190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5917190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917190 prefixEnd_5917190 := by exact prefixLift 5917190
  have htrace : WordTrace (prefixWord ++ tailWord_5917190) baseStart_5917190 baseEnd_5917190 := by
    simpa [prefixWord, tailWord_5917190, baseEnd_5917190] using wordTrace_append hprefix tailTrace_5917190
  have hstable : (prefixWord ++ tailWord_5917190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917190).length < 2 ^ (prefixWord ++ tailWord_5917190).sum := by decide
  have hdescent : baseEnd_5917190 < baseStart_5917190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917196 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_5917196 : Nat := 118140960795 + 5917196 * 2 ^ 59
def prefixEnd_5917196 : Nat := 4983230072969 + 3 ^ 40 * 5917196 * 2
def baseEnd_5917196 : Nat := 3038365674861736177137317

theorem tailTrace_5917196 : CollatzResearch.WordTrace tailWord_5917196 prefixEnd_5917196 3038365674861736177137317 := by
  unfold tailWord_5917196
  simp only [CollatzResearch.WordTrace]
  refine ⟨107908934135508471732897721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143878578847344628977196961 107908934135508471732897721)
  ·
    refine ⟨80931700601631353799673291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107908934135508471732897721 80931700601631353799673291)
    ·
      refine ⟨121397550902447030699509937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80931700601631353799673291 121397550902447030699509937)
      ·
        refine ⟨91048163176835273024632453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121397550902447030699509937 91048163176835273024632453)
        ·
          refine ⟨17071530595656613692118585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91048163176835273024632453 17071530595656613692118585)
          ·
            refine ⟨12803647946742460269088939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17071530595656613692118585 12803647946742460269088939)
            ·
              refine ⟨19205471920113690403633409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803647946742460269088939 19205471920113690403633409)
              ·
                refine ⟨14404103940085267802725057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19205471920113690403633409 14404103940085267802725057)
                ·
                  refine ⟨10803077955063950852043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14404103940085267802725057 10803077955063950852043793)
                  ·
                    refine ⟨8102308466297963139032845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10803077955063950852043793 8102308466297963139032845)
                    ·
                      refine ⟨3038365674861736177137317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102308466297963139032845 3038365674861736177137317)
                      ·
                        rfl

theorem cell23_5917196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_5917196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917196 prefixEnd_5917196 := by exact prefixLift 5917196
  have htrace : WordTrace (prefixWord ++ tailWord_5917196) baseStart_5917196 baseEnd_5917196 := by
    simpa [prefixWord, tailWord_5917196, baseEnd_5917196] using wordTrace_append hprefix tailTrace_5917196
  have hstable : (prefixWord ++ tailWord_5917196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917196).length < 2 ^ (prefixWord ++ tailWord_5917196).sum := by decide
  have hdescent : baseEnd_5917196 < baseStart_5917196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917203 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 1, 4]
def baseStart_5917203 : Nat := 118140960795 + 5917203 * 2 ^ 59
def prefixEnd_5917203 : Nat := 4983230072969 + 3 ^ 40 * 5917203 * 2
def baseEnd_5917203 : Nat := 1012789756408772549916595

theorem tailTrace_5917203 : CollatzResearch.WordTrace tailWord_5917203 prefixEnd_5917203 1012789756408772549916595 := by
  unfold tailWord_5917203
  simp only [CollatzResearch.WordTrace]
  refine ⟨215818123581991583661300263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143878749054661055774200175 215818123581991583661300263)
  ·
    refine ⟨323727185372987375491950395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215818123581991583661300263 323727185372987375491950395)
    ·
      refine ⟨485590778059481063237925593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323727185372987375491950395 485590778059481063237925593)
      ·
        refine ⟨364193083544610797428444195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485590778059481063237925593 364193083544610797428444195)
        ·
          refine ⟨546289625316916196142666293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364193083544610797428444195 546289625316916196142666293)
          ·
            refine ⟨51214652373460893388374965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 546289625316916196142666293 51214652373460893388374965)
            ·
              refine ⟨4801373660011958755160153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51214652373460893388374965 4801373660011958755160153)
              ·
                refine ⟨3601030245008969066370115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4801373660011958755160153 3601030245008969066370115)
                ·
                  refine ⟨5401545367513453599555173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601030245008969066370115 5401545367513453599555173)
                  ·
                    refine ⟨1012789756408772549916595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401545367513453599555173 1012789756408772549916595)
                    ·
                      rfl

theorem cell23_5917203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 4].length) (baseStart_5917203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917203 prefixEnd_5917203 := by exact prefixLift 5917203
  have htrace : WordTrace (prefixWord ++ tailWord_5917203) baseStart_5917203 baseEnd_5917203 := by
    simpa [prefixWord, tailWord_5917203, baseEnd_5917203] using wordTrace_append hprefix tailTrace_5917203
  have hstable : (prefixWord ++ tailWord_5917203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917203).length < 2 ^ (prefixWord ++ tailWord_5917203).sum := by decide
  have hdescent : baseEnd_5917203 < baseStart_5917203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917216 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 6]
def baseStart_5917216 : Nat := 118140960795 + 5917216 * 2 ^ 59
def prefixEnd_5917216 : Nat := 4983230072969 + 3 ^ 40 * 5917216 * 2
def baseEnd_5917216 : Nat := 337597327163869566543025

theorem tailTrace_5917216 : CollatzResearch.WordTrace tailWord_5917216 prefixEnd_5917216 337597327163869566543025 := by
  unfold tailWord_5917216
  simp only [CollatzResearch.WordTrace]
  refine ⟨107909298865472243440761751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143879065153962991254349001 107909298865472243440761751)
  ·
    refine ⟨161863948298208365161142627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107909298865472243440761751 161863948298208365161142627)
    ·
      refine ⟨242795922447312547741713941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161863948298208365161142627 242795922447312547741713941)
      ·
        refine ⟨11381058864717775675392841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242795922447312547741713941 11381058864717775675392841)
        ·
          refine ⟨8535794148538331756544631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11381058864717775675392841 8535794148538331756544631)
          ·
            refine ⟨12803691222807497634816947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535794148538331756544631 12803691222807497634816947)
            ·
              refine ⟨19205536834211246452225421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803691222807497634816947 19205536834211246452225421)
              ·
                refine ⟨7202076312829217419584533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19205536834211246452225421 7202076312829217419584533)
                ·
                  refine ⟨337597327163869566543025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7202076312829217419584533 337597327163869566543025)
                  ·
                    rfl

theorem cell23_5917216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_5917216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917216 prefixEnd_5917216 := by exact prefixLift 5917216
  have htrace : WordTrace (prefixWord ++ tailWord_5917216) baseStart_5917216 baseEnd_5917216 := by
    simpa [prefixWord, tailWord_5917216, baseEnd_5917216] using wordTrace_append hprefix tailTrace_5917216
  have hstable : (prefixWord ++ tailWord_5917216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917216).length < 2 ^ (prefixWord ++ tailWord_5917216).sum := by decide
  have hdescent : baseEnd_5917216 < baseStart_5917216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917254 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_5917254 : Nat := 118140960795 + 5917254 * 2 ^ 59
def prefixEnd_5917254 : Nat := 4983230072969 + 3 ^ 40 * 5917254 * 2
def baseEnd_5917254 : Nat := 1012798485579898983404017

theorem tailTrace_5917254 : CollatzResearch.WordTrace tailWord_5917254 prefixEnd_5917254 1012798485579898983404017 := by
  unfold tailWord_5917254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744374490775213105356463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143879989136537879580937877 6744374490775213105356463)
  ·
    refine ⟨10116561736162819658034695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744374490775213105356463 10116561736162819658034695)
    ·
      refine ⟨15174842604244229487052043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116561736162819658034695 15174842604244229487052043)
      ·
        refine ⟨22762263906366344230578065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15174842604244229487052043 22762263906366344230578065)
        ·
          refine ⟨17071697929774758172933549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22762263906366344230578065 17071697929774758172933549)
          ·
            refine ⟨6401886723665534314850081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17071697929774758172933549 6401886723665534314850081)
            ·
              refine ⟨4801415042749150736137561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401886723665534314850081 4801415042749150736137561)
              ·
                refine ⟨3601061282061863052103171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4801415042749150736137561 3601061282061863052103171)
                ·
                  refine ⟨5401591923092794578154757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601061282061863052103171 5401591923092794578154757)
                  ·
                    refine ⟨1012798485579898983404017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401591923092794578154757 1012798485579898983404017)
                    ·
                      rfl

theorem cell23_5917254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_5917254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917254 prefixEnd_5917254 := by exact prefixLift 5917254
  have htrace : WordTrace (prefixWord ++ tailWord_5917254) baseStart_5917254 baseEnd_5917254 := by
    simpa [prefixWord, tailWord_5917254, baseEnd_5917254] using wordTrace_append hprefix tailTrace_5917254
  have hstable : (prefixWord ++ tailWord_5917254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917254).length < 2 ^ (prefixWord ++ tailWord_5917254).sum := by decide
  have hdescent : baseEnd_5917254 < baseStart_5917254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917259 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 4, 4]
def baseStart_5917259 : Nat := 118140960795 + 5917259 * 2 ^ 59
def prefixEnd_5917259 : Nat := 4983230072969 + 3 ^ 40 * 5917259 * 2
def baseEnd_5917259 : Nat := 1012799341380989810216509

theorem tailTrace_5917259 : CollatzResearch.WordTrace tailWord_5917259 prefixEnd_5917259 1012799341380989810216509 := by
  unfold tailWord_5917259
  simp only [CollatzResearch.WordTrace]
  refine ⟨215820166069788705225338831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143880110713192470150225887 215820166069788705225338831)
  ·
    refine ⟨323730249104683057838008247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215820166069788705225338831 323730249104683057838008247)
    ·
      refine ⟨485595373657024586757012371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323730249104683057838008247 485595373657024586757012371)
      ·
        refine ⟨728393060485536880135518557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485595373657024586757012371 728393060485536880135518557)
        ·
          refine ⟨273147397682076330050819459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728393060485536880135518557 273147397682076330050819459)
          ·
            refine ⟨409721096523114495076229189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273147397682076330050819459 409721096523114495076229189)
            ·
              refine ⟨76822705598083967826792973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409721096523114495076229189 76822705598083967826792973)
              ·
                refine ⟨28808514599281487935047365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76822705598083967826792973 28808514599281487935047365)
                ·
                  refine ⟨5401596487365278987821381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28808514599281487935047365 5401596487365278987821381)
                  ·
                    refine ⟨1012799341380989810216509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401596487365278987821381 1012799341380989810216509)
                    ·
                      rfl

theorem cell23_5917259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 4].length) (baseStart_5917259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917259 prefixEnd_5917259 := by exact prefixLift 5917259
  have htrace : WordTrace (prefixWord ++ tailWord_5917259) baseStart_5917259 baseEnd_5917259 := by
    simpa [prefixWord, tailWord_5917259, baseEnd_5917259] using wordTrace_append hprefix tailTrace_5917259
  have hstable : (prefixWord ++ tailWord_5917259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917259).length < 2 ^ (prefixWord ++ tailWord_5917259).sum := by decide
  have hdescent : baseEnd_5917259 < baseStart_5917259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917269 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5917269 : Nat := 118140960795 + 5917269 * 2 ^ 59
def prefixEnd_5917269 : Nat := 4983230072969 + 3 ^ 40 * 5917269 * 2
def baseEnd_5917269 : Nat := 3038403158949514391524481

theorem tailTrace_5917269 : CollatzResearch.WordTrace tailWord_5917269 prefixEnd_5917269 3038403158949514391524481 := by
  unfold tailWord_5917269
  simp only [CollatzResearch.WordTrace]
  refine ⟨215820530799752476933202861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143880353866501651288801907 215820530799752476933202861)
  ·
    refine ⟨80932699049907178849951073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215820530799752476933202861 80932699049907178849951073)
    ·
      refine ⟨60699524287430384137463305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80932699049907178849951073 60699524287430384137463305)
      ·
        refine ⟨45524643215572788103097479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60699524287430384137463305 45524643215572788103097479)
        ·
          refine ⟨68286964823359182154646219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45524643215572788103097479 68286964823359182154646219)
          ·
            refine ⟨102430447235038773231969329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68286964823359182154646219 102430447235038773231969329)
            ·
              refine ⟨76822835426279079923976997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102430447235038773231969329 76822835426279079923976997)
              ·
                refine ⟨14404281642427327485745687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76822835426279079923976997 14404281642427327485745687)
                ·
                  refine ⟨21606422463640991228618531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14404281642427327485745687 21606422463640991228618531)
                  ·
                    refine ⟨32409633695461486842927797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21606422463640991228618531 32409633695461486842927797)
                    ·
                      refine ⟨3038403158949514391524481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32409633695461486842927797 3038403158949514391524481)
                      ·
                        rfl

theorem cell23_5917269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5917269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917269 prefixEnd_5917269 := by exact prefixLift 5917269
  have htrace : WordTrace (prefixWord ++ tailWord_5917269) baseStart_5917269 baseEnd_5917269 := by
    simpa [prefixWord, tailWord_5917269, baseEnd_5917269] using wordTrace_append hprefix tailTrace_5917269
  have hstable : (prefixWord ++ tailWord_5917269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917269).length < 2 ^ (prefixWord ++ tailWord_5917269).sum := by decide
  have hdescent : baseEnd_5917269 < baseStart_5917269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917283 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 3, 2, 2]
def baseStart_5917283 : Nat := 118140960795 + 5917283 * 2 ^ 59
def prefixEnd_5917283 : Nat := 4983230072969 + 3 ^ 40 * 5917283 * 2
def baseEnd_5917283 : Nat := 3038410347678677336749417

theorem tailTrace_5917283 : CollatzResearch.WordTrace tailWord_5917283 prefixEnd_5917283 3038410347678677336749417 := by
  unfold tailWord_5917283
  simp only [CollatzResearch.WordTrace]
  refine ⟨215821041421701757324212503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143880694281134504882808335 215821041421701757324212503)
  ·
    refine ⟨323731562132552635986318755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215821041421701757324212503 323731562132552635986318755)
    ·
      refine ⟨485597343198828953979478133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323731562132552635986318755 485597343198828953979478133)
      ·
        refine ⟨45524750924890214435576075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 485597343198828953979478133 45524750924890214435576075)
        ·
          refine ⟨68287126387335321653364113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45524750924890214435576075 68287126387335321653364113)
          ·
            refine ⟨51215344790501491240023085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68287126387335321653364113 51215344790501491240023085)
            ·
              refine ⟨19205754296438059215008657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51215344790501491240023085 19205754296438059215008657)
              ·
                refine ⟨14404315722328544411256493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19205754296438059215008657 14404315722328544411256493)
                ·
                  refine ⟨5401618395873204154221185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14404315722328544411256493 5401618395873204154221185)
                  ·
                    refine ⟨4051213796904903115665889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401618395873204154221185 4051213796904903115665889)
                    ·
                      refine ⟨3038410347678677336749417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051213796904903115665889 3038410347678677336749417)
                      ·
                        rfl

theorem cell23_5917283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_5917283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917283 prefixEnd_5917283 := by exact prefixLift 5917283
  have htrace : WordTrace (prefixWord ++ tailWord_5917283) baseStart_5917283 baseEnd_5917283 := by
    simpa [prefixWord, tailWord_5917283, baseEnd_5917283] using wordTrace_append hprefix tailTrace_5917283
  have hstable : (prefixWord ++ tailWord_5917283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917283).length < 2 ^ (prefixWord ++ tailWord_5917283).sum := by decide
  have hdescent : baseEnd_5917283 < baseStart_5917283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917299 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3]
def baseStart_5917299 : Nat := 118140960795 + 5917299 * 2 ^ 59
def prefixEnd_5917299 : Nat := 4983230072969 + 3 ^ 40 * 5917299 * 2
def baseEnd_5917299 : Nat := 3038418563369149274149343

theorem tailTrace_5917299 : CollatzResearch.WordTrace tailWord_5917299 prefixEnd_5917299 3038418563369149274149343 := by
  unfold tailWord_5917299
  simp only [CollatzResearch.WordTrace]
  refine ⟨215821624989643792056794951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143881083326429194704529967 215821624989643792056794951)
  ·
    refine ⟨323732437484465688085192427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215821624989643792056794951 323732437484465688085192427)
    ·
      refine ⟨485598656226698532127788641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323732437484465688085192427 485598656226698532127788641)
      ·
        refine ⟨364198992170023899095841481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485598656226698532127788641 364198992170023899095841481)
        ·
          refine ⟨273149244127517924321881111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364198992170023899095841481 273149244127517924321881111)
          ·
            refine ⟨409723866191276886482821667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273149244127517924321881111 409723866191276886482821667)
            ·
              refine ⟨614585799286915329724232501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409723866191276886482821667 614585799286915329724232501)
              ·
                refine ⟨57617418683148312161646797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 614585799286915329724232501 57617418683148312161646797)
                ·
                  refine ⟨21606532006180617060617549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57617418683148312161646797 21606532006180617060617549)
                  ·
                    refine ⟨8102449502317731397731581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21606532006180617060617549 8102449502317731397731581)
                    ·
                      refine ⟨3038418563369149274149343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102449502317731397731581 3038418563369149274149343)
                      ·
                        rfl

theorem cell23_5917299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_5917299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917299 prefixEnd_5917299 := by exact prefixLift 5917299
  have htrace : WordTrace (prefixWord ++ tailWord_5917299) baseStart_5917299 baseEnd_5917299 := by
    simpa [prefixWord, tailWord_5917299, baseEnd_5917299] using wordTrace_append hprefix tailTrace_5917299
  have hstable : (prefixWord ++ tailWord_5917299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917299).length < 2 ^ (prefixWord ++ tailWord_5917299).sum := by decide
  have hdescent : baseEnd_5917299 < baseStart_5917299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917303 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 1, 2, 3]
def baseStart_5917303 : Nat := 118140960795 + 5917303 * 2 ^ 59
def prefixEnd_5917303 : Nat := 4983230072969 + 3 ^ 40 * 5917303 * 2
def baseEnd_5917303 : Nat := 3038420617291767258499325

theorem tailTrace_5917303 : CollatzResearch.WordTrace tailWord_5917303 prefixEnd_5917303 3038420617291767258499325 := by
  unfold tailWord_5917303
  simp only [CollatzResearch.WordTrace]
  refine ⟨215821770881629300739940563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143881180587752867159960375 215821770881629300739940563)
  ·
    refine ⟨323732656322443951109910845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215821770881629300739940563 323732656322443951109910845)
    ·
      refine ⟨121399746120916481666216567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323732656322443951109910845 121399746120916481666216567)
      ·
        refine ⟨182099619181374722499324851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121399746120916481666216567 182099619181374722499324851)
        ·
          refine ⟨273149428772062083748987277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182099619181374722499324851 273149428772062083748987277)
          ·
            refine ⟨102431035789523281405870229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273149428772062083748987277 102431035789523281405870229)
            ·
              refine ⟨4801454802633903815900167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102431035789523281405870229 4801454802633903815900167)
              ·
                refine ⟨7202182203950855723850251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801454802633903815900167 7202182203950855723850251)
                ·
                  refine ⟨10803273305926283585775377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202182203950855723850251 10803273305926283585775377)
                  ·
                    refine ⟨8102454979444712689331533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10803273305926283585775377 8102454979444712689331533)
                    ·
                      refine ⟨3038420617291767258499325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102454979444712689331533 3038420617291767258499325)
                      ·
                        rfl

theorem cell23_5917303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_5917303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917303 prefixEnd_5917303 := by exact prefixLift 5917303
  have htrace : WordTrace (prefixWord ++ tailWord_5917303) baseStart_5917303 baseEnd_5917303 := by
    simpa [prefixWord, tailWord_5917303, baseEnd_5917303] using wordTrace_append hprefix tailTrace_5917303
  have hstable : (prefixWord ++ tailWord_5917303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917303).length < 2 ^ (prefixWord ++ tailWord_5917303).sum := by decide
  have hdescent : baseEnd_5917303 < baseStart_5917303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917351 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5917351 : Nat := 118140960795 + 5917351 * 2 ^ 59
def prefixEnd_5917351 : Nat := 4983230072969 + 3 ^ 40 * 5917351 * 2
def baseEnd_5917351 : Nat := 3038445264363183070699105

theorem tailTrace_5917351 : CollatzResearch.WordTrace tailWord_5917351 prefixEnd_5917351 3038445264363183070699105 := by
  unfold tailWord_5917351
  simp only [CollatzResearch.WordTrace]
  refine ⟨215823521585455404937687907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143882347723636936625125271 215823521585455404937687907)
  ·
    refine ⟨323735282378183107406531861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215823521585455404937687907 323735282378183107406531861)
    ·
      refine ⟨15175091361477333159681181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 323735282378183107406531861 15175091361477333159681181)
      ·
        refine ⟨5690659260553999934880443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15175091361477333159681181 5690659260553999934880443)
        ·
          refine ⟨8535988890830999902320665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690659260553999934880443 8535988890830999902320665)
          ·
            refine ⟨6401991668123249926740499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8535988890830999902320665 6401991668123249926740499)
            ·
              refine ⟨9602987502184874890110749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401991668123249926740499 9602987502184874890110749)
              ·
                refine ⟨3601120313319328083791531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9602987502184874890110749 3601120313319328083791531)
                ·
                  refine ⟨5401680469978992125687297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601120313319328083791531 5401680469978992125687297)
                  ·
                    refine ⟨4051260352484244094265473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401680469978992125687297 4051260352484244094265473)
                    ·
                      refine ⟨3038445264363183070699105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051260352484244094265473 3038445264363183070699105)
                      ·
                        rfl

theorem cell23_5917351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5917351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917351 prefixEnd_5917351 := by exact prefixLift 5917351
  have htrace : WordTrace (prefixWord ++ tailWord_5917351) baseStart_5917351 baseEnd_5917351 := by
    simpa [prefixWord, tailWord_5917351, baseEnd_5917351] using wordTrace_append hprefix tailTrace_5917351
  have hstable : (prefixWord ++ tailWord_5917351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917351).length < 2 ^ (prefixWord ++ tailWord_5917351).sum := by decide
  have hdescent : baseEnd_5917351 < baseStart_5917351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917359 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_5917359 : Nat := 118140960795 + 5917359 * 2 ^ 59
def prefixEnd_5917359 : Nat := 4983230072969 + 3 ^ 40 * 5917359 * 2
def baseEnd_5917359 : Nat := 3038449372208419039399067

theorem tailTrace_5917359 : CollatzResearch.WordTrace tailWord_5917359 prefixEnd_5917359 3038449372208419039399067 := by
  unfold tailWord_5917359
  simp only [CollatzResearch.WordTrace]
  refine ⟨215823813369426422303979131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143882542246284281535986087 215823813369426422303979131)
  ·
    refine ⟨323735720054139633455968697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215823813369426422303979131 323735720054139633455968697)
    ·
      refine ⟨242801790040604725091976523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323735720054139633455968697 242801790040604725091976523)
      ·
        refine ⟨364202685060907087637964785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242801790040604725091976523 364202685060907087637964785)
        ·
          refine ⟨273152013795680315728473589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364202685060907087637964785 273152013795680315728473589)
          ·
            refine ⟨25608001293345029599544399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273152013795680315728473589 25608001293345029599544399)
            ·
              refine ⟨38412001940017544399316599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25608001293345029599544399 38412001940017544399316599)
              ·
                refine ⟨57618002910026316598974899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38412001940017544399316599 57618002910026316598974899)
                ·
                  refine ⟨86427004365039474898462349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57618002910026316598974899 86427004365039474898462349)
                  ·
                    refine ⟨32410126636889803086923381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86427004365039474898462349 32410126636889803086923381)
                    ·
                      refine ⟨3038449372208419039399067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32410126636889803086923381 3038449372208419039399067)
                      ·
                        rfl

theorem cell23_5917359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_5917359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917359 prefixEnd_5917359 := by exact prefixLift 5917359
  have htrace : WordTrace (prefixWord ++ tailWord_5917359) baseStart_5917359 baseEnd_5917359 := by
    simpa [prefixWord, tailWord_5917359, baseEnd_5917359] using wordTrace_append hprefix tailTrace_5917359
  have hstable : (prefixWord ++ tailWord_5917359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917359).length < 2 ^ (prefixWord ++ tailWord_5917359).sum := by decide
  have hdescent : baseEnd_5917359 < baseStart_5917359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917394 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_5917394 : Nat := 118140960795 + 5917394 * 2 ^ 59
def prefixEnd_5917394 : Nat := 4983230072969 + 3 ^ 40 * 5917394 * 2
def baseEnd_5917394 : Nat := 3038467344031326402461407

theorem tailTrace_5917394 : CollatzResearch.WordTrace tailWord_5917394 prefixEnd_5917394 3038467344031326402461407 := by
  unfold tailWord_5917394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53956272481074905820375809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143883393282866415521002157 53956272481074905820375809)
  ·
    refine ⟨40467204360806179365281857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53956272481074905820375809 40467204360806179365281857)
    ·
      refine ⟨30350403270604634523961393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40467204360806179365281857 30350403270604634523961393)
      ·
        refine ⟨22762802452953475892971045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30350403270604634523961393 22762802452953475892971045)
        ·
          refine ⟨4268025459928776729932071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22762802452953475892971045 4268025459928776729932071)
          ·
            refine ⟨6402038189893165094898107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268025459928776729932071 6402038189893165094898107)
            ·
              refine ⟨9603057284839747642347161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402038189893165094898107 9603057284839747642347161)
              ·
                refine ⟨7202292963629810731760371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9603057284839747642347161 7202292963629810731760371)
                ·
                  refine ⟨10803439445444716097640557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202292963629810731760371 10803439445444716097640557)
                  ·
                    refine ⟨4051289792041768536615209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10803439445444716097640557 4051289792041768536615209)
                    ·
                      refine ⟨3038467344031326402461407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051289792041768536615209 3038467344031326402461407)
                      ·
                        rfl

theorem cell23_5917394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_5917394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917394 prefixEnd_5917394 := by exact prefixLift 5917394
  have htrace : WordTrace (prefixWord ++ tailWord_5917394) baseStart_5917394 baseEnd_5917394 := by
    simpa [prefixWord, tailWord_5917394, baseEnd_5917394] using wordTrace_append hprefix tailTrace_5917394
  have hstable : (prefixWord ++ tailWord_5917394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917394).length < 2 ^ (prefixWord ++ tailWord_5917394).sum := by decide
  have hdescent : baseEnd_5917394 < baseStart_5917394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917436 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5917436 : Nat := 118140960795 + 5917436 * 2 ^ 59
def prefixEnd_5917436 : Nat := 4983230072969 + 3 ^ 40 * 5917436 * 2
def baseEnd_5917436 : Nat := 3038488910218815238136213

theorem tailTrace_5917436 : CollatzResearch.WordTrace tailWord_5917436 prefixEnd_5917436 3038488910218815238136213 := by
  unfold tailWord_5917436
  simp only [CollatzResearch.WordTrace]
  refine ⟨107913310895073732227266081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143884414526764976303021441 107913310895073732227266081)
  ·
    refine ⟨80934983171305299170449561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107913310895073732227266081 80934983171305299170449561)
    ·
      refine ⟨60701237378478974377837171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80934983171305299170449561 60701237378478974377837171)
      ·
        refine ⟨91051856067718461566755757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60701237378478974377837171 91051856067718461566755757)
        ·
          refine ⟨34144446025394423087533409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91051856067718461566755757 34144446025394423087533409)
          ·
            refine ⟨25608334519045817315650057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34144446025394423087533409 25608334519045817315650057)
            ·
              refine ⟨19206250889284362986737543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25608334519045817315650057 19206250889284362986737543)
              ·
                refine ⟨28809376333926544480106315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19206250889284362986737543 28809376333926544480106315)
                ·
                  refine ⟨43214064500889816720159473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28809376333926544480106315 43214064500889816720159473)
                  ·
                    refine ⟨32410548375667362540119605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43214064500889816720159473 32410548375667362540119605)
                    ·
                      refine ⟨3038488910218815238136213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32410548375667362540119605 3038488910218815238136213)
                      ·
                        rfl

theorem cell23_5917436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5917436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917436 prefixEnd_5917436 := by exact prefixLift 5917436
  have htrace : WordTrace (prefixWord ++ tailWord_5917436) baseStart_5917436 baseEnd_5917436 := by
    simpa [prefixWord, tailWord_5917436, baseEnd_5917436] using wordTrace_append hprefix tailTrace_5917436
  have hstable : (prefixWord ++ tailWord_5917436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917436).length < 2 ^ (prefixWord ++ tailWord_5917436).sum := by decide
  have hdescent : baseEnd_5917436 < baseStart_5917436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917439 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 8]
def baseStart_5917439 : Nat := 118140960795 + 5917439 * 2 ^ 59
def prefixEnd_5917439 : Nat := 4983230072969 + 3 ^ 40 * 5917439 * 2
def baseEnd_5917439 : Nat := 1012830150220259575466233

theorem tailTrace_5917439 : CollatzResearch.WordTrace tailWord_5917439 prefixEnd_5917439 1012830150220259575466233 := by
  unfold tailWord_5917439
  simp only [CollatzResearch.WordTrace]
  refine ⟨215826731209136595966891371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143884487472757730644594247 215826731209136595966891371)
  ·
    refine ⟨323740096813704893950337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215826731209136595966891371 323740096813704893950337057)
    ·
      refine ⟨242805072610278670462752793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323740096813704893950337057 242805072610278670462752793)
      ·
        refine ⟨182103804457709002847064595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242805072610278670462752793 182103804457709002847064595)
        ·
          refine ⟨273155706686563504270596893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182103804457709002847064595 273155706686563504270596893)
          ·
            refine ⟨102433390007461314101473835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273155706686563504270596893 102433390007461314101473835)
            ·
              refine ⟨153650085011191971152210753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102433390007461314101473835 153650085011191971152210753)
              ·
                refine ⟨115237563758393978364158065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153650085011191971152210753 115237563758393978364158065)
                ·
                  refine ⟨86428172818795483773118549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115237563758393978364158065 86428172818795483773118549)
                  ·
                    refine ⟨1012830150220259575466233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86428172818795483773118549 1012830150220259575466233)
                    ·
                      rfl

theorem cell23_5917439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_5917439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917439 prefixEnd_5917439 := by exact prefixLift 5917439
  have htrace : WordTrace (prefixWord ++ tailWord_5917439) baseStart_5917439 baseEnd_5917439 := by
    simpa [prefixWord, tailWord_5917439, baseEnd_5917439] using wordTrace_append hprefix tailTrace_5917439
  have hstable : (prefixWord ++ tailWord_5917439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917439).length < 2 ^ (prefixWord ++ tailWord_5917439).sum := by decide
  have hdescent : baseEnd_5917439 < baseStart_5917439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917463 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5917463 : Nat := 118140960795 + 5917463 * 2 ^ 59
def prefixEnd_5917463 : Nat := 4983230072969 + 3 ^ 40 * 5917463 * 2
def baseEnd_5917463 : Nat := 3038502774196486632498589

theorem tailTrace_5917463 : CollatzResearch.WordTrace tailWord_5917463 prefixEnd_5917463 3038502774196486632498589 := by
  unfold tailWord_5917463
  simp only [CollatzResearch.WordTrace]
  refine ⟨215827606561049648065765043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143885071040699765377176695 215827606561049648065765043)
  ·
    refine ⟨323741409841574472098647565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215827606561049648065765043 323741409841574472098647565)
    ·
      refine ⟨121403028690590427036992837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323741409841574472098647565 121403028690590427036992837)
      ·
        refine ⟨22763067879485705069436157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121403028690590427036992837 22763067879485705069436157)
        ·
          refine ⟨8536150454807139401038559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22763067879485705069436157 8536150454807139401038559)
          ·
            refine ⟨12804225682210709101557839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536150454807139401038559 12804225682210709101557839)
            ·
              refine ⟨19206338523316063652336759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804225682210709101557839 19206338523316063652336759)
              ·
                refine ⟨28809507784974095478505139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19206338523316063652336759 28809507784974095478505139)
                ·
                  refine ⟨43214261677461143217757709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28809507784974095478505139 43214261677461143217757709)
                  ·
                    refine ⟨16205348129047928706659141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43214261677461143217757709 16205348129047928706659141)
                    ·
                      refine ⟨3038502774196486632498589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16205348129047928706659141 3038502774196486632498589)
                      ·
                        rfl

theorem cell23_5917463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5917463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917463 prefixEnd_5917463 := by exact prefixLift 5917463
  have htrace : WordTrace (prefixWord ++ tailWord_5917463) baseStart_5917463 baseEnd_5917463 := by
    simpa [prefixWord, tailWord_5917463, baseEnd_5917463] using wordTrace_append hprefix tailTrace_5917463
  have hstable : (prefixWord ++ tailWord_5917463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917463).length < 2 ^ (prefixWord ++ tailWord_5917463).sum := by decide
  have hdescent : baseEnd_5917463 < baseStart_5917463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917490 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_5917490 : Nat := 118140960795 + 5917490 * 2 ^ 59
def prefixEnd_5917490 : Nat := 4983230072969 + 3 ^ 40 * 5917490 * 2
def baseEnd_5917490 : Nat := 1012838879391386008953655

theorem tailTrace_5917490 : CollatzResearch.WordTrace tailWord_5917490 prefixEnd_5917490 1012838879391386008953655 := by
  unfold tailWord_5917490
  simp only [CollatzResearch.WordTrace]
  refine ⟨53957147832987957919249481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143885727554634554451331949 53957147832987957919249481)
  ·
    refine ⟨40467860874740968439437111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53957147832987957919249481 40467860874740968439437111)
    ·
      refine ⟨60701791312111452659155667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40467860874740968439437111 60701791312111452659155667)
      ·
        refine ⟨91052686968167178988733501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60701791312111452659155667 91052686968167178988733501)
        ·
          refine ⟨34144757613062692120775063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91052686968167178988733501 34144757613062692120775063)
          ·
            refine ⟨51217136419594038181162595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34144757613062692120775063 51217136419594038181162595)
            ·
              refine ⟨76825704629391057271743893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51217136419594038181162595 76825704629391057271743893)
              ·
                refine ⟨3601204904502705809612995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76825704629391057271743893 3601204904502705809612995)
                ·
                  refine ⟨5401807356754058714419493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601204904502705809612995 5401807356754058714419493)
                  ·
                    refine ⟨1012838879391386008953655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401807356754058714419493 1012838879391386008953655)
                    ·
                      rfl

theorem cell23_5917490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_5917490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917490 prefixEnd_5917490 := by exact prefixLift 5917490
  have htrace : WordTrace (prefixWord ++ tailWord_5917490) baseStart_5917490 baseEnd_5917490 := by
    simpa [prefixWord, tailWord_5917490, baseEnd_5917490] using wordTrace_append hprefix tailTrace_5917490
  have hstable : (prefixWord ++ tailWord_5917490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917490).length < 2 ^ (prefixWord ++ tailWord_5917490).sum := by decide
  have hdescent : baseEnd_5917490 < baseStart_5917490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917523 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 6, 3, 2]
def baseStart_5917523 : Nat := 118140960795 + 5917523 * 2 ^ 59
def prefixEnd_5917523 : Nat := 4983230072969 + 3 ^ 40 * 5917523 * 2
def baseEnd_5917523 : Nat := 3038533583035756397748313

theorem tailTrace_5917523 : CollatzResearch.WordTrace tailWord_5917523 prefixEnd_5917523 3038533583035756397748313 := by
  unfold tailWord_5917523
  simp only [CollatzResearch.WordTrace]
  refine ⟨215829794940832278312949223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143886529960554852208632815 215829794940832278312949223)
  ·
    refine ⟨323744692411248417469423835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215829794940832278312949223 323744692411248417469423835)
    ·
      refine ⟨485617038616872626204135753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323744692411248417469423835 485617038616872626204135753)
      ·
        refine ⟨364212778962654469653101815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485617038616872626204135753 364212778962654469653101815)
        ·
          refine ⟨546319168443981704479652723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364212778962654469653101815 546319168443981704479652723)
          ·
            refine ⟨819478752665972556719479085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546319168443981704479652723 819478752665972556719479085)
            ·
              refine ⟨307304532249739708769804657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819478752665972556719479085 307304532249739708769804657)
              ·
                refine ⟨230478399187304781577353493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307304532249739708769804657 230478399187304781577353493)
                ·
                  refine ⟨10803674961904911636438445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230478399187304781577353493 10803674961904911636438445)
                  ·
                    refine ⟨4051378110714341863664417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10803674961904911636438445 4051378110714341863664417)
                    ·
                      refine ⟨3038533583035756397748313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051378110714341863664417 3038533583035756397748313)
                      ·
                        rfl

theorem cell23_5917523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3, 2].length) (baseStart_5917523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917523 prefixEnd_5917523 := by exact prefixLift 5917523
  have htrace : WordTrace (prefixWord ++ tailWord_5917523) baseStart_5917523 baseEnd_5917523 := by
    simpa [prefixWord, tailWord_5917523, baseEnd_5917523] using wordTrace_append hprefix tailTrace_5917523
  have hstable : (prefixWord ++ tailWord_5917523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917523).length < 2 ^ (prefixWord ++ tailWord_5917523).sum := by decide
  have hdescent : baseEnd_5917523 < baseStart_5917523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917524 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5917524 : Nat := 118140960795 + 5917524 * 2 ^ 59
def prefixEnd_5917524 : Nat := 4983230072969 + 3 ^ 40 * 5917524 * 2
def baseEnd_5917524 : Nat := 1012844698838803631278603

theorem tailTrace_5917524 : CollatzResearch.WordTrace tailWord_5917524 prefixEnd_5917524 1012844698838803631278603 := by
  unfold tailWord_5917524
  simp only [CollatzResearch.WordTrace]
  refine ⟨107914915706914327741867813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143886554275885770322490417 107914915706914327741867813)
  ·
    refine ⟨20234046695046436451600215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107914915706914327741867813 20234046695046436451600215)
    ·
      refine ⟨30351070042569654677400323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20234046695046436451600215 30351070042569654677400323)
      ·
        refine ⟨45526605063854482016100485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30351070042569654677400323 45526605063854482016100485)
        ·
          refine ⟨8536238449472715378018841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45526605063854482016100485 8536238449472715378018841)
          ·
            refine ⟨6402178837104536533514131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536238449472715378018841 6402178837104536533514131)
            ·
              refine ⟨9603268255656804800271197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402178837104536533514131 9603268255656804800271197)
              ·
                refine ⟨3601225595871301800101699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9603268255656804800271197 3601225595871301800101699)
                ·
                  refine ⟨5401838393806952700152549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601225595871301800101699 5401838393806952700152549)
                  ·
                    refine ⟨1012844698838803631278603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5401838393806952700152549 1012844698838803631278603)
                    ·
                      rfl

theorem cell23_5917524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5917524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917524 prefixEnd_5917524 := by exact prefixLift 5917524
  have htrace : WordTrace (prefixWord ++ tailWord_5917524) baseStart_5917524 baseEnd_5917524 := by
    simpa [prefixWord, tailWord_5917524, baseEnd_5917524] using wordTrace_append hprefix tailTrace_5917524
  have hstable : (prefixWord ++ tailWord_5917524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917524).length < 2 ^ (prefixWord ++ tailWord_5917524).sum := by decide
  have hdescent : baseEnd_5917524 < baseStart_5917524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917540 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_5917540 : Nat := 118140960795 + 5917540 * 2 ^ 59
def prefixEnd_5917540 : Nat := 4983230072969 + 3 ^ 40 * 5917540 * 2
def baseEnd_5917540 : Nat := 3038542312206882831235735

theorem tailTrace_5917540 : CollatzResearch.WordTrace tailWord_5917540 prefixEnd_5917540 3038542312206882831235735 := by
  unfold tailWord_5917540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107915207490885345108159037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143886943321180460144212049 107915207490885345108159037)
  ·
    refine ⟨40468202809082004415559639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107915207490885345108159037 40468202809082004415559639)
    ·
      refine ⟨60702304213623006623339459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40468202809082004415559639 60702304213623006623339459)
      ·
        refine ⟨91053456320434509935009189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60702304213623006623339459 91053456320434509935009189)
        ·
          refine ⟨17072523060081470612814223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91053456320434509935009189 17072523060081470612814223)
          ·
            refine ⟨25608784590122205919221335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17072523060081470612814223 25608784590122205919221335)
            ·
              refine ⟨38413176885183308878832003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25608784590122205919221335 38413176885183308878832003)
              ·
                refine ⟨57619765327774963318248005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38413176885183308878832003 57619765327774963318248005)
                ·
                  refine ⟨10803705998957805622171501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57619765327774963318248005 10803705998957805622171501)
                  ·
                    refine ⟨4051389749609177108314313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10803705998957805622171501 4051389749609177108314313)
                    ·
                      refine ⟨3038542312206882831235735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051389749609177108314313 3038542312206882831235735)
                      ·
                        rfl

theorem cell23_5917540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_5917540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917540 prefixEnd_5917540 := by exact prefixLift 5917540
  have htrace : WordTrace (prefixWord ++ tailWord_5917540) baseStart_5917540 baseEnd_5917540 := by
    simpa [prefixWord, tailWord_5917540, baseEnd_5917540] using wordTrace_append hprefix tailTrace_5917540
  have hstable : (prefixWord ++ tailWord_5917540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917540).length < 2 ^ (prefixWord ++ tailWord_5917540).sum := by decide
  have hdescent : baseEnd_5917540 < baseStart_5917540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917604 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_5917604 : Nat := 118140960795 + 5917604 * 2 ^ 59
def prefixEnd_5917604 : Nat := 4983230072969 + 3 ^ 40 * 5917604 * 2
def baseEnd_5917604 : Nat := 3038575174968770580835441

theorem tailTrace_5917604 : CollatzResearch.WordTrace tailWord_5917604 prefixEnd_5917604 3038575174968770580835441 := by
  unfold tailWord_5917604
  simp only [CollatzResearch.WordTrace]
  refine ⟨107916374626769414573323933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143888499502359219431098577 107916374626769414573323933)
  ·
    refine ⟨40468640485038530464996475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107916374626769414573323933 40468640485038530464996475)
    ·
      refine ⟨60702960727557795697494713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40468640485038530464996475 60702960727557795697494713)
      ·
        refine ⟨45527220545668346773121035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60702960727557795697494713 45527220545668346773121035)
        ·
          refine ⟨68290830818502520159681553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45527220545668346773121035 68290830818502520159681553)
          ·
            refine ⟨51218123113876890119761165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68290830818502520159681553 51218123113876890119761165)
            ·
              refine ⟨19206796167703833794910437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51218123113876890119761165 19206796167703833794910437)
              ·
                refine ⟨3601274281444468836545707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19206796167703833794910437 3601274281444468836545707)
                ·
                  refine ⟨5401911422166703254818561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601274281444468836545707 5401911422166703254818561)
                  ·
                    refine ⟨4051433566625027441113921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401911422166703254818561 4051433566625027441113921)
                    ·
                      refine ⟨3038575174968770580835441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051433566625027441113921 3038575174968770580835441)
                      ·
                        rfl

theorem cell23_5917604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_5917604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917604 prefixEnd_5917604 := by exact prefixLift 5917604
  have htrace : WordTrace (prefixWord ++ tailWord_5917604) baseStart_5917604 baseEnd_5917604 := by
    simpa [prefixWord, tailWord_5917604, baseEnd_5917604] using wordTrace_append hprefix tailTrace_5917604
  have hstable : (prefixWord ++ tailWord_5917604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917604).length < 2 ^ (prefixWord ++ tailWord_5917604).sum := by decide
  have hdescent : baseEnd_5917604 < baseStart_5917604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917638 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5917638 : Nat := 118140960795 + 5917638 * 2 ^ 59
def prefixEnd_5917638 : Nat := 4983230072969 + 3 ^ 40 * 5917638 * 2
def baseEnd_5917638 : Nat := 3038592633311023447810285

theorem tailTrace_5917638 : CollatzResearch.WordTrace tailWord_5917638 prefixEnd_5917638 3038592633311023447810285 := by
  unfold tailWord_5917638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744812166731739154793299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143889326223610435302257045 6744812166731739154793299)
  ·
    refine ⟨10117218250097608732189949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744812166731739154793299 10117218250097608732189949)
    ·
      refine ⟨3793956843786603274571231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10117218250097608732189949 3793956843786603274571231)
      ·
        refine ⟨5690935265679904911856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793956843786603274571231 5690935265679904911856847)
        ·
          refine ⟨8536402898519857367785271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690935265679904911856847 8536402898519857367785271)
          ·
            refine ⟨12804604347779786051677907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536402898519857367785271 12804604347779786051677907)
            ·
              refine ⟨19206906521669679077516861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804604347779786051677907 19206906521669679077516861)
              ·
                refine ⟨7202589945626129654068823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19206906521669679077516861 7202589945626129654068823)
                ·
                  refine ⟨10803884918439194481103235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202589945626129654068823 10803884918439194481103235)
                  ·
                    refine ⟨16205827377658791721654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10803884918439194481103235 16205827377658791721654853)
                    ·
                      refine ⟨3038592633311023447810285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16205827377658791721654853 3038592633311023447810285)
                      ·
                        rfl

theorem cell23_5917638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5917638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917638 prefixEnd_5917638 := by exact prefixLift 5917638
  have htrace : WordTrace (prefixWord ++ tailWord_5917638) baseStart_5917638 baseEnd_5917638 := by
    simpa [prefixWord, tailWord_5917638, baseEnd_5917638] using wordTrace_append hprefix tailTrace_5917638
  have hstable : (prefixWord ++ tailWord_5917638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917638).length < 2 ^ (prefixWord ++ tailWord_5917638).sum := by decide
  have hdescent : baseEnd_5917638 < baseStart_5917638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917647 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 1, 3, 2]
def baseStart_5917647 : Nat := 118140960795 + 5917647 * 2 ^ 59
def prefixEnd_5917647 : Nat := 4983230072969 + 3 ^ 40 * 5917647 * 2
def baseEnd_5917647 : Nat := 3038597254636913912597743

theorem tailTrace_5917647 : CollatzResearch.WordTrace tailWord_5917647 prefixEnd_5917647 3038597254636913912597743 := by
  unfold tailWord_5917647
  simp only [CollatzResearch.WordTrace]
  refine ⟨215834317592383047490463195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143889545061588698326975463 215834317592383047490463195)
  ·
    refine ⟨323751476388574571235694793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215834317592383047490463195 323751476388574571235694793)
    ·
      refine ⟨242813607291430928426771095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323751476388574571235694793 242813607291430928426771095)
      ·
        refine ⟨364220410937146392640156643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242813607291430928426771095 364220410937146392640156643)
        ·
          refine ⟨546330616405719588960234965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364220410937146392640156643 546330616405719588960234965)
          ·
            refine ⟨12804623822009052866255507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 546330616405719588960234965 12804623822009052866255507)
            ·
              refine ⟨19206935733013579299383261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804623822009052866255507 19206935733013579299383261)
              ·
                refine ⟨7202600899880092237268723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19206935733013579299383261 7202600899880092237268723)
                ·
                  refine ⟨10803901349820138355903085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202600899880092237268723 10803901349820138355903085)
                  ·
                    refine ⟨4051463006182551883463657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10803901349820138355903085 4051463006182551883463657)
                    ·
                      refine ⟨3038597254636913912597743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051463006182551883463657 3038597254636913912597743)
                      ·
                        rfl

theorem cell23_5917647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3, 2].length) (baseStart_5917647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917647 prefixEnd_5917647 := by exact prefixLift 5917647
  have htrace : WordTrace (prefixWord ++ tailWord_5917647) baseStart_5917647 baseEnd_5917647 := by
    simpa [prefixWord, tailWord_5917647, baseEnd_5917647] using wordTrace_append hprefix tailTrace_5917647
  have hstable : (prefixWord ++ tailWord_5917647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917647).length < 2 ^ (prefixWord ++ tailWord_5917647).sum := by decide
  have hdescent : baseEnd_5917647 < baseStart_5917647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917654 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5917654 : Nat := 118140960795 + 5917654 * 2 ^ 59
def prefixEnd_5917654 : Nat := 4983230072969 + 3 ^ 40 * 5917654 * 2
def baseEnd_5917654 : Nat := 3038600849001495385210211

theorem tailTrace_5917654 : CollatzResearch.WordTrace tailWord_5917654 prefixEnd_5917654 3038600849001495385210211 := by
  unfold tailWord_5917654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489660806459855480373001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143889715268905125123978677 13489660806459855480373001)
  ·
    refine ⟨10117245604844891610279751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13489660806459855480373001 10117245604844891610279751)
    ·
      refine ⟨15175868407267337415419627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117245604844891610279751 15175868407267337415419627)
      ·
        refine ⟨22763802610901006123129441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15175868407267337415419627 22763802610901006123129441)
        ·
          refine ⟨17072851958175754592347081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22763802610901006123129441 17072851958175754592347081)
          ·
            refine ⟨12804638968631815944260311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17072851958175754592347081 12804638968631815944260311)
            ·
              refine ⟨19206958452947723916390467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804638968631815944260311 19206958452947723916390467)
              ·
                refine ⟨28810437679421585874585701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19206958452947723916390467 28810437679421585874585701)
                ·
                  refine ⟨5401957064891547351484819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28810437679421585874585701 5401957064891547351484819)
                  ·
                    refine ⟨8102935597337321027227229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401957064891547351484819 8102935597337321027227229)
                    ·
                      refine ⟨3038600849001495385210211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8102935597337321027227229 3038600849001495385210211)
                      ·
                        rfl

theorem cell23_5917654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5917654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917654 prefixEnd_5917654 := by exact prefixLift 5917654
  have htrace : WordTrace (prefixWord ++ tailWord_5917654) baseStart_5917654 baseEnd_5917654 := by
    simpa [prefixWord, tailWord_5917654, baseEnd_5917654] using wordTrace_append hprefix tailTrace_5917654
  have hstable : (prefixWord ++ tailWord_5917654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917654).length < 2 ^ (prefixWord ++ tailWord_5917654).sum := by decide
  have hdescent : baseEnd_5917654 < baseStart_5917654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917763 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_5917763 : Nat := 118140960795 + 5917763 * 2 ^ 59
def prefixEnd_5917763 : Nat := 4983230072969 + 3 ^ 40 * 5917763 * 2
def baseEnd_5917763 : Nat := 3038656818392835458747209

theorem tailTrace_5917763 : CollatzResearch.WordTrace tailWord_5917763 prefixEnd_5917763 3038656818392835458747209 := by
  unfold tailWord_5917763
  simp only [CollatzResearch.WordTrace]
  refine ⟨215838548459962799301685943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143892365639975199534457295 215838548459962799301685943)
  ·
    refine ⟨323757822689944198952528915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215838548459962799301685943 323757822689944198952528915)
    ·
      refine ⟨485636734034916298428793373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323757822689944198952528915 485636734034916298428793373)
      ·
        refine ⟨182113775263093611910797515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485636734034916298428793373 182113775263093611910797515)
        ·
          refine ⟨273170662894640417866196273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182113775263093611910797515 273170662894640417866196273)
          ·
            refine ⟨204877997170980313399647205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273170662894640417866196273 204877997170980313399647205)
            ·
              refine ⟨38414624469558808762433851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204877997170980313399647205 38414624469558808762433851)
              ·
                refine ⟨57621936704338213143650777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38414624469558808762433851 57621936704338213143650777)
                ·
                  refine ⟨43216452528253659857738083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57621936704338213143650777 43216452528253659857738083)
                  ·
                    refine ⟨64824678792380489786607125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43216452528253659857738083 64824678792380489786607125)
                    ·
                      refine ⟨3038656818392835458747209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64824678792380489786607125 3038656818392835458747209)
                      ·
                        rfl

theorem cell23_5917763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_5917763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917763 prefixEnd_5917763 := by exact prefixLift 5917763
  have htrace : WordTrace (prefixWord ++ tailWord_5917763) baseStart_5917763 baseEnd_5917763 := by
    simpa [prefixWord, tailWord_5917763, baseEnd_5917763] using wordTrace_append hprefix tailTrace_5917763
  have hstable : (prefixWord ++ tailWord_5917763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917763).length < 2 ^ (prefixWord ++ tailWord_5917763).sum := by decide
  have hdescent : baseEnd_5917763 < baseStart_5917763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917794 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5917794 : Nat := 118140960795 + 5917794 * 2 ^ 59
def prefixEnd_5917794 : Nat := 4983230072969 + 3 ^ 40 * 5917794 * 2
def baseEnd_5917794 : Nat := 1012890912097708279153189

theorem tailTrace_5917794 : CollatzResearch.WordTrace tailWord_5917794 prefixEnd_5917794 1012890912097708279153189 := by
  unfold tailWord_5917794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53959919780712622899016109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143893119415233661064042957 53959919780712622899016109)
  ·
    refine ⟨20234969917767233587131041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53959919780712622899016109 20234969917767233587131041)
    ·
      refine ⟨15176227438325425190348281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20234969917767233587131041 15176227438325425190348281)
      ·
        refine ⟨11382170578744068892761211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15176227438325425190348281 11382170578744068892761211)
        ·
          refine ⟨17073255868116103339141817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382170578744068892761211 17073255868116103339141817)
          ·
            refine ⟨12804941901087077504356363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17073255868116103339141817 12804941901087077504356363)
            ·
              refine ⟨19207412851630616256534545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804941901087077504356363 19207412851630616256534545)
              ·
                refine ⟨14405559638722962192400909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19207412851630616256534545 14405559638722962192400909)
                ·
                  refine ⟨5402084864521110822150341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14405559638722962192400909 5402084864521110822150341)
                  ·
                    refine ⟨1012890912097708279153189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402084864521110822150341 1012890912097708279153189)
                    ·
                      rfl

theorem cell23_5917794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5917794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917794 prefixEnd_5917794 := by exact prefixLift 5917794
  have htrace : WordTrace (prefixWord ++ tailWord_5917794) baseStart_5917794 baseEnd_5917794 := by
    simpa [prefixWord, tailWord_5917794, baseEnd_5917794] using wordTrace_append hprefix tailTrace_5917794
  have hstable : (prefixWord ++ tailWord_5917794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917794).length < 2 ^ (prefixWord ++ tailWord_5917794).sum := by decide
  have hdescent : baseEnd_5917794 < baseStart_5917794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917827 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 4, 3, 2]
def baseStart_5917827 : Nat := 118140960795 + 5917827 * 2 ^ 59
def prefixEnd_5917827 : Nat := 4983230072969 + 3 ^ 40 * 5917827 * 2
def baseEnd_5917827 : Nat := 3038689681154723208346915

theorem tailTrace_5917827 : CollatzResearch.WordTrace tailWord_5917827 prefixEnd_5917827 3038689681154723208346915 := by
  unfold tailWord_5917827
  simp only [CollatzResearch.WordTrace]
  refine ⟨215840882731730938232015735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143893921821153958821343823 215840882731730938232015735)
  ·
    refine ⟨323761324097596407348023603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215840882731730938232015735 323761324097596407348023603)
    ·
      refine ⟨485641986146394611022035405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323761324097596407348023603 485641986146394611022035405)
      ·
        refine ⟨182115744804897979133263277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485641986146394611022035405 182115744804897979133263277)
        ·
          refine ⟨68293404301836742174973729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182115744804897979133263277 68293404301836742174973729)
          ·
            refine ⟨51220053226377556631230297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68293404301836742174973729 51220053226377556631230297)
            ·
              refine ⟨38415039919783167473422723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51220053226377556631230297 38415039919783167473422723)
              ·
                refine ⟨57622559879674751210134085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38415039919783167473422723 57622559879674751210134085)
                ·
                  refine ⟨10804229977439015851900141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57622559879674751210134085 10804229977439015851900141)
                  ·
                    refine ⟨4051586241539630944462553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10804229977439015851900141 4051586241539630944462553)
                    ·
                      refine ⟨3038689681154723208346915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051586241539630944462553 3038689681154723208346915)
                      ·
                        rfl

theorem cell23_5917827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_5917827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917827 prefixEnd_5917827 := by exact prefixLift 5917827
  have htrace : WordTrace (prefixWord ++ tailWord_5917827) baseStart_5917827 baseEnd_5917827 := by
    simpa [prefixWord, tailWord_5917827, baseEnd_5917827] using wordTrace_append hprefix tailTrace_5917827
  have hstable : (prefixWord ++ tailWord_5917827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917827).length < 2 ^ (prefixWord ++ tailWord_5917827).sum := by decide
  have hdescent : baseEnd_5917827 < baseStart_5917827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917834 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5917834 : Nat := 118140960795 + 5917834 * 2 ^ 59
def prefixEnd_5917834 : Nat := 4983230072969 + 3 ^ 40 * 5917834 * 2
def baseEnd_5917834 : Nat := 3038693275519304680959383

theorem tailTrace_5917834 : CollatzResearch.WordTrace tailWord_5917834 prefixEnd_5917834 3038693275519304680959383 := by
  unfold tailWord_5917834
  simp only [CollatzResearch.WordTrace]
  refine ⟨53960284510676394606880139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143894092028470385618347037 53960284510676394606880139)
  ·
    refine ⟨80940426766014591910320209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53960284510676394606880139 80940426766014591910320209)
    ·
      refine ⟨60705320074510943932740157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80940426766014591910320209 60705320074510943932740157)
      ·
        refine ⟨22764495027941603974777559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60705320074510943932740157 22764495027941603974777559)
        ·
          refine ⟨34146742541912405962166339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22764495027941603974777559 34146742541912405962166339)
          ·
            refine ⟨51220113812868608943249509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34146742541912405962166339 51220113812868608943249509)
            ·
              refine ⟨9603771339912864176859283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51220113812868608943249509 9603771339912864176859283)
              ·
                refine ⟨14405657009869296265288925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9603771339912864176859283 14405657009869296265288925)
                ·
                  refine ⟨5402121378700986099483347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14405657009869296265288925 5402121378700986099483347)
                  ·
                    refine ⟨8103182068051479149225021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5402121378700986099483347 8103182068051479149225021)
                    ·
                      refine ⟨3038693275519304680959383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103182068051479149225021 3038693275519304680959383)
                      ·
                        rfl

theorem cell23_5917834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5917834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917834 prefixEnd_5917834 := by exact prefixLift 5917834
  have htrace : WordTrace (prefixWord ++ tailWord_5917834) baseStart_5917834 baseEnd_5917834 := by
    simpa [prefixWord, tailWord_5917834, baseEnd_5917834] using wordTrace_append hprefix tailTrace_5917834
  have hstable : (prefixWord ++ tailWord_5917834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917834).length < 2 ^ (prefixWord ++ tailWord_5917834).sum := by decide
  have hdescent : baseEnd_5917834 < baseStart_5917834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917840 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_5917840 : Nat := 118140960795 + 5917840 * 2 ^ 59
def prefixEnd_5917840 : Nat := 4983230072969 + 3 ^ 40 * 5917840 * 2
def baseEnd_5917840 : Nat := 3038696356403231657484355

theorem tailTrace_5917840 : CollatzResearch.WordTrace tailWord_5917840 prefixEnd_5917840 3038696356403231657484355 := by
  unfold tailWord_5917840
  simp only [CollatzResearch.WordTrace]
  refine ⟨107920678440341920726119487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143894237920455894301492649 107920678440341920726119487)
  ·
    refine ⟨161881017660512881089179231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107920678440341920726119487 161881017660512881089179231)
    ·
      refine ⟨242821526490769321633768847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161881017660512881089179231 242821526490769321633768847)
      ·
        refine ⟨364232289736153982450653271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242821526490769321633768847 364232289736153982450653271)
        ·
          refine ⟨546348434604230973675979907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364232289736153982450653271 546348434604230973675979907)
          ·
            refine ⟨819522651906346460513969861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546348434604230973675979907 819522651906346460513969861)
            ·
              refine ⟨153660497232439961346369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 819522651906346460513969861 153660497232439961346369349)
              ·
                refine ⟨28811343231082492752444253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153660497232439961346369349 28811343231082492752444253)
                ·
                  refine ⟨10804253711655934782166595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28811343231082492752444253 10804253711655934782166595)
                  ·
                    refine ⟨16206380567483902173249893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10804253711655934782166595 16206380567483902173249893)
                    ·
                      refine ⟨3038696356403231657484355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16206380567483902173249893 3038696356403231657484355)
                      ·
                        rfl

theorem cell23_5917840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_5917840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917840 prefixEnd_5917840 := by exact prefixLift 5917840
  have htrace : WordTrace (prefixWord ++ tailWord_5917840) baseStart_5917840 baseEnd_5917840 := by
    simpa [prefixWord, tailWord_5917840, baseEnd_5917840] using wordTrace_append hprefix tailTrace_5917840
  have hstable : (prefixWord ++ tailWord_5917840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917840).length < 2 ^ (prefixWord ++ tailWord_5917840).sum := by decide
  have hdescent : baseEnd_5917840 < baseStart_5917840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917854 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5917854 : Nat := 118140960795 + 5917854 * 2 ^ 59
def prefixEnd_5917854 : Nat := 4983230072969 + 3 ^ 40 * 5917854 * 2
def baseEnd_5917854 : Nat := 1012901181710798200903097

theorem tailTrace_5917854 : CollatzResearch.WordTrace tailWord_5917854 prefixEnd_5917854 1012901181710798200903097 := by
  unfold tailWord_5917854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26980233437829140230406077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143894578335088747895499077 26980233437829140230406077)
  ·
    refine ⟨10117587539185927586402279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26980233437829140230406077 10117587539185927586402279)
    ·
      refine ⟨15176381308778891379603419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117587539185927586402279 15176381308778891379603419)
      ·
        refine ⟨22764571963168337069405129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15176381308778891379603419 22764571963168337069405129)
        ·
          refine ⟨17073428972376252802053847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22764571963168337069405129 17073428972376252802053847)
          ·
            refine ⟨25610143458564379203080771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17073428972376252802053847 25610143458564379203080771)
            ·
              refine ⟨38415215187846568804621157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25610143458564379203080771 38415215187846568804621157)
              ·
                refine ⟨7202852847721231650866467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38415215187846568804621157 7202852847721231650866467)
                ·
                  refine ⟨10804279271581847476299701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202852847721231650866467 10804279271581847476299701)
                  ·
                    refine ⟨1012901181710798200903097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10804279271581847476299701 1012901181710798200903097)
                    ·
                      rfl

theorem cell23_5917854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5917854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917854 prefixEnd_5917854 := by exact prefixLift 5917854
  have htrace : WordTrace (prefixWord ++ tailWord_5917854) baseStart_5917854 baseEnd_5917854 := by
    simpa [prefixWord, tailWord_5917854, baseEnd_5917854] using wordTrace_append hprefix tailTrace_5917854
  have hstable : (prefixWord ++ tailWord_5917854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917854).length < 2 ^ (prefixWord ++ tailWord_5917854).sum := by decide
  have hdescent : baseEnd_5917854 < baseStart_5917854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917857 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5917857 : Nat := 118140960795 + 5917857 * 2 ^ 59
def prefixEnd_5917857 : Nat := 4983230072969 + 3 ^ 40 * 5917857 * 2
def baseEnd_5917857 : Nat := 3038705085574358090971777

theorem tailTrace_5917857 : CollatzResearch.WordTrace tailWord_5917857 prefixEnd_5917857 3038705085574358090971777 := by
  unfold tailWord_5917857
  simp only [CollatzResearch.WordTrace]
  refine ⟨215841976921622253355607825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143894651281081502237071883 215841976921622253355607825)
  ·
    refine ⟨161881482691216690016705869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215841976921622253355607825 161881482691216690016705869)
    ·
      refine ⟨60705556009206258756264701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161881482691216690016705869 60705556009206258756264701)
      ·
        refine ⟨22764583503452347033599263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60705556009206258756264701 22764583503452347033599263)
        ·
          refine ⟨34146875255178520550398895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22764583503452347033599263 34146875255178520550398895)
          ·
            refine ⟨51220312882767780825598343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34146875255178520550398895 51220312882767780825598343)
            ·
              refine ⟨76830469324151671238397515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51220312882767780825598343 76830469324151671238397515)
              ·
                refine ⟨115245703986227506857596273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76830469324151671238397515 115245703986227506857596273)
                ·
                  refine ⟨86434277989670630143197205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115245703986227506857596273 86434277989670630143197205)
                  ·
                    refine ⟨4051606780765810787962369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86434277989670630143197205 4051606780765810787962369)
                    ·
                      refine ⟨3038705085574358090971777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051606780765810787962369 3038705085574358090971777)
                      ·
                        rfl

theorem cell23_5917857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5917857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917857 prefixEnd_5917857 := by exact prefixLift 5917857
  have htrace : WordTrace (prefixWord ++ tailWord_5917857) baseStart_5917857 baseEnd_5917857 := by
    simpa [prefixWord, tailWord_5917857, baseEnd_5917857] using wordTrace_append hprefix tailTrace_5917857
  have hstable : (prefixWord ++ tailWord_5917857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917857).length < 2 ^ (prefixWord ++ tailWord_5917857).sum := by decide
  have hdescent : baseEnd_5917857 < baseStart_5917857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917908 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5917908 : Nat := 118140960795 + 5917908 * 2 ^ 59
def prefixEnd_5917908 : Nat := 4983230072969 + 3 ^ 40 * 5917908 * 2
def baseEnd_5917908 : Nat := 3038731273087737391434043

theorem tailTrace_5917908 : CollatzResearch.WordTrace tailWord_5917908 prefixEnd_5917908 3038731273087737391434043 := by
  unfold tailWord_5917908
  simp only [CollatzResearch.WordTrace]
  refine ⟨107921918522218744532857189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143895891362958326043809585 107921918522218744532857189)
  ·
    refine ⟨20235359722916014599910723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107921918522218744532857189 20235359722916014599910723)
    ·
      refine ⟨30353039584374021899866085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20235359722916014599910723 30353039584374021899866085)
      ·
        refine ⟨5691194922070129106224891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30353039584374021899866085 5691194922070129106224891)
        ·
          refine ⟨8536792383105193659337337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691194922070129106224891 8536792383105193659337337)
          ·
            refine ⟨6402594287328895244503003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536792383105193659337337 6402594287328895244503003)
            ·
              refine ⟨9603891430993342866754505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402594287328895244503003 9603891430993342866754505)
              ·
                refine ⟨7202918573245007150065879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9603891430993342866754505 7202918573245007150065879)
                ·
                  refine ⟨10804377859867510725098819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7202918573245007150065879 10804377859867510725098819)
                  ·
                    refine ⟨16206566789801266087648229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10804377859867510725098819 16206566789801266087648229)
                    ·
                      refine ⟨3038731273087737391434043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16206566789801266087648229 3038731273087737391434043)
                      ·
                        rfl

theorem cell23_5917908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5917908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917908 prefixEnd_5917908 := by exact prefixLift 5917908
  have htrace : WordTrace (prefixWord ++ tailWord_5917908) baseStart_5917908 baseEnd_5917908 := by
    simpa [prefixWord, tailWord_5917908, baseEnd_5917908] using wordTrace_append hprefix tailTrace_5917908
  have hstable : (prefixWord ++ tailWord_5917908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917908).length < 2 ^ (prefixWord ++ tailWord_5917908).sum := by decide
  have hdescent : baseEnd_5917908 < baseStart_5917908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917964 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_5917964 : Nat := 118140960795 + 5917964 * 2 ^ 59
def prefixEnd_5917964 : Nat := 4983230072969 + 3 ^ 40 * 5917964 * 2
def baseEnd_5917964 : Nat := 3038760028004389172333785

theorem tailTrace_5917964 : CollatzResearch.WordTrace tailWord_5917964 prefixEnd_5917964 3038760028004389172333785 := by
  unfold tailWord_5917964
  simp only [CollatzResearch.WordTrace]
  refine ⟨107922939766117305314876473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143897253021489740419835297 107922939766117305314876473)
  ·
    refine ⟨80942204824587978986157355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107922939766117305314876473 80942204824587978986157355)
    ·
      refine ⟨121413307236881968479236033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80942204824587978986157355 121413307236881968479236033)
      ·
        refine ⟨91059980427661476359427025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121413307236881968479236033 91059980427661476359427025)
        ·
          refine ⟨68294985320746107269570269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91059980427661476359427025 68294985320746107269570269)
          ·
            refine ⟨25610619495279790226088851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68294985320746107269570269 25610619495279790226088851)
            ·
              refine ⟨38415929242919685339133277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25610619495279790226088851 38415929242919685339133277)
              ·
                refine ⟨14405973466094882002174979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38415929242919685339133277 14405973466094882002174979)
                ·
                  refine ⟨21608960199142323003262469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14405973466094882002174979 21608960199142323003262469)
                  ·
                    refine ⟨4051680037339185563111713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21608960199142323003262469 4051680037339185563111713)
                    ·
                      refine ⟨3038760028004389172333785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051680037339185563111713 3038760028004389172333785)
                      ·
                        rfl

theorem cell23_5917964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_5917964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917964 prefixEnd_5917964 := by exact prefixLift 5917964
  have htrace : WordTrace (prefixWord ++ tailWord_5917964) baseStart_5917964 baseEnd_5917964 := by
    simpa [prefixWord, tailWord_5917964, baseEnd_5917964] using wordTrace_append hprefix tailTrace_5917964
  have hstable : (prefixWord ++ tailWord_5917964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917964).length < 2 ^ (prefixWord ++ tailWord_5917964).sum := by decide
  have hdescent : baseEnd_5917964 < baseStart_5917964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917981 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5917981 : Nat := 118140960795 + 5917981 * 2 ^ 59
def prefixEnd_5917981 : Nat := 4983230072969 + 3 ^ 40 * 5917981 * 2
def baseEnd_5917981 : Nat := 3038768757175515605821207

theorem tailTrace_5917981 : CollatzResearch.WordTrace tailWord_5917981 prefixEnd_5917981 3038768757175515605821207 := by
  unfold tailWord_5917981
  simp only [CollatzResearch.WordTrace]
  refine ⟨215846499573173022533121797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143897666382115348355414531 215846499573173022533121797)
  ·
    refine ⟨40471218669969941724960337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215846499573173022533121797 40471218669969941724960337)
    ·
      refine ⟨30353414002477456293720253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40471218669969941724960337 30353414002477456293720253)
      ·
        refine ⟨11382530250929046110145095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30353414002477456293720253 11382530250929046110145095)
        ·
          refine ⟨17073795376393569165217643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382530250929046110145095 17073795376393569165217643)
          ·
            refine ⟨25610693064590353747826465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17073795376393569165217643 25610693064590353747826465)
            ·
              refine ⟨19208019798442765310869849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25610693064590353747826465 19208019798442765310869849)
              ·
                refine ⟨14406014848832073983152387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19208019798442765310869849 14406014848832073983152387)
                ·
                  refine ⟨21609022273248110974728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14406014848832073983152387 21609022273248110974728581)
                  ·
                    refine ⟨4051691676234020807761609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21609022273248110974728581 4051691676234020807761609)
                    ·
                      refine ⟨3038768757175515605821207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051691676234020807761609 3038768757175515605821207)
                      ·
                        rfl

theorem cell23_5917981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5917981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917981 prefixEnd_5917981 := by exact prefixLift 5917981
  have htrace : WordTrace (prefixWord ++ tailWord_5917981) baseStart_5917981 baseEnd_5917981 := by
    simpa [prefixWord, tailWord_5917981, baseEnd_5917981] using wordTrace_append hprefix tailTrace_5917981
  have hstable : (prefixWord ++ tailWord_5917981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917981).length < 2 ^ (prefixWord ++ tailWord_5917981).sum := by decide
  have hdescent : baseEnd_5917981 < baseStart_5917981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5917994 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5917994 : Nat := 118140960795 + 5917994 * 2 ^ 59
def prefixEnd_5917994 : Nat := 4983230072969 + 3 ^ 40 * 5917994 * 2
def baseEnd_5917994 : Nat := 3038775432424024054958647

theorem tailTrace_5917994 : CollatzResearch.WordTrace tailWord_5917994 prefixEnd_5917994 3038775432424024054958647 := by
  unfold tailWord_5917994
  simp only [CollatzResearch.WordTrace]
  refine ⟨53961743430531481438336259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143897982481417283835563357 53961743430531481438336259)
  ·
    refine ⟨80942615145797222157504389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53961743430531481438336259 80942615145797222157504389)
    ·
      refine ⟨15176740339836979154532073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80942615145797222157504389 15176740339836979154532073)
      ·
        refine ⟨11382555254877734365899055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15176740339836979154532073 11382555254877734365899055)
        ·
          refine ⟨17073832882316601548848583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382555254877734365899055 17073832882316601548848583)
          ·
            refine ⟨25610749323474902323272875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17073832882316601548848583 25610749323474902323272875)
            ·
              refine ⟨38416123985212353484909313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25610749323474902323272875 38416123985212353484909313)
              ·
                refine ⟨28812092988909265113681985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38416123985212353484909313 28812092988909265113681985)
                ·
                  refine ⟨21609069741681948835261489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28812092988909265113681985 21609069741681948835261489)
                  ·
                    refine ⟨16206802306261461626446117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21609069741681948835261489 16206802306261461626446117)
                    ·
                      refine ⟨3038775432424024054958647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16206802306261461626446117 3038775432424024054958647)
                      ·
                        rfl

theorem cell23_5917994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5917994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5917994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5917994 prefixEnd_5917994 := by exact prefixLift 5917994
  have htrace : WordTrace (prefixWord ++ tailWord_5917994) baseStart_5917994 baseEnd_5917994 := by
    simpa [prefixWord, tailWord_5917994, baseEnd_5917994] using wordTrace_append hprefix tailTrace_5917994
  have hstable : (prefixWord ++ tailWord_5917994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5917994).length < 2 ^ (prefixWord ++ tailWord_5917994).sum := by decide
  have hdescent : baseEnd_5917994 < baseStart_5917994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5917994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918004 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5918004 : Nat := 118140960795 + 5918004 * 2 ^ 59
def prefixEnd_5918004 : Nat := 4983230072969 + 3 ^ 40 * 5918004 * 2
def baseEnd_5918004 : Nat := 337642285247841001759289

theorem tailTrace_5918004 : CollatzResearch.WordTrace tailWord_5918004 prefixEnd_5918004 337642285247841001759289 := by
  unfold tailWord_5918004
  simp only [CollatzResearch.WordTrace]
  refine ⟨107923669226044848730604533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143898225634726464974139377 107923669226044848730604533)
  ·
    refine ⟨10117843989941704568494175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107923669226044848730604533 10117843989941704568494175)
    ·
      refine ⟨15176765984912556852741263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117843989941704568494175 15176765984912556852741263)
      ·
        refine ⟨22765148977368835279111895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15176765984912556852741263 22765148977368835279111895)
        ·
          refine ⟨34147723466053252918667843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22765148977368835279111895 34147723466053252918667843)
          ·
            refine ⟨51221585199079879378001765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34147723466053252918667843 51221585199079879378001765)
            ·
              refine ⟨9604047224827477383375331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51221585199079879378001765 9604047224827477383375331)
              ·
                refine ⟨14406070837241216075062997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9604047224827477383375331 14406070837241216075062997)
                ·
                  refine ⟨337642285247841001759289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14406070837241216075062997 337642285247841001759289)
                  ·
                    rfl

theorem cell23_5918004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5918004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918004 prefixEnd_5918004 := by exact prefixLift 5918004
  have htrace : WordTrace (prefixWord ++ tailWord_5918004) baseStart_5918004 baseEnd_5918004 := by
    simpa [prefixWord, tailWord_5918004, baseEnd_5918004] using wordTrace_append hprefix tailTrace_5918004
  have hstable : (prefixWord ++ tailWord_5918004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918004).length < 2 ^ (prefixWord ++ tailWord_5918004).sum := by decide
  have hdescent : baseEnd_5918004 < baseStart_5918004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918014 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_5918014 : Nat := 118140960795 + 5918014 * 2 ^ 59
def prefixEnd_5918014 : Nat := 4983230072969 + 3 ^ 40 * 5918014 * 2
def baseEnd_5918014 : Nat := 3038785702037113976708555

theorem tailTrace_5918014 : CollatzResearch.WordTrace tailWord_5918014 prefixEnd_5918014 3038785702037113976708555 := by
  unfold tailWord_5918014
  simp only [CollatzResearch.WordTrace]
  refine ⟨26980962897756683646134137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143898468788035646112715397 26980962897756683646134137)
  ·
    refine ⟨20235722173317512734600603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26980962897756683646134137 20235722173317512734600603)
    ·
      refine ⟨30353583259976269101900905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20235722173317512734600603 30353583259976269101900905)
      ·
        refine ⟨22765187444982201826425679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30353583259976269101900905 22765187444982201826425679)
        ·
          refine ⟨34147781167473302739638519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22765187444982201826425679 34147781167473302739638519)
          ·
            refine ⟨51221671751209954109457779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34147781167473302739638519 51221671751209954109457779)
            ·
              refine ⟨76832507626814931164186669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51221671751209954109457779 76832507626814931164186669)
              ·
                refine ⟨28812190360055599186570001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76832507626814931164186669 28812190360055599186570001)
                ·
                  refine ⟨21609142770041699389927501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28812190360055599186570001 21609142770041699389927501)
                  ·
                    refine ⟨8103428538765637271222813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21609142770041699389927501 8103428538765637271222813)
                    ·
                      refine ⟨3038785702037113976708555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103428538765637271222813 3038785702037113976708555)
                      ·
                        rfl

theorem cell23_5918014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_5918014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918014 prefixEnd_5918014 := by exact prefixLift 5918014
  have htrace : WordTrace (prefixWord ++ tailWord_5918014) baseStart_5918014 baseEnd_5918014 := by
    simpa [prefixWord, tailWord_5918014, baseEnd_5918014] using wordTrace_append hprefix tailTrace_5918014
  have hstable : (prefixWord ++ tailWord_5918014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918014).length < 2 ^ (prefixWord ++ tailWord_5918014).sum := by decide
  have hdescent : baseEnd_5918014 < baseStart_5918014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918057 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_5918057 : Nat := 118140960795 + 5918057 * 2 ^ 59
def prefixEnd_5918057 : Nat := 4983230072969 + 3 ^ 40 * 5918057 * 2
def baseEnd_5918057 : Nat := 3038807781705257308470857

theorem tailTrace_5918057 : CollatzResearch.WordTrace tailWord_5918057 prefixEnd_5918057 3038807781705257308470857 := by
  unfold tailWord_5918057
  simp only [CollatzResearch.WordTrace]
  refine ⟨215849271520897687512888425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143899514347265125008592283 215849271520897687512888425)
  ·
    refine ⟨161886953640673265634666319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215849271520897687512888425 161886953640673265634666319)
    ·
      refine ⟨242830430461009898451999479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161886953640673265634666319 242830430461009898451999479)
      ·
        refine ⟨364245645691514847677999219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242830430461009898451999479 364245645691514847677999219)
        ·
          refine ⟨546368468537272271516998829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364245645691514847677999219 546368468537272271516998829)
          ·
            refine ⟨204888175701477101818874561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546368468537272271516998829 204888175701477101818874561)
            ·
              refine ⟨153666131776107826364155921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204888175701477101818874561 153666131776107826364155921)
              ·
                refine ⟨115249598832080869773116941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153666131776107826364155921 115249598832080869773116941)
                ·
                  refine ⟨43218599562030326164918853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115249598832080869773116941 43218599562030326164918853)
                  ·
                    refine ⟨8103487417880686155922285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43218599562030326164918853 8103487417880686155922285)
                    ·
                      refine ⟨3038807781705257308470857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103487417880686155922285 3038807781705257308470857)
                      ·
                        rfl

theorem cell23_5918057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_5918057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918057 prefixEnd_5918057 := by exact prefixLift 5918057
  have htrace : WordTrace (prefixWord ++ tailWord_5918057) baseStart_5918057 baseEnd_5918057 := by
    simpa [prefixWord, tailWord_5918057, baseEnd_5918057] using wordTrace_append hprefix tailTrace_5918057
  have hstable : (prefixWord ++ tailWord_5918057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918057).length < 2 ^ (prefixWord ++ tailWord_5918057).sum := by decide
  have hdescent : baseEnd_5918057 < baseStart_5918057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918144 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_5918144 : Nat := 118140960795 + 5918144 * 2 ^ 59
def prefixEnd_5918144 : Nat := 4983230072969 + 3 ^ 40 * 5918144 * 2
def baseEnd_5918144 : Nat := 3038852454522198468082957

theorem tailTrace_5918144 : CollatzResearch.WordTrace tailWord_5918144 prefixEnd_5918144 3038852454522198468082957 := by
  unfold tailWord_5918144
  simp only [CollatzResearch.WordTrace]
  refine ⟨107926222335791250685652743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143901629781055000914203657 107926222335791250685652743)
  ·
    refine ⟨161889333503686876028479115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107926222335791250685652743 161889333503686876028479115)
    ·
      refine ⟨242834000255530314042718673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161889333503686876028479115 242834000255530314042718673)
      ·
        refine ⟨182125500191647735532039005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242834000255530314042718673 182125500191647735532039005)
        ·
          refine ⟨68297062571867900824514627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182125500191647735532039005 68297062571867900824514627)
          ·
            refine ⟨102445593857801851236771941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68297062571867900824514627 102445593857801851236771941)
            ·
              refine ⟨19208548848337847106894739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102445593857801851236771941 19208548848337847106894739)
              ·
                refine ⟨28812823272506770660342109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19208548848337847106894739 28812823272506770660342109)
                ·
                  refine ⟨10804808727190038997628291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28812823272506770660342109 10804808727190038997628291)
                  ·
                    refine ⟨16207213090785058496442437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10804808727190038997628291 16207213090785058496442437)
                    ·
                      refine ⟨3038852454522198468082957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16207213090785058496442437 3038852454522198468082957)
                      ·
                        rfl

theorem cell23_5918144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_5918144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918144 prefixEnd_5918144 := by exact prefixLift 5918144
  have htrace : WordTrace (prefixWord ++ tailWord_5918144) baseStart_5918144 baseEnd_5918144 := by
    simpa [prefixWord, tailWord_5918144, baseEnd_5918144] using wordTrace_append hprefix tailTrace_5918144
  have hstable : (prefixWord ++ tailWord_5918144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918144).length < 2 ^ (prefixWord ++ tailWord_5918144).sum := by decide
  have hdescent : baseEnd_5918144 < baseStart_5918144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918148 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5918148 : Nat := 118140960795 + 5918148 * 2 ^ 59
def prefixEnd_5918148 : Nat := 4983230072969 + 3 ^ 40 * 5918148 * 2
def baseEnd_5918148 : Nat := 3038854508444816452432939

theorem tailTrace_5918148 : CollatzResearch.WordTrace tailWord_5918148 prefixEnd_5918148 3038854508444816452432939 := by
  unfold tailWord_5918148
  simp only [CollatzResearch.WordTrace]
  refine ⟨107926295281784005027225549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143901727042378673369634065 107926295281784005027225549)
  ·
    refine ⟨40472360730669001885209581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107926295281784005027225549 40472360730669001885209581)
    ·
      refine ⟨15177135274000875706953593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40472360730669001885209581 15177135274000875706953593)
      ·
        refine ⟨11382851455500656780215195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15177135274000875706953593 11382851455500656780215195)
        ·
          refine ⟨17074277183250985170322793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382851455500656780215195 17074277183250985170322793)
          ·
            refine ⟨12805707887438238877742095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17074277183250985170322793 12805707887438238877742095)
            ·
              refine ⟨19208561831157358316613143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12805707887438238877742095 19208561831157358316613143)
              ·
                refine ⟨28812842746736037474919715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19208561831157358316613143 28812842746736037474919715)
                ·
                  refine ⟨43219264120104056212379573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28812842746736037474919715 43219264120104056212379573)
                  ·
                    refine ⟨4051806011259755269910585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43219264120104056212379573 4051806011259755269910585)
                    ·
                      refine ⟨3038854508444816452432939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4051806011259755269910585 3038854508444816452432939)
                      ·
                        rfl

theorem cell23_5918148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5918148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918148 prefixEnd_5918148 := by exact prefixLift 5918148
  have htrace : WordTrace (prefixWord ++ tailWord_5918148) baseStart_5918148 baseEnd_5918148 := by
    simpa [prefixWord, tailWord_5918148, baseEnd_5918148] using wordTrace_append hprefix tailTrace_5918148
  have hstable : (prefixWord ++ tailWord_5918148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918148).length < 2 ^ (prefixWord ++ tailWord_5918148).sum := by decide
  have hdescent : baseEnd_5918148 < baseStart_5918148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918154 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_5918154 : Nat := 118140960795 + 5918154 * 2 ^ 59
def prefixEnd_5918154 : Nat := 4983230072969 + 3 ^ 40 * 5918154 * 2
def baseEnd_5918154 : Nat := 1012952529776247809652637

theorem tailTrace_5918154 : CollatzResearch.WordTrace tailWord_5918154 prefixEnd_5918154 1012952529776247809652637 := by
  unfold tailWord_5918154
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963202350386568269792379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143901872934364182052779677 53963202350386568269792379)
  ·
    refine ⟨80944803525579852404688569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53963202350386568269792379 80944803525579852404688569)
    ·
      refine ⟨60708602644184889303516427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80944803525579852404688569 60708602644184889303516427)
      ·
        refine ⟨91062903966277333955274641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60708602644184889303516427 91062903966277333955274641)
        ·
          refine ⟨68297177974708000466455981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91062903966277333955274641 68297177974708000466455981)
          ·
            refine ⟨25611441740515500174920993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68297177974708000466455981 25611441740515500174920993)
            ·
              refine ⟨19208581305386625131190745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25611441740515500174920993 19208581305386625131190745)
              ·
                refine ⟨14406435979039968848393059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19208581305386625131190745 14406435979039968848393059)
                ·
                  refine ⟨21609653968559953272589589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14406435979039968848393059 21609653968559953272589589)
                  ·
                    refine ⟨1012952529776247809652637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21609653968559953272589589 1012952529776247809652637)
                    ·
                      rfl

theorem cell23_5918154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_5918154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918154 prefixEnd_5918154 := by exact prefixLift 5918154
  have htrace : WordTrace (prefixWord ++ tailWord_5918154) baseStart_5918154 baseEnd_5918154 := by
    simpa [prefixWord, tailWord_5918154, baseEnd_5918154] using wordTrace_append hprefix tailTrace_5918154
  have hstable : (prefixWord ++ tailWord_5918154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918154).length < 2 ^ (prefixWord ++ tailWord_5918154).sum := by decide
  have hdescent : baseEnd_5918154 < baseStart_5918154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918181 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5918181 : Nat := 118140960795 + 5918181 * 2 ^ 59
def prefixEnd_5918181 : Nat := 4983230072969 + 3 ^ 40 * 5918181 * 2
def baseEnd_5918181 : Nat := 3038871453306414823320287

theorem tailTrace_5918181 : CollatzResearch.WordTrace tailWord_5918181 prefixEnd_5918181 3038871453306414823320287 := by
  unfold tailWord_5918181
  simp only [CollatzResearch.WordTrace]
  refine ⟨215853794172448456690402397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143902529448298971126934931 215853794172448456690402397)
  ·
    refine ⟨80945172814668171258900899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215853794172448456690402397 80945172814668171258900899)
    ·
      refine ⟨121417759222002256888351349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80945172814668171258900899 121417759222002256888351349)
      ·
        refine ⟨11382914927062711583282939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121417759222002256888351349 11382914927062711583282939)
        ·
          refine ⟨17074372390594067374924409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11382914927062711583282939 17074372390594067374924409)
          ·
            refine ⟨12805779292945550531193307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17074372390594067374924409 12805779292945550531193307)
            ·
              refine ⟨19208668939418325796789961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12805779292945550531193307 19208668939418325796789961)
              ·
                refine ⟨14406501704563744347592471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19208668939418325796789961 14406501704563744347592471)
                ·
                  refine ⟨21609752556845616521388707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14406501704563744347592471 21609752556845616521388707)
                  ·
                    refine ⟨32414628835268424782083061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21609752556845616521388707 32414628835268424782083061)
                    ·
                      refine ⟨3038871453306414823320287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32414628835268424782083061 3038871453306414823320287)
                      ·
                        rfl

theorem cell23_5918181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5918181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918181 prefixEnd_5918181 := by exact prefixLift 5918181
  have htrace : WordTrace (prefixWord ++ tailWord_5918181) baseStart_5918181 baseEnd_5918181 := by
    simpa [prefixWord, tailWord_5918181, baseEnd_5918181] using wordTrace_append hprefix tailTrace_5918181
  have hstable : (prefixWord ++ tailWord_5918181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918181).length < 2 ^ (prefixWord ++ tailWord_5918181).sum := by decide
  have hdescent : baseEnd_5918181 < baseStart_5918181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_5918187 : Nat := 118140960795 + 5918187 * 2 ^ 59
def prefixEnd_5918187 : Nat := 4983230072969 + 3 ^ 40 * 5918187 * 2
def baseEnd_5918187 : Nat := 3038874534190341799845259

theorem tailTrace_5918187 : CollatzResearch.WordTrace tailWord_5918187 prefixEnd_5918187 3038874534190341799845259 := by
  unfold tailWord_5918187
  simp only [CollatzResearch.WordTrace]
  refine ⟨215854013010426719715120815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143902675340284479810080543 215854013010426719715120815)
  ·
    refine ⟨323781019515640079572681223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215854013010426719715120815 323781019515640079572681223)
    ·
      refine ⟨485671529273460119359021835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323781019515640079572681223 485671529273460119359021835)
      ·
        refine ⟨728507293910190179038532753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485671529273460119359021835 728507293910190179038532753)
        ·
          refine ⟨546380470432642634278899565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728507293910190179038532753 546380470432642634278899565)
          ·
            refine ⟨204892676412240987854587337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546380470432642634278899565 204892676412240987854587337)
            ·
              refine ⟨153669507309180740890940503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204892676412240987854587337 153669507309180740890940503)
              ·
                refine ⟨230504260963771111336410755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153669507309180740890940503 230504260963771111336410755)
                ·
                  refine ⟨345756391445656667004616133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230504260963771111336410755 345756391445656667004616133)
                  ·
                    refine ⟨64829323396060625063365525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345756391445656667004616133 64829323396060625063365525)
                    ·
                      refine ⟨3038874534190341799845259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64829323396060625063365525 3038874534190341799845259)
                      ·
                        rfl

theorem cell23_5918187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_5918187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918187 prefixEnd_5918187 := by exact prefixLift 5918187
  have htrace : WordTrace (prefixWord ++ tailWord_5918187) baseStart_5918187 baseEnd_5918187 := by
    simpa [prefixWord, tailWord_5918187, baseEnd_5918187] using wordTrace_append hprefix tailTrace_5918187
  have hstable : (prefixWord ++ tailWord_5918187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918187).length < 2 ^ (prefixWord ++ tailWord_5918187).sum := by decide
  have hdescent : baseEnd_5918187 < baseStart_5918187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918198 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5918198 : Nat := 118140960795 + 5918198 * 2 ^ 59
def prefixEnd_5918198 : Nat := 4983230072969 + 3 ^ 40 * 5918198 * 2
def baseEnd_5918198 : Nat := 3038880182477541256807709

theorem tailTrace_5918198 : CollatzResearch.WordTrace tailWord_5918198 prefixEnd_5918198 3038880182477541256807709 := by
  unfold tailWord_5918198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490900888336679287110703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143902942808924579062514165 13490900888336679287110703)
  ·
    refine ⟨20236351332505018930666055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13490900888336679287110703 20236351332505018930666055)
    ·
      refine ⟨30354526998757528395999083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20236351332505018930666055 30354526998757528395999083)
      ·
        refine ⟨45531790498136292593998625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30354526998757528395999083 45531790498136292593998625)
        ·
          refine ⟨34148842873602219445498969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45531790498136292593998625 34148842873602219445498969)
          ·
            refine ⟨25611632155201664584124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34148842873602219445498969 25611632155201664584124227)
            ·
              refine ⟨38417448232802496876186341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25611632155201664584124227 38417448232802496876186341)
              ·
                refine ⟨7203271543650468164284939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38417448232802496876186341 7203271543650468164284939)
                ·
                  refine ⟨10804907315475702246427409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203271543650468164284939 10804907315475702246427409)
                  ·
                    refine ⟨8103680486606776684820557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10804907315475702246427409 8103680486606776684820557)
                    ·
                      refine ⟨3038880182477541256807709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103680486606776684820557 3038880182477541256807709)
                      ·
                        rfl

theorem cell23_5918198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5918198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918198 prefixEnd_5918198 := by exact prefixLift 5918198
  have htrace : WordTrace (prefixWord ++ tailWord_5918198) baseStart_5918198 baseEnd_5918198 := by
    simpa [prefixWord, tailWord_5918198, baseEnd_5918198] using wordTrace_append hprefix tailTrace_5918198
  have hstable : (prefixWord ++ tailWord_5918198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918198).length < 2 ^ (prefixWord ++ tailWord_5918198).sum := by decide
  have hdescent : baseEnd_5918198 < baseStart_5918198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918206 : List Nat := [4, 2, 2, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5918206 : Nat := 118140960795 + 5918206 * 2 ^ 59
def prefixEnd_5918206 : Nat := 4983230072969 + 3 ^ 40 * 5918206 * 2
def baseEnd_5918206 : Nat := 3038884290322777225507673

theorem tailTrace_5918206 : CollatzResearch.WordTrace tailWord_5918206 prefixEnd_5918206 3038884290322777225507673 := by
  unfold tailWord_5918206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26981838249669735745007809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143903137331571923973374981 26981838249669735745007809)
  ·
    refine ⟨20236378687252301808755857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26981838249669735745007809 20236378687252301808755857)
    ·
      refine ⟨15177284015439226356566893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20236378687252301808755857 15177284015439226356566893)
      ·
        refine ⟨5691481505789709883712585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15177284015439226356566893 5691481505789709883712585)
        ·
          refine ⟨4268611129342282412784439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691481505789709883712585 4268611129342282412784439)
          ·
            refine ⟨6402916694013423619176659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268611129342282412784439 6402916694013423619176659)
            ·
              refine ⟨9604375041020135428764989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402916694013423619176659 9604375041020135428764989)
              ·
                refine ⟨3601640640382550785786871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604375041020135428764989 3601640640382550785786871)
                ·
                  refine ⟨5402460960573826178680307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601640640382550785786871 5402460960573826178680307)
                  ·
                    refine ⟨8103691440860739268020461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5402460960573826178680307 8103691440860739268020461)
                    ·
                      refine ⟨3038884290322777225507673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103691440860739268020461 3038884290322777225507673)
                      ·
                        rfl

theorem cell23_5918206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5918206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918206 prefixEnd_5918206 := by exact prefixLift 5918206
  have htrace : WordTrace (prefixWord ++ tailWord_5918206) baseStart_5918206 baseEnd_5918206 := by
    simpa [prefixWord, tailWord_5918206, baseEnd_5918206] using wordTrace_append hprefix tailTrace_5918206
  have hstable : (prefixWord ++ tailWord_5918206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918206).length < 2 ^ (prefixWord ++ tailWord_5918206).sum := by decide
  have hdescent : baseEnd_5918206 < baseStart_5918206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918234 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_5918234 : Nat := 118140960795 + 5918234 * 2 ^ 59
def prefixEnd_5918234 : Nat := 4983230072969 + 3 ^ 40 * 5918234 * 2
def baseEnd_5918234 : Nat := 3038898667781103115957543

theorem tailTrace_5918234 : CollatzResearch.WordTrace tailWord_5918234 prefixEnd_5918234 3038898667781103115957543 := by
  unfold tailWord_5918234
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963931810314111685520439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143903818160837631161387837 53963931810314111685520439)
  ·
    refine ⟨80945897715471167528280659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53963931810314111685520439 80945897715471167528280659)
    ·
      refine ⟨121418846573206751292420989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80945897715471167528280659 121418846573206751292420989)
      ·
        refine ⟨45532067464952531734657871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121418846573206751292420989 45532067464952531734657871)
        ·
          refine ⟨68298101197428797601986807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45532067464952531734657871 68298101197428797601986807)
          ·
            refine ⟨102447151796143196402980211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68298101197428797601986807 102447151796143196402980211)
            ·
              refine ⟨153670727694214794604470317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102447151796143196402980211 153670727694214794604470317)
              ·
                refine ⟨57626522885330547976676369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153670727694214794604470317 57626522885330547976676369)
                ·
                  refine ⟨43219892163997910982507277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57626522885330547976676369 43219892163997910982507277)
                  ·
                    refine ⟨16207459561499216618440229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43219892163997910982507277 16207459561499216618440229)
                    ·
                      refine ⟨3038898667781103115957543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16207459561499216618440229 3038898667781103115957543)
                      ·
                        rfl

theorem cell23_5918234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_5918234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918234 prefixEnd_5918234 := by exact prefixLift 5918234
  have htrace : WordTrace (prefixWord ++ tailWord_5918234) baseStart_5918234 baseEnd_5918234 := by
    simpa [prefixWord, tailWord_5918234, baseEnd_5918234] using wordTrace_append hprefix tailTrace_5918234
  have hstable : (prefixWord ++ tailWord_5918234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918234).length < 2 ^ (prefixWord ++ tailWord_5918234).sum := by decide
  have hdescent : baseEnd_5918234 < baseStart_5918234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918304 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_5918304 : Nat := 118140960795 + 5918304 * 2 ^ 59
def prefixEnd_5918304 : Nat := 4983230072969 + 3 ^ 40 * 5918304 * 2
def baseEnd_5918304 : Nat := 1012978203808972614027407

theorem tailTrace_5918304 : CollatzResearch.WordTrace tailWord_5918304 prefixEnd_5918304 1012978203808972614027407 := by
  unfold tailWord_5918304
  simp only [CollatzResearch.WordTrace]
  refine ⟨107929140175501424348564983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143905520234001899131419977 107929140175501424348564983)
  ·
    refine ⟨161893710263252136522847475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107929140175501424348564983 161893710263252136522847475)
    ·
      refine ⟨242840565394878204784271213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161893710263252136522847475 242840565394878204784271213)
      ·
        refine ⟨91065212023079326794101705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242840565394878204784271213 91065212023079326794101705)
        ·
          refine ⟨68298909017309495095576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91065212023079326794101705 68298909017309495095576279)
          ·
            refine ⟨102448363525964242643364419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68298909017309495095576279 102448363525964242643364419)
            ·
              refine ⟨153672545288946363965046629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102448363525964242643364419 153672545288946363965046629)
              ·
                refine ⟨28813602241677443243446243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153672545288946363965046629 28813602241677443243446243)
                ·
                  refine ⟨43220403362516164865169365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28813602241677443243446243 43220403362516164865169365)
                  ·
                    refine ⟨1012978203808972614027407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43220403362516164865169365 1012978203808972614027407)
                    ·
                      rfl

theorem cell23_5918304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_5918304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918304 prefixEnd_5918304 := by exact prefixLift 5918304
  have htrace : WordTrace (prefixWord ++ tailWord_5918304) baseStart_5918304 baseEnd_5918304 := by
    simpa [prefixWord, tailWord_5918304, baseEnd_5918304] using wordTrace_append hprefix tailTrace_5918304
  have hstable : (prefixWord ++ tailWord_5918304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918304).length < 2 ^ (prefixWord ++ tailWord_5918304).sum := by decide
  have hdescent : baseEnd_5918304 < baseStart_5918304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918325 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 5]
def baseStart_5918325 : Nat := 118140960795 + 5918325 * 2 ^ 59
def prefixEnd_5918325 : Nat := 4983230072969 + 3 ^ 40 * 5918325 * 2
def baseEnd_5918325 : Nat := 337660599391184695546625

theorem tailTrace_5918325 : CollatzResearch.WordTrace tailWord_5918325 prefixEnd_5918325 337660599391184695546625 := by
  unfold tailWord_5918325
  simp only [CollatzResearch.WordTrace]
  refine ⟨215859046283926769283644429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143906030855951179522429619 215859046283926769283644429)
  ·
    refine ⟨80947142356472538481366661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215859046283926769283644429 80947142356472538481366661)
    ·
      refine ⟨15177589191838600965256249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80947142356472538481366661 15177589191838600965256249)
      ·
        refine ⟨11383191893878950723942187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15177589191838600965256249 11383191893878950723942187)
        ·
          refine ⟨17074787840818426085913281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11383191893878950723942187 17074787840818426085913281)
          ·
            refine ⟨12806090880613819564434961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17074787840818426085913281 12806090880613819564434961)
            ·
              refine ⟨9604568160460364673326221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12806090880613819564434961 9604568160460364673326221)
              ·
                refine ⟨3601713060172636752497333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604568160460364673326221 3601713060172636752497333)
                ·
                  refine ⟨337660599391184695546625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3601713060172636752497333 337660599391184695546625)
                  ·
                    rfl

theorem cell23_5918325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_5918325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918325 prefixEnd_5918325 := by exact prefixLift 5918325
  have htrace : WordTrace (prefixWord ++ tailWord_5918325) baseStart_5918325 baseEnd_5918325 := by
    simpa [prefixWord, tailWord_5918325, baseEnd_5918325] using wordTrace_append hprefix tailTrace_5918325
  have hstable : (prefixWord ++ tailWord_5918325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918325).length < 2 ^ (prefixWord ++ tailWord_5918325).sum := by decide
  have hdescent : baseEnd_5918325 < baseStart_5918325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918341 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_5918341 : Nat := 118140960795 + 5918341 * 2 ^ 59
def prefixEnd_5918341 : Nat := 4983230072969 + 3 ^ 40 * 5918341 * 2
def baseEnd_5918341 : Nat := 3038953610211134197319551

theorem tailTrace_5918341 : CollatzResearch.WordTrace tailWord_5918341 prefixEnd_5918341 3038953610211134197319551 := by
  unfold tailWord_5918341
  simp only [CollatzResearch.WordTrace]
  refine ⟨215859629851868804016226877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143906419901245869344151251 215859629851868804016226877)
  ·
    refine ⟨80947361194450801506085079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215859629851868804016226877 80947361194450801506085079)
    ·
      refine ⟨121421041791676202259127619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80947361194450801506085079 121421041791676202259127619)
      ·
        refine ⟨182131562687514303388691429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121421041791676202259127619 182131562687514303388691429)
        ·
          refine ⟨34149668003908931885379643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182131562687514303388691429 34149668003908931885379643)
          ·
            refine ⟨51224502005863397828069465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34149668003908931885379643 51224502005863397828069465)
            ·
              refine ⟨38418376504397548371052099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51224502005863397828069465 38418376504397548371052099)
              ·
                refine ⟨57627564756596322556578149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38418376504397548371052099 57627564756596322556578149)
                ·
                  refine ⟨10805168391861810479358403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57627564756596322556578149 10805168391861810479358403)
                  ·
                    refine ⟨16207752587792715719037605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10805168391861810479358403 16207752587792715719037605)
                    ·
                      refine ⟨3038953610211134197319551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16207752587792715719037605 3038953610211134197319551)
                      ·
                        rfl

theorem cell23_5918341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_5918341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918341 prefixEnd_5918341 := by exact prefixLift 5918341
  have htrace : WordTrace (prefixWord ++ tailWord_5918341) baseStart_5918341 baseEnd_5918341 := by
    simpa [prefixWord, tailWord_5918341, baseEnd_5918341] using wordTrace_append hprefix tailTrace_5918341
  have hstable : (prefixWord ++ tailWord_5918341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918341).length < 2 ^ (prefixWord ++ tailWord_5918341).sum := by decide
  have hdescent : baseEnd_5918341 < baseStart_5918341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918361 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_5918361 : Nat := 118140960795 + 5918361 * 2 ^ 59
def prefixEnd_5918361 : Nat := 4983230072969 + 3 ^ 40 * 5918361 * 2
def baseEnd_5918361 : Nat := 3038963879824224119069459

theorem tailTrace_5918361 : CollatzResearch.WordTrace tailWord_5918361 prefixEnd_5918361 3038963879824224119069459 := by
  unfold tailWord_5918361
  simp only [CollatzResearch.WordTrace]
  refine ⟨215860359311796347431954937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143906906207864231621303291 215860359311796347431954937)
  ·
    refine ⟨161895269483847260573966203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215860359311796347431954937 161895269483847260573966203)
    ·
      refine ⟨242842904225770890860949305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161895269483847260573966203 242842904225770890860949305)
      ·
        refine ⟨182132178169328168145711979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242842904225770890860949305 182132178169328168145711979)
        ·
          refine ⟨273198267253992252218567969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182132178169328168145711979 273198267253992252218567969)
          ·
            refine ⟨204898700440494189163925977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273198267253992252218567969 204898700440494189163925977)
            ·
              refine ⟨153674025330370641872944483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204898700440494189163925977 153674025330370641872944483)
              ·
                refine ⟨230511037995555962809416725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153674025330370641872944483 230511037995555962809416725)
                ·
                  refine ⟨10805204906041685756691409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230511037995555962809416725 10805204906041685756691409)
                  ·
                    refine ⟨8103903679531264317518557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10805204906041685756691409 8103903679531264317518557)
                    ·
                      refine ⟨3038963879824224119069459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8103903679531264317518557 3038963879824224119069459)
                      ·
                        rfl

theorem cell23_5918361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_5918361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918361 prefixEnd_5918361 := by exact prefixLift 5918361
  have htrace : WordTrace (prefixWord ++ tailWord_5918361) baseStart_5918361 baseEnd_5918361 := by
    simpa [prefixWord, tailWord_5918361, baseEnd_5918361] using wordTrace_append hprefix tailTrace_5918361
  have hstable : (prefixWord ++ tailWord_5918361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918361).length < 2 ^ (prefixWord ++ tailWord_5918361).sum := by decide
  have hdescent : baseEnd_5918361 < baseStart_5918361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918368 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_5918368 : Nat := 118140960795 + 5918368 * 2 ^ 59
def prefixEnd_5918368 : Nat := 4983230072969 + 3 ^ 40 * 5918368 * 2
def baseEnd_5918368 : Nat := 1012989158062935197227309

theorem tailTrace_5918368 : CollatzResearch.WordTrace tailWord_5918368 prefixEnd_5918368 1012989158062935197227309 := by
  unfold tailWord_5918368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107930307311385493813729879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143907076415180658418306505 107930307311385493813729879)
  ·
    refine ⟨161895460967078240720594819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107930307311385493813729879 161895460967078240720594819)
    ·
      refine ⟨242843191450617361080892229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161895460967078240720594819 242843191450617361080892229)
      ·
        refine ⟨45533098396990755202667293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242843191450617361080892229 45533098396990755202667293)
        ·
          refine ⟨17074911898871533201000235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45533098396990755202667293 17074911898871533201000235)
          ·
            refine ⟨25612367848307299801500353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17074911898871533201000235 25612367848307299801500353)
            ·
              refine ⟨19209275886230474851125265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25612367848307299801500353 19209275886230474851125265)
              ·
                refine ⟨14406956914672856138343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19209275886230474851125265 14406956914672856138343949)
                ·
                  refine ⟨5402608843002321051878981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14406956914672856138343949 5402608843002321051878981)
                  ·
                    refine ⟨1012989158062935197227309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402608843002321051878981 1012989158062935197227309)
                    ·
                      rfl

theorem cell23_5918368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_5918368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918368 prefixEnd_5918368 := by exact prefixLift 5918368
  have htrace : WordTrace (prefixWord ++ tailWord_5918368) baseStart_5918368 baseEnd_5918368 := by
    simpa [prefixWord, tailWord_5918368, baseEnd_5918368] using wordTrace_append hprefix tailTrace_5918368
  have hstable : (prefixWord ++ tailWord_5918368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918368).length < 2 ^ (prefixWord ++ tailWord_5918368).sum := by decide
  have hdescent : baseEnd_5918368 < baseStart_5918368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918376 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 5]
def baseStart_5918376 : Nat := 118140960795 + 5918376 * 2 ^ 59
def prefixEnd_5918376 : Nat := 4983230072969 + 3 ^ 40 * 5918376 * 2
def baseEnd_5918376 : Nat := 337663509114893506709099

theorem tailTrace_5918376 : CollatzResearch.WordTrace tailWord_5918376 prefixEnd_5918376 337663509114893506709099 := by
  unfold tailWord_5918376
  simp only [CollatzResearch.WordTrace]
  refine ⟨107930453203371002496875491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143907270937828003329167321 107930453203371002496875491)
  ·
    refine ⟨161895679805056503745313237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107930453203371002496875491 161895679805056503745313237)
    ·
      refine ⟨3794429995431011806530779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 161895679805056503745313237 3794429995431011806530779)
      ·
        refine ⟨5691644993146517709796169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794429995431011806530779 5691644993146517709796169)
        ·
          refine ⟨4268733744859888282347127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691644993146517709796169 4268733744859888282347127)
          ·
            refine ⟨6403100617289832423520691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268733744859888282347127 6403100617289832423520691)
            ·
              refine ⟨9604650925934748635281037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403100617289832423520691 9604650925934748635281037)
              ·
                refine ⟨3601744097225530738230389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604650925934748635281037 3601744097225530738230389)
                ·
                  refine ⟨337663509114893506709099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3601744097225530738230389 337663509114893506709099)
                  ·
                    rfl

theorem cell23_5918376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 5].length) (baseStart_5918376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918376 prefixEnd_5918376 := by exact prefixLift 5918376
  have htrace : WordTrace (prefixWord ++ tailWord_5918376) baseStart_5918376 baseEnd_5918376 := by
    simpa [prefixWord, tailWord_5918376, baseEnd_5918376] using wordTrace_append hprefix tailTrace_5918376
  have hstable : (prefixWord ++ tailWord_5918376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918376).length < 2 ^ (prefixWord ++ tailWord_5918376).sum := by decide
  have hdescent : baseEnd_5918376 < baseStart_5918376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918381 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 10]
def baseStart_5918381 : Nat := 118140960795 + 5918381 * 2 ^ 59
def prefixEnd_5918381 : Nat := 4983230072969 + 3 ^ 40 * 5918381 * 2
def baseEnd_5918381 : Nat := 337663794381923782313263

theorem tailTrace_5918381 : CollatzResearch.WordTrace tailWord_5918381 prefixEnd_5918381 337663794381923782313263 := by
  unfold tailWord_5918381
  simp only [CollatzResearch.WordTrace]
  refine ⟨215861088771723890847682997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143907392514482593898455331 215861088771723890847682997)
  ·
    refine ⟨20236977072349114766970281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215861088771723890847682997 20236977072349114766970281)
    ·
      refine ⟨15177732804261836075227711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20236977072349114766970281 15177732804261836075227711)
      ·
        refine ⟨22766599206392754112841567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15177732804261836075227711 22766599206392754112841567)
        ·
          refine ⟨34149898809589131169262351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22766599206392754112841567 34149898809589131169262351)
          ·
            refine ⟨51224848214383696753893527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34149898809589131169262351 51224848214383696753893527)
            ·
              refine ⟨76837272321575545130840291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51224848214383696753893527 76837272321575545130840291)
              ·
                refine ⟨115255908482363317696260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76837272321575545130840291 115255908482363317696260437)
                ·
                  refine ⟨337663794381923782313263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 115255908482363317696260437 337663794381923782313263)
                  ·
                    rfl

theorem cell23_5918381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_5918381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918381 prefixEnd_5918381 := by exact prefixLift 5918381
  have htrace : WordTrace (prefixWord ++ tailWord_5918381) baseStart_5918381 baseEnd_5918381 := by
    simpa [prefixWord, tailWord_5918381, baseEnd_5918381] using wordTrace_append hprefix tailTrace_5918381
  have hstable : (prefixWord ++ tailWord_5918381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918381).length < 2 ^ (prefixWord ++ tailWord_5918381).sum := by decide
  have hdescent : baseEnd_5918381 < baseStart_5918381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918461 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_5918461 : Nat := 118140960795 + 5918461 * 2 ^ 59
def prefixEnd_5918461 : Nat := 4983230072969 + 3 ^ 40 * 5918461 * 2
def baseEnd_5918461 : Nat := 3039015227889673727818999

theorem tailTrace_5918461 : CollatzResearch.WordTrace tailWord_5918461 prefixEnd_5918461 3039015227889673727818999 := by
  unfold tailWord_5918461
  simp only [CollatzResearch.WordTrace]
  refine ⟨215864006611434064510595237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143909337740956043007063491 215864006611434064510595237)
  ·
    refine ⟨40474501239643887095736607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215864006611434064510595237 40474501239643887095736607)
    ·
      refine ⟨60711751859465830643604911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40474501239643887095736607 60711751859465830643604911)
      ·
        refine ⟨91067627789198745965407367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60711751859465830643604911 91067627789198745965407367)
        ·
          refine ⟨136601441683798118948111051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91067627789198745965407367 136601441683798118948111051)
          ·
            refine ⟨204902162525697178422166577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136601441683798118948111051 204902162525697178422166577)
            ·
              refine ⟨153676621894272883816624933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204902162525697178422166577 153676621894272883816624933)
              ·
                refine ⟨28814366605176165715617175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153676621894272883816624933 28814366605176165715617175)
                ·
                  refine ⟨43221549907764248573425763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28814366605176165715617175 43221549907764248573425763)
                  ·
                    refine ⟨64832324861646372860138645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43221549907764248573425763 64832324861646372860138645)
                    ·
                      refine ⟨3039015227889673727818999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64832324861646372860138645 3039015227889673727818999)
                      ·
                        rfl

theorem cell23_5918461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_5918461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918461 prefixEnd_5918461 := by exact prefixLift 5918461
  have htrace : WordTrace (prefixWord ++ tailWord_5918461) baseStart_5918461 baseEnd_5918461 := by
    simpa [prefixWord, tailWord_5918461, baseEnd_5918461] using wordTrace_append hprefix tailTrace_5918461
  have hstable : (prefixWord ++ tailWord_5918461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918461).length < 2 ^ (prefixWord ++ tailWord_5918461).sum := by decide
  have hdescent : baseEnd_5918461 < baseStart_5918461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918478 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5918478 : Nat := 118140960795 + 5918478 * 2 ^ 59
def prefixEnd_5918478 : Nat := 4983230072969 + 3 ^ 40 * 5918478 * 2
def baseEnd_5918478 : Nat := 3039023957060800161306421

theorem tailTrace_5918478 : CollatzResearch.WordTrace tailWord_5918478 prefixEnd_5918478 3039023957060800161306421 := by
  unfold tailWord_5918478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26983078331546559551745511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143909751101581650942642725 26983078331546559551745511)
  ·
    refine ⟨40474617497319839327618267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26983078331546559551745511 40474617497319839327618267)
    ·
      refine ⟨60711926245979758991427401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40474617497319839327618267 60711926245979758991427401)
      ·
        refine ⟨45533944684484819243570551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60711926245979758991427401 45533944684484819243570551)
        ·
          refine ⟨68300917026727228865355827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45533944684484819243570551 68300917026727228865355827)
          ·
            refine ⟨102451375540090843298033741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68300917026727228865355827 102451375540090843298033741)
            ·
              refine ⟨38419265827534066236762653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102451375540090843298033741 38419265827534066236762653)
              ·
                refine ⟨14407224685325274838785995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38419265827534066236762653 14407224685325274838785995)
                ·
                  refine ⟨21610837027987912258178993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14407224685325274838785995 21610837027987912258178993)
                  ·
                    refine ⟨16208127770990934193634245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21610837027987912258178993 16208127770990934193634245)
                    ·
                      refine ⟨3039023957060800161306421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16208127770990934193634245 3039023957060800161306421)
                      ·
                        rfl

theorem cell23_5918478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5918478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918478 prefixEnd_5918478 := by exact prefixLift 5918478
  have htrace : WordTrace (prefixWord ++ tailWord_5918478) baseStart_5918478 baseEnd_5918478 := by
    simpa [prefixWord, tailWord_5918478, baseEnd_5918478] using wordTrace_append hprefix tailTrace_5918478
  have hstable : (prefixWord ++ tailWord_5918478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918478).length < 2 ^ (prefixWord ++ tailWord_5918478).sum := by decide
  have hdescent : baseEnd_5918478 < baseStart_5918478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918511 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_5918511 : Nat := 118140960795 + 5918511 * 2 ^ 59
def prefixEnd_5918511 : Nat := 4983230072969 + 3 ^ 40 * 5918511 * 2
def baseEnd_5918511 : Nat := 3039040901922398532193769

theorem tailTrace_5918511 : CollatzResearch.WordTrace tailWord_5918511 prefixEnd_5918511 3039040901922398532193769 := by
  unfold tailWord_5918511
  simp only [CollatzResearch.WordTrace]
  refine ⟨215865830261252923049915387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143910553507501948699943591 215865830261252923049915387)
  ·
    refine ⟨323798745391879384574873081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215865830261252923049915387 323798745391879384574873081)
    ·
      refine ⟨242849059043909538431154811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323798745391879384574873081 242849059043909538431154811)
      ·
        refine ⟨364273588565864307646732217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242849059043909538431154811 364273588565864307646732217)
        ·
          refine ⟨273205191424398230735049163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364273588565864307646732217 273205191424398230735049163)
          ·
            refine ⟨409807787136597346102573745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273205191424398230735049163 409807787136597346102573745)
            ·
              refine ⟨307355840352448009576930309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409807787136597346102573745 307355840352448009576930309)
              ·
                refine ⟨57629220066084001795674433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307355840352448009576930309 57629220066084001795674433)
                ·
                  refine ⟨43221915049563001346755825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57629220066084001795674433 43221915049563001346755825)
                  ·
                    refine ⟨32416436287172251010066869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43221915049563001346755825 32416436287172251010066869)
                    ·
                      refine ⟨3039040901922398532193769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32416436287172251010066869 3039040901922398532193769)
                      ·
                        rfl

theorem cell23_5918511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_5918511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918511 prefixEnd_5918511 := by exact prefixLift 5918511
  have htrace : WordTrace (prefixWord ++ tailWord_5918511) baseStart_5918511 baseEnd_5918511 := by
    simpa [prefixWord, tailWord_5918511, baseEnd_5918511] using wordTrace_append hprefix tailTrace_5918511
  have hstable : (prefixWord ++ tailWord_5918511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918511).length < 2 ^ (prefixWord ++ tailWord_5918511).sum := by decide
  have hdescent : baseEnd_5918511 < baseStart_5918511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918516 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_5918516 : Nat := 118140960795 + 5918516 * 2 ^ 59
def prefixEnd_5918516 : Nat := 4983230072969 + 3 ^ 40 * 5918516 * 2
def baseEnd_5918516 : Nat := 3039043469325671012631247

theorem tailTrace_5918516 : CollatzResearch.WordTrace tailWord_5918516 prefixEnd_5918516 3039043469325671012631247 := by
  unfold tailWord_5918516
  simp only [CollatzResearch.WordTrace]
  refine ⟨107933006313117404451923701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143910675084156539269231601 107933006313117404451923701)
  ·
    refine ⟨10118719341854756667367847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107933006313117404451923701 10118719341854756667367847)
    ·
      refine ⟨15178079012782135001051771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118719341854756667367847 15178079012782135001051771)
      ·
        refine ⟨22767118519173202501577657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178079012782135001051771 22767118519173202501577657)
        ·
          refine ⟨17075338889379901876183243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22767118519173202501577657 17075338889379901876183243)
          ·
            refine ⟨25613008334069852814274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17075338889379901876183243 25613008334069852814274865)
            ·
              refine ⟨19209756250552389610706149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25613008334069852814274865 19209756250552389610706149)
              ·
                refine ⟨3601829296978573052007403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19209756250552389610706149 3601829296978573052007403)
                ·
                  refine ⟨5402743945467859578011105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601829296978573052007403 5402743945467859578011105)
                  ·
                    refine ⟨4052057959100894683508329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5402743945467859578011105 4052057959100894683508329)
                    ·
                      refine ⟨3039043469325671012631247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052057959100894683508329 3039043469325671012631247)
                      ·
                        rfl

theorem cell23_5918516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_5918516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918516 prefixEnd_5918516 := by exact prefixLift 5918516
  have htrace : WordTrace (prefixWord ++ tailWord_5918516) baseStart_5918516 baseEnd_5918516 := by
    simpa [prefixWord, tailWord_5918516, baseEnd_5918516] using wordTrace_append hprefix tailTrace_5918516
  have hstable : (prefixWord ++ tailWord_5918516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918516).length < 2 ^ (prefixWord ++ tailWord_5918516).sum := by decide
  have hdescent : baseEnd_5918516 < baseStart_5918516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_5918571 : Nat := 118140960795 + 5918571 * 2 ^ 59
def prefixEnd_5918571 : Nat := 4983230072969 + 3 ^ 40 * 5918571 * 2
def baseEnd_5918571 : Nat := 3039071710761668297443493

theorem tailTrace_5918571 : CollatzResearch.WordTrace tailWord_5918571 prefixEnd_5918571 3039071710761668297443493 := by
  unfold tailWord_5918571
  simp only [CollatzResearch.WordTrace]
  refine ⟨215868018641035553297099567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143912012427357035531399711 215868018641035553297099567)
  ·
    refine ⟨323802027961553329945649351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215868018641035553297099567 323802027961553329945649351)
    ·
      refine ⟨485703041942329994918474027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323802027961553329945649351 485703041942329994918474027)
      ·
        refine ⟨728554562913494992377711041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485703041942329994918474027 728554562913494992377711041)
        ·
          refine ⟨546415922185121244283283281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728554562913494992377711041 546415922185121244283283281)
          ·
            refine ⟨409811941638840933212462461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546415922185121244283283281 409811941638840933212462461)
            ·
              refine ⟨153679478114565349954673423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409811941638840933212462461 153679478114565349954673423)
              ·
                refine ⟨230519217171848024932010135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153679478114565349954673423 230519217171848024932010135)
                ·
                  refine ⟨345778825757772037398015203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230519217171848024932010135 345778825757772037398015203)
                  ·
                    refine ⟨518668238636658056097022805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345778825757772037398015203 518668238636658056097022805)
                    ·
                      refine ⟨3039071710761668297443493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 518668238636658056097022805 3039071710761668297443493)
                      ·
                        rfl

theorem cell23_5918571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_5918571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918571 prefixEnd_5918571 := by exact prefixLift 5918571
  have htrace : WordTrace (prefixWord ++ tailWord_5918571) baseStart_5918571 baseEnd_5918571 := by
    simpa [prefixWord, tailWord_5918571, baseEnd_5918571] using wordTrace_append hprefix tailTrace_5918571
  have hstable : (prefixWord ++ tailWord_5918571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918571).length < 2 ^ (prefixWord ++ tailWord_5918571).sum := by decide
  have hdescent : baseEnd_5918571 < baseStart_5918571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918572 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_5918572 : Nat := 118140960795 + 5918572 * 2 ^ 59
def prefixEnd_5918572 : Nat := 4983230072969 + 3 ^ 40 * 5918572 * 2
def baseEnd_5918572 : Nat := 3039072224242322793530989

theorem tailTrace_5918572 : CollatzResearch.WordTrace tailWord_5918572 prefixEnd_5918572 3039072224242322793530989 := by
  unfold tailWord_5918572
  simp only [CollatzResearch.WordTrace]
  refine ⟨107934027557015965233942985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143912036742687953645257313 107934027557015965233942985)
  ·
    refine ⟨80950520667761973925457239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107934027557015965233942985 80950520667761973925457239)
    ·
      refine ⟨121425781001642960888185859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80950520667761973925457239 121425781001642960888185859)
      ·
        refine ⟨182138671502464441332278789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121425781001642960888185859 182138671502464441332278789)
        ·
          refine ⟨34151000906712082749802273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182138671502464441332278789 34151000906712082749802273)
          ·
            refine ⟨25613250680034062062351705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34151000906712082749802273 25613250680034062062351705)
            ·
              refine ⟨19209938010025546546763779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25613250680034062062351705 19209938010025546546763779)
              ·
                refine ⟨28814907015038319820145669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19209938010025546546763779 28814907015038319820145669)
                ·
                  refine ⟨5402795065319684966277313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28814907015038319820145669 5402795065319684966277313)
                  ·
                    refine ⟨4052096298989763724707985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5402795065319684966277313 4052096298989763724707985)
                    ·
                      refine ⟨3039072224242322793530989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052096298989763724707985 3039072224242322793530989)
                      ·
                        rfl

theorem cell23_5918572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_5918572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918572 prefixEnd_5918572 := by exact prefixLift 5918572
  have htrace : WordTrace (prefixWord ++ tailWord_5918572) baseStart_5918572 baseEnd_5918572 := by
    simpa [prefixWord, tailWord_5918572, baseEnd_5918572] using wordTrace_append hprefix tailTrace_5918572
  have hstable : (prefixWord ++ tailWord_5918572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918572).length < 2 ^ (prefixWord ++ tailWord_5918572).sum := by decide
  have hdescent : baseEnd_5918572 < baseStart_5918572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918593 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5918593 : Nat := 118140960795 + 5918593 * 2 ^ 59
def prefixEnd_5918593 : Nat := 4983230072969 + 3 ^ 40 * 5918593 * 2
def baseEnd_5918593 : Nat := 3039083007336067211368393

theorem tailTrace_5918593 : CollatzResearch.WordTrace tailWord_5918593 prefixEnd_5918593 3039083007336067211368393 := by
  unfold tailWord_5918593
  simp only [CollatzResearch.WordTrace]
  refine ⟨215868821046955851054400433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143912547364637234036266955 215868821046955851054400433)
  ·
    refine ⟨161901615785216888290800325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215868821046955851054400433 161901615785216888290800325)
    ·
      refine ⟨30356552959728166554525061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161901615785216888290800325 30356552959728166554525061)
      ·
        refine ⟨5691853679949031228973449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30356552959728166554525061 5691853679949031228973449)
        ·
          refine ⟨4268890259961773421730087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691853679949031228973449 4268890259961773421730087)
          ·
            refine ⟨6403335389942660132595131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268890259961773421730087 6403335389942660132595131)
            ·
              refine ⟨9605003084913990198892697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403335389942660132595131 9605003084913990198892697)
              ·
                refine ⟨7203752313685492649169523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605003084913990198892697 7203752313685492649169523)
                ·
                  refine ⟨10805628470528238973754285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203752313685492649169523 10805628470528238973754285)
                  ·
                    refine ⟨4052110676448089615157857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10805628470528238973754285 4052110676448089615157857)
                    ·
                      refine ⟨3039083007336067211368393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052110676448089615157857 3039083007336067211368393)
                      ·
                        rfl

theorem cell23_5918593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5918593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918593 prefixEnd_5918593 := by exact prefixLift 5918593
  have htrace : WordTrace (prefixWord ++ tailWord_5918593) baseStart_5918593 baseEnd_5918593 := by
    simpa [prefixWord, tailWord_5918593, baseEnd_5918593] using wordTrace_append hprefix tailTrace_5918593
  have hstable : (prefixWord ++ tailWord_5918593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918593).length < 2 ^ (prefixWord ++ tailWord_5918593).sum := by decide
  have hdescent : baseEnd_5918593 < baseStart_5918593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918608 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_5918608 : Nat := 118140960795 + 5918608 * 2 ^ 59
def prefixEnd_5918608 : Nat := 4983230072969 + 3 ^ 40 * 5918608 * 2
def baseEnd_5918608 : Nat := 1013030236515294884226941

theorem tailTrace_5918608 : CollatzResearch.WordTrace tailWord_5918608 prefixEnd_5918608 1013030236515294884226941 := by
  unfold tailWord_5918608
  simp only [CollatzResearch.WordTrace]
  refine ⟨107934684070950754308098239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143912912094601005744130985 107934684070950754308098239)
  ·
    refine ⟨161902026106426131462147359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107934684070950754308098239 161902026106426131462147359)
    ·
      refine ⟨242853039159639197193221039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161902026106426131462147359 242853039159639197193221039)
      ·
        refine ⟨364279558739458795789831559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242853039159639197193221039 364279558739458795789831559)
        ·
          refine ⟨546419338109188193684747339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364279558739458795789831559 546419338109188193684747339)
          ·
            refine ⟨819629007163782290527121009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546419338109188193684747339 819629007163782290527121009)
            ·
              refine ⟨614721755372836717895340757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819629007163782290527121009 614721755372836717895340757)
              ·
                refine ⟨14407541141550860575672049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 614721755372836717895340757 14407541141550860575672049)
                ·
                  refine ⟨10805655856163145431754037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14407541141550860575672049 10805655856163145431754037)
                  ·
                    refine ⟨1013030236515294884226941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10805655856163145431754037 1013030236515294884226941)
                    ·
                      rfl

theorem cell23_5918608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_5918608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918608 prefixEnd_5918608 := by exact prefixLift 5918608
  have htrace : WordTrace (prefixWord ++ tailWord_5918608) baseStart_5918608 baseEnd_5918608 := by
    simpa [prefixWord, tailWord_5918608, baseEnd_5918608] using wordTrace_append hprefix tailTrace_5918608
  have hstable : (prefixWord ++ tailWord_5918608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918608).length < 2 ^ (prefixWord ++ tailWord_5918608).sum := by decide
  have hdescent : baseEnd_5918608 < baseStart_5918608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918655 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 3, 4]
def baseStart_5918655 : Nat := 118140960795 + 5918655 * 2 ^ 59
def prefixEnd_5918655 : Nat := 4983230072969 + 3 ^ 40 * 5918655 * 2
def baseEnd_5918655 : Nat := 1013038281045548656264369

theorem tailTrace_5918655 : CollatzResearch.WordTrace tailWord_5918655 prefixEnd_5918655 1013038281045548656264369 := by
  unfold tailWord_5918655
  simp only [CollatzResearch.WordTrace]
  refine ⟨215871082372731235643157419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143914054915154157095438279 215871082372731235643157419)
  ·
    refine ⟨323806623559096853464736129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215871082372731235643157419 323806623559096853464736129)
    ·
      refine ⟨242854967669322640098552097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323806623559096853464736129 242854967669322640098552097)
      ·
        refine ⟨182141225751991980073914073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242854967669322640098552097 182141225751991980073914073)
        ·
          refine ⟨136605919313993985055435555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182141225751991980073914073 136605919313993985055435555)
          ·
            refine ⟨204908878970990977583153333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136605919313993985055435555 204908878970990977583153333)
            ·
              refine ⟨19210207403530404148420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204908878970990977583153333 19210207403530404148420625)
              ·
                refine ⟨14407655552647803111315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19210207403530404148420625 14407655552647803111315469)
                ·
                  refine ⟨5402870832242926166743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14407655552647803111315469 5402870832242926166743301)
                  ·
                    refine ⟨1013038281045548656264369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402870832242926166743301 1013038281045548656264369)
                    ·
                      rfl

theorem cell23_5918655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_5918655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918655 prefixEnd_5918655 := by exact prefixLift 5918655
  have htrace : WordTrace (prefixWord ++ tailWord_5918655) baseStart_5918655 baseEnd_5918655 := by
    simpa [prefixWord, tailWord_5918655, baseEnd_5918655] using wordTrace_append hprefix tailTrace_5918655
  have hstable : (prefixWord ++ tailWord_5918655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918655).length < 2 ^ (prefixWord ++ tailWord_5918655).sum := by decide
  have hdescent : baseEnd_5918655 < baseStart_5918655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918672 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 1, 4]
def baseStart_5918672 : Nat := 118140960795 + 5918672 * 2 ^ 59
def prefixEnd_5918672 : Nat := 4983230072969 + 3 ^ 40 * 5918672 * 2
def baseEnd_5918672 : Nat := 1013041190769257467426843

theorem tailTrace_5918672 : CollatzResearch.WordTrace tailWord_5918672 prefixEnd_5918672 1013041190769257467426843 := by
  unfold tailWord_5918672
  simp only [CollatzResearch.WordTrace]
  refine ⟨107935851206834823773263135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143914468275779765031017513 107935851206834823773263135)
  ·
    refine ⟨161903776810252235659894703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107935851206834823773263135 161903776810252235659894703)
    ·
      refine ⟨242855665215378353489842055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161903776810252235659894703 242855665215378353489842055)
      ·
        refine ⟨364283497823067530234763083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242855665215378353489842055 364283497823067530234763083)
        ·
          refine ⟨546425246734601295352144625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364283497823067530234763083 546425246734601295352144625)
          ·
            refine ⟨409818935050950971514108469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546425246734601295352144625 409818935050950971514108469)
            ·
              refine ⟨38420525161026653579447669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 409818935050950971514108469 38420525161026653579447669)
              ·
                refine ⟨3601924233846248773073219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38420525161026653579447669 3601924233846248773073219)
                ·
                  refine ⟨5402886350769373159609829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601924233846248773073219 5402886350769373159609829)
                  ·
                    refine ⟨1013041190769257467426843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402886350769373159609829 1013041190769257467426843)
                    ·
                      rfl

theorem cell23_5918672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_5918672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918672 prefixEnd_5918672 := by exact prefixLift 5918672
  have htrace : WordTrace (prefixWord ++ tailWord_5918672) baseStart_5918672 baseEnd_5918672 := by
    simpa [prefixWord, tailWord_5918672, baseEnd_5918672] using wordTrace_append hprefix tailTrace_5918672
  have hstable : (prefixWord ++ tailWord_5918672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918672).length < 2 ^ (prefixWord ++ tailWord_5918672).sum := by decide
  have hdescent : baseEnd_5918672 < baseStart_5918672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918712 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_5918712 : Nat := 118140960795 + 5918712 * 2 ^ 59
def prefixEnd_5918712 : Nat := 4983230072969 + 3 ^ 40 * 5918712 * 2
def baseEnd_5918712 : Nat := 3039144111533952245780345

theorem tailTrace_5918712 : CollatzResearch.WordTrace tailWord_5918712 prefixEnd_5918712 3039144111533952245780345 := by
  unfold tailWord_5918712
  simp only [CollatzResearch.WordTrace]
  refine ⟨107936580666762367188991195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143915440889016489585321593 107936580666762367188991195)
  ·
    refine ⟨161904871000143550783486793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107936580666762367188991195 161904871000143550783486793)
    ·
      refine ⟨121428653250107663087615095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161904871000143550783486793 121428653250107663087615095)
      ·
        refine ⟨182142979875161494631422643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121428653250107663087615095 182142979875161494631422643)
        ·
          refine ⟨273214469812742241947133965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182142979875161494631422643 273214469812742241947133965)
          ·
            refine ⟨102455426179778340730175237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273214469812742241947133965 102455426179778340730175237)
            ·
              refine ⟨19210392408708438886907857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102455426179778340730175237 19210392408708438886907857)
              ·
                refine ⟨14407794306531329165180893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19210392408708438886907857 14407794306531329165180893)
                ·
                  refine ⟨5402922864949248436942835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14407794306531329165180893 5402922864949248436942835)
                  ·
                    refine ⟨8104384297423872655414253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5402922864949248436942835 8104384297423872655414253)
                    ·
                      refine ⟨3039144111533952245780345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104384297423872655414253 3039144111533952245780345)
                      ·
                        rfl

theorem cell23_5918712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_5918712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918712 prefixEnd_5918712 := by exact prefixLift 5918712
  have htrace : WordTrace (prefixWord ++ tailWord_5918712) baseStart_5918712 baseEnd_5918712 := by
    simpa [prefixWord, tailWord_5918712, baseEnd_5918712] using wordTrace_append hprefix tailTrace_5918712
  have hstable : (prefixWord ++ tailWord_5918712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918712).length < 2 ^ (prefixWord ++ tailWord_5918712).sum := by decide
  have hdescent : baseEnd_5918712 < baseStart_5918712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918715 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 1, 5]
def baseStart_5918715 : Nat := 118140960795 + 5918715 * 2 ^ 59
def prefixEnd_5918715 : Nat := 4983230072969 + 3 ^ 40 * 5918715 * 2
def baseEnd_5918715 : Nat := 1013048550658638578014277

theorem tailTrace_5918715 : CollatzResearch.WordTrace tailWord_5918715 prefixEnd_5918715 1013048550658638578014277 := by
  unfold tailWord_5918715
  simp only [CollatzResearch.WordTrace]
  refine ⟨215873270752513865890341599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143915513835009243926894399 215873270752513865890341599)
  ·
    refine ⟨323809906128770798835512399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215873270752513865890341599 323809906128770798835512399)
    ·
      refine ⟨485714859193156198253268599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323809906128770798835512399 485714859193156198253268599)
      ·
        refine ⟨728572288789734297379902899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485714859193156198253268599 728572288789734297379902899)
        ·
          refine ⟨1092858433184601446069854349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728572288789734297379902899 1092858433184601446069854349)
          ·
            refine ⟨409821912444225542276195381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1092858433184601446069854349 409821912444225542276195381)
            ·
              refine ⟨38420804291646144588393317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 409821912444225542276195381 38420804291646144588393317)
              ·
                refine ⟨7203900804683652110323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38420804291646144588393317 7203900804683652110323747)
                ·
                  refine ⟨10805851207025478165485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203900804683652110323747 10805851207025478165485621)
                  ·
                    refine ⟨1013048550658638578014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10805851207025478165485621 1013048550658638578014277)
                    ·
                      rfl

theorem cell23_5918715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 5].length) (baseStart_5918715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918715 prefixEnd_5918715 := by exact prefixLift 5918715
  have htrace : WordTrace (prefixWord ++ tailWord_5918715) baseStart_5918715 baseEnd_5918715 := by
    simpa [prefixWord, tailWord_5918715, baseEnd_5918715] using wordTrace_append hprefix tailTrace_5918715
  have hstable : (prefixWord ++ tailWord_5918715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918715).length < 2 ^ (prefixWord ++ tailWord_5918715).sum := by decide
  have hdescent : baseEnd_5918715 < baseStart_5918715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918733 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5918733 : Nat := 118140960795 + 5918733 * 2 ^ 59
def prefixEnd_5918733 : Nat := 4983230072969 + 3 ^ 40 * 5918733 * 2
def baseEnd_5918733 : Nat := 3039154894627696663617749

theorem tailTrace_5918733 : CollatzResearch.WordTrace tailWord_5918733 prefixEnd_5918733 3039154894627696663617749 := by
  unfold tailWord_5918733
  simp only [CollatzResearch.WordTrace]
  refine ⟨215873927266448654964496853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143915951510965769976331235 215873927266448654964496853)
  ·
    refine ⟨5059545170307390350730395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 215873927266448654964496853 5059545170307390350730395)
    ·
      refine ⟨7589317755461085526095593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059545170307390350730395 7589317755461085526095593)
      ·
        refine ⟨5691988316595814144571695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7589317755461085526095593 5691988316595814144571695)
        ·
          refine ⟨8537982474893721216857543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691988316595814144571695 8537982474893721216857543)
          ·
            refine ⟨12806973712340581825286315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537982474893721216857543 12806973712340581825286315)
            ·
              refine ⟨19210460568510872737929473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12806973712340581825286315 19210460568510872737929473)
              ·
                refine ⟨14407845426383154553447105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19210460568510872737929473 14407845426383154553447105)
                ·
                  refine ⟨10805884069787365915085329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14407845426383154553447105 10805884069787365915085329)
                  ·
                    refine ⟨8104413052340524436313997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10805884069787365915085329 8104413052340524436313997)
                    ·
                      refine ⟨3039154894627696663617749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104413052340524436313997 3039154894627696663617749)
                      ·
                        rfl

theorem cell23_5918733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5918733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918733 prefixEnd_5918733 := by exact prefixLift 5918733
  have htrace : WordTrace (prefixWord ++ tailWord_5918733) baseStart_5918733 baseEnd_5918733 := by
    simpa [prefixWord, tailWord_5918733, baseEnd_5918733] using wordTrace_append hprefix tailTrace_5918733
  have hstable : (prefixWord ++ tailWord_5918733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918733).length < 2 ^ (prefixWord ++ tailWord_5918733).sum := by decide
  have hdescent : baseEnd_5918733 < baseStart_5918733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918740 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5918740 : Nat := 118140960795 + 5918740 * 2 ^ 59
def prefixEnd_5918740 : Nat := 4983230072969 + 3 ^ 40 * 5918740 * 2
def baseEnd_5918740 : Nat := 1013052829664092712076739

theorem tailTrace_5918740 : CollatzResearch.WordTrace tailWord_5918740 prefixEnd_5918740 1013052829664092712076739 := by
  unfold tailWord_5918740
  simp only [CollatzResearch.WordTrace]
  refine ⟨107937091288711647580000837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143916121718282196773334449 107937091288711647580000837)
  ·
    refine ⟨20238204616633433921250157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107937091288711647580000837 20238204616633433921250157)
    ·
      refine ⟨7589326731237537720468809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20238204616633433921250157 7589326731237537720468809)
      ·
        refine ⟨5691995048428153290351607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7589326731237537720468809 5691995048428153290351607)
        ·
          refine ⟨8537992572642229935527411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691995048428153290351607 8537992572642229935527411)
          ·
            refine ⟨12806988858963344903291117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537992572642229935527411 12806988858963344903291117)
            ·
              refine ⟨4802620822111254338734169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12806988858963344903291117 4802620822111254338734169)
              ·
                refine ⟨3601965616583440754050627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802620822111254338734169 3601965616583440754050627)
                ·
                  refine ⟨5402948424875161131075941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601965616583440754050627 5402948424875161131075941)
                  ·
                    refine ⟨1013052829664092712076739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5402948424875161131075941 1013052829664092712076739)
                    ·
                      rfl

theorem cell23_5918740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5918740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918740 prefixEnd_5918740 := by exact prefixLift 5918740
  have htrace : WordTrace (prefixWord ++ tailWord_5918740) baseStart_5918740 baseEnd_5918740 := by
    simpa [prefixWord, tailWord_5918740, baseEnd_5918740] using wordTrace_append hprefix tailTrace_5918740
  have hstable : (prefixWord ++ tailWord_5918740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918740).length < 2 ^ (prefixWord ++ tailWord_5918740).sum := by decide
  have hdescent : baseEnd_5918740 < baseStart_5918740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918755 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_5918755 : Nat := 118140960795 + 5918755 * 2 ^ 59
def prefixEnd_5918755 : Nat := 4983230072969 + 3 ^ 40 * 5918755 * 2
def baseEnd_5918755 : Nat := 3039166191202095577542647

theorem tailTrace_5918755 : CollatzResearch.WordTrace tailWord_5918755 prefixEnd_5918755 3039166191202095577542647 := by
  unfold tailWord_5918755
  simp only [CollatzResearch.WordTrace]
  refine ⟨215874729672368952721797719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143916486448245968481198479 215874729672368952721797719)
  ·
    refine ⟨323812094508553429082696579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215874729672368952721797719 323812094508553429082696579)
    ·
      refine ⟨485718141762830143624044869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323812094508553429082696579 485718141762830143624044869)
      ·
        refine ⟨91072151580530651929508413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 485718141762830143624044869 91072151580530651929508413)
        ·
          refine ⟨34152056842698994473565655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91072151580530651929508413 34152056842698994473565655)
          ·
            refine ⟨51228085264048491710348483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34152056842698994473565655 51228085264048491710348483)
            ·
              refine ⟨76842127896072737565522725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51228085264048491710348483 76842127896072737565522725)
              ·
                refine ⟨14407898980513638293535511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76842127896072737565522725 14407898980513638293535511)
                ·
                  refine ⟨21611848470770457440303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14407898980513638293535511 21611848470770457440303267)
                  ·
                    refine ⟨32417772706155686160454901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21611848470770457440303267 32417772706155686160454901)
                    ·
                      refine ⟨3039166191202095577542647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32417772706155686160454901 3039166191202095577542647)
                      ·
                        rfl

theorem cell23_5918755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_5918755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918755 prefixEnd_5918755 := by exact prefixLift 5918755
  have htrace : WordTrace (prefixWord ++ tailWord_5918755) baseStart_5918755 baseEnd_5918755 := by
    simpa [prefixWord, tailWord_5918755, baseEnd_5918755] using wordTrace_append hprefix tailTrace_5918755
  have hstable : (prefixWord ++ tailWord_5918755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918755).length < 2 ^ (prefixWord ++ tailWord_5918755).sum := by decide
  have hdescent : baseEnd_5918755 < baseStart_5918755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918769 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 4]
def baseStart_5918769 : Nat := 118140960795 + 5918769 * 2 ^ 59
def prefixEnd_5918769 : Nat := 4983230072969 + 3 ^ 40 * 5918769 * 2
def baseEnd_5918769 : Nat := 3039173379931258522767583

theorem tailTrace_5918769 : CollatzResearch.WordTrace tailWord_5918769 prefixEnd_5918769 3039173379931258522767583 := by
  unfold tailWord_5918769
  simp only [CollatzResearch.WordTrace]
  refine ⟨215875240294318233112807361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143916826862878822075204907 215875240294318233112807361)
  ·
    refine ⟨161906430220738674834605521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215875240294318233112807361 161906430220738674834605521)
    ·
      refine ⟨121429822665554006125954141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161906430220738674834605521 121429822665554006125954141)
      ·
        refine ⟨45536183499582752297232803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121429822665554006125954141 45536183499582752297232803)
        ·
          refine ⟨68304275249374128445849205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45536183499582752297232803 68304275249374128445849205)
          ·
            refine ⟨6403525804628824541798363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68304275249374128445849205 6403525804628824541798363)
            ·
              refine ⟨9605288706943236812697545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403525804628824541798363 9605288706943236812697545)
              ·
                refine ⟨7203966530207427609523159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605288706943236812697545 7203966530207427609523159)
                ·
                  refine ⟨10805949795311141414284739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203966530207427609523159 10805949795311141414284739)
                  ·
                    refine ⟨16208924692966712121427109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10805949795311141414284739 16208924692966712121427109)
                    ·
                      refine ⟨3039173379931258522767583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16208924692966712121427109 3039173379931258522767583)
                      ·
                        rfl

theorem cell23_5918769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_5918769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918769 prefixEnd_5918769 := by exact prefixLift 5918769
  have htrace : WordTrace (prefixWord ++ tailWord_5918769) baseStart_5918769 baseEnd_5918769 := by
    simpa [prefixWord, tailWord_5918769, baseEnd_5918769] using wordTrace_append hprefix tailTrace_5918769
  have hstable : (prefixWord ++ tailWord_5918769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918769).length < 2 ^ (prefixWord ++ tailWord_5918769).sum := by decide
  have hdescent : baseEnd_5918769 < baseStart_5918769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918805 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5918805 : Nat := 118140960795 + 5918805 * 2 ^ 59
def prefixEnd_5918805 : Nat := 4983230072969 + 3 ^ 40 * 5918805 * 2
def baseEnd_5918805 : Nat := 1013063955078273460639139

theorem tailTrace_5918805 : CollatzResearch.WordTrace tailWord_5918805 prefixEnd_5918805 1013063955078273460639139 := by
  unfold tailWord_5918805
  simp only [CollatzResearch.WordTrace]
  refine ⟨215876553322187811261117869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143917702214791874174078579 215876553322187811261117869)
  ·
    refine ⟨80953707495820429222919201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215876553322187811261117869 80953707495820429222919201)
    ·
      refine ⟨60715280621865321917189401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80953707495820429222919201 60715280621865321917189401)
      ·
        refine ⟨45536460466398991437892051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60715280621865321917189401 45536460466398991437892051)
        ·
          refine ⟨68304690699598487156838077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45536460466398991437892051 68304690699598487156838077)
          ·
            refine ⟨25614259012349432683814279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68304690699598487156838077 25614259012349432683814279)
            ·
              refine ⟨38421388518524149025721419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614259012349432683814279 38421388518524149025721419)
              ·
                refine ⟨57632082777786223538582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38421388518524149025721419 57632082777786223538582129)
                ·
                  refine ⟨43224062083339667653936597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57632082777786223538582129 43224062083339667653936597)
                  ·
                    refine ⟨1013063955078273460639139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43224062083339667653936597 1013063955078273460639139)
                    ·
                      rfl

theorem cell23_5918805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5918805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918805 prefixEnd_5918805 := by exact prefixLift 5918805
  have htrace : WordTrace (prefixWord ++ tailWord_5918805) baseStart_5918805 baseEnd_5918805 := by
    simpa [prefixWord, tailWord_5918805, baseEnd_5918805] using wordTrace_append hprefix tailTrace_5918805
  have hstable : (prefixWord ++ tailWord_5918805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918805).length < 2 ^ (prefixWord ++ tailWord_5918805).sum := by decide
  have hdescent : baseEnd_5918805 < baseStart_5918805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918806 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5918806 : Nat := 118140960795 + 5918806 * 2 ^ 59
def prefixEnd_5918806 : Nat := 4983230072969 + 3 ^ 40 * 5918806 * 2
def baseEnd_5918806 : Nat := 3039192378715474878004913

theorem tailTrace_5918806 : CollatzResearch.WordTrace tailWord_5918806 prefixEnd_5918806 3039192378715474878004913 := by
  unfold tailWord_5918806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492286862199011776994017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143917726530122792287936181 13492286862199011776994017)
  ·
    refine ⟨10119215146649258832745513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13492286862199011776994017 10119215146649258832745513)
    ·
      refine ⟨7589411359986944124559135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10119215146649258832745513 7589411359986944124559135)
      ·
        refine ⟨11384117039980416186838703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589411359986944124559135 11384117039980416186838703)
        ·
          refine ⟨17076175559970624280258055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384117039980416186838703 17076175559970624280258055)
          ·
            refine ⟨25614263339955936420387083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076175559970624280258055 25614263339955936420387083)
            ·
              refine ⟨38421395009933904630580625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614263339955936420387083 38421395009933904630580625)
              ·
                refine ⟨28816046257450428472935469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38421395009933904630580625 28816046257450428472935469)
                ·
                  refine ⟨10806017346543910677350801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28816046257450428472935469 10806017346543910677350801)
                  ·
                    refine ⟨8104513009907933008013101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10806017346543910677350801 8104513009907933008013101)
                    ·
                      refine ⟨3039192378715474878004913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104513009907933008013101 3039192378715474878004913)
                      ·
                        rfl

theorem cell23_5918806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5918806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918806 prefixEnd_5918806 := by exact prefixLift 5918806
  have htrace : WordTrace (prefixWord ++ tailWord_5918806) baseStart_5918806 baseEnd_5918806 := by
    simpa [prefixWord, tailWord_5918806, baseEnd_5918806] using wordTrace_append hprefix tailTrace_5918806
  have hstable : (prefixWord ++ tailWord_5918806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918806).length < 2 ^ (prefixWord ++ tailWord_5918806).sum := by decide
  have hdescent : baseEnd_5918806 < baseStart_5918806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918819 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 3]
def baseStart_5918819 : Nat := 118140960795 + 5918819 * 2 ^ 59
def prefixEnd_5918819 : Nat := 4983230072969 + 3 ^ 40 * 5918819 * 2
def baseEnd_5918819 : Nat := 3039199053963983327142353

theorem tailTrace_5918819 : CollatzResearch.WordTrace tailWord_5918819 prefixEnd_5918819 3039199053963983327142353 := by
  unfold tailWord_5918819
  simp only [CollatzResearch.WordTrace]
  refine ⟨215877063944137091652127511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143918042629424727768085007 215877063944137091652127511)
  ·
    refine ⟨323815595916205637478191267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215877063944137091652127511 323815595916205637478191267)
    ·
      refine ⟨485723393874308456217286901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323815595916205637478191267 485723393874308456217286901)
      ·
        refine ⟨45536568175716417770370647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 485723393874308456217286901 45536568175716417770370647)
        ·
          refine ⟨68304852263574626655555971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45536568175716417770370647 68304852263574626655555971)
          ·
            refine ⟨102457278395361939983333957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68304852263574626655555971 102457278395361939983333957)
            ·
              refine ⟨19210739699130363746875117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102457278395361939983333957 19210739699130363746875117)
              ·
                refine ⟨7204027387173886405078169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19210739699130363746875117 7204027387173886405078169)
                ·
                  refine ⟨5403020540380414803808627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7204027387173886405078169 5403020540380414803808627)
                  ·
                    refine ⟨8104530810570622205712941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5403020540380414803808627 8104530810570622205712941)
                    ·
                      refine ⟨3039199053963983327142353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104530810570622205712941 3039199053963983327142353)
                      ·
                        rfl

theorem cell23_5918819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_5918819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918819 prefixEnd_5918819 := by exact prefixLift 5918819
  have htrace : WordTrace (prefixWord ++ tailWord_5918819) baseStart_5918819 baseEnd_5918819 := by
    simpa [prefixWord, tailWord_5918819, baseEnd_5918819] using wordTrace_append hprefix tailTrace_5918819
  have hstable : (prefixWord ++ tailWord_5918819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918819).length < 2 ^ (prefixWord ++ tailWord_5918819).sum := by decide
  have hdescent : baseEnd_5918819 < baseStart_5918819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918825 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_5918825 : Nat := 118140960795 + 5918825 * 2 ^ 59
def prefixEnd_5918825 : Nat := 4983230072969 + 3 ^ 40 * 5918825 * 2
def baseEnd_5918825 : Nat := 3039202134847910303667325

theorem tailTrace_5918825 : CollatzResearch.WordTrace tailWord_5918825 prefixEnd_5918825 3039202134847910303667325 := by
  unfold tailWord_5918825
  simp only [CollatzResearch.WordTrace]
  refine ⟨215877282782115354676845929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143918188521410236451230619 215877282782115354676845929)
  ·
    refine ⟨161907962086586516007634447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215877282782115354676845929 161907962086586516007634447)
    ·
      refine ⟨242861943129879774011451671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161907962086586516007634447 242861943129879774011451671)
      ·
        refine ⟨364292914694819661017177507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242861943129879774011451671 364292914694819661017177507)
        ·
          refine ⟨546439372042229491525766261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364292914694819661017177507 546439372042229491525766261)
          ·
            refine ⟨51228691128959014830540587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 546439372042229491525766261 51228691128959014830540587)
            ·
              refine ⟨76843036693438522245810881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51228691128959014830540587 76843036693438522245810881)
              ·
                refine ⟨57632277520078891684358161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76843036693438522245810881 57632277520078891684358161)
                ·
                  refine ⟨43224208140059168763268621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57632277520078891684358161 43224208140059168763268621)
                  ·
                    refine ⟨16209078052522188286225733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43224208140059168763268621 16209078052522188286225733)
                    ·
                      refine ⟨3039202134847910303667325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16209078052522188286225733 3039202134847910303667325)
                      ·
                        rfl

theorem cell23_5918825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_5918825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918825 prefixEnd_5918825 := by exact prefixLift 5918825
  have htrace : WordTrace (prefixWord ++ tailWord_5918825) baseStart_5918825 baseEnd_5918825 := by
    simpa [prefixWord, tailWord_5918825, baseEnd_5918825] using wordTrace_append hprefix tailTrace_5918825
  have hstable : (prefixWord ++ tailWord_5918825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918825).length < 2 ^ (prefixWord ++ tailWord_5918825).sum := by decide
  have hdescent : baseEnd_5918825 < baseStart_5918825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918829 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_5918829 : Nat := 118140960795 + 5918829 * 2 ^ 59
def prefixEnd_5918829 : Nat := 4983230072969 + 3 ^ 40 * 5918829 * 2
def baseEnd_5918829 : Nat := 3039204188770528288017307

theorem tailTrace_5918829 : CollatzResearch.WordTrace tailWord_5918829 prefixEnd_5918829 3039204188770528288017307 := by
  unfold tailWord_5918829
  simp only [CollatzResearch.WordTrace]
  refine ⟨215877428674100863359991541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143918285782733908906661027 215877428674100863359991541)
  ·
    refine ⟨20238508938196955939999207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215877428674100863359991541 20238508938196955939999207)
    ·
      refine ⟨30357763407295433909998811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20238508938196955939999207 30357763407295433909998811)
      ·
        refine ⟨45536645110943150864998217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30357763407295433909998811 45536645110943150864998217)
        ·
          refine ⟨34152483833207363148748663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45536645110943150864998217 34152483833207363148748663)
          ·
            refine ⟨51228725749811044723122995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34152483833207363148748663 51228725749811044723122995)
            ·
              refine ⟨76843088624716567084684493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51228725749811044723122995 76843088624716567084684493)
              ·
                refine ⟨28816158234268712656756685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76843088624716567084684493 28816158234268712656756685)
                ·
                  refine ⟨10806059337850767246283757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28816158234268712656756685 10806059337850767246283757)
                  ·
                    refine ⟨4052272251694037717356409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10806059337850767246283757 4052272251694037717356409)
                    ·
                      refine ⟨3039204188770528288017307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052272251694037717356409 3039204188770528288017307)
                      ·
                        rfl

theorem cell23_5918829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_5918829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918829 prefixEnd_5918829 := by exact prefixLift 5918829
  have htrace : WordTrace (prefixWord ++ tailWord_5918829) baseStart_5918829 baseEnd_5918829 := by
    simpa [prefixWord, tailWord_5918829, baseEnd_5918829] using wordTrace_append hprefix tailTrace_5918829
  have hstable : (prefixWord ++ tailWord_5918829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918829).length < 2 ^ (prefixWord ++ tailWord_5918829).sum := by decide
  have hdescent : baseEnd_5918829 < baseStart_5918829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918912 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_5918912 : Nat := 118140960795 + 5918912 * 2 ^ 59
def prefixEnd_5918912 : Nat := 4983230072969 + 3 ^ 40 * 5918912 * 2
def baseEnd_5918912 : Nat := 1013082269221617154426475

theorem tailTrace_5918912 : CollatzResearch.WordTrace tailWord_5918912 prefixEnd_5918912 1013082269221617154426475 := by
  unfold tailWord_5918912
  simp only [CollatzResearch.WordTrace]
  refine ⟨107940227966400084267631495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143920303955200112356841993 107940227966400084267631495)
  ·
    refine ⟨161910341949600126401447243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107940227966400084267631495 161910341949600126401447243)
    ·
      refine ⟨242865512924400189602170865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161910341949600126401447243 242865512924400189602170865)
      ·
        refine ⟨182149134693300142201628149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242865512924400189602170865 182149134693300142201628149)
        ·
          refine ⟨17076481377496888331402639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182149134693300142201628149 17076481377496888331402639)
          ·
            refine ⟨25614722066245332497103959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076481377496888331402639 25614722066245332497103959)
            ·
              refine ⟨38422083099367998745655939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614722066245332497103959 38422083099367998745655939)
              ·
                refine ⟨57633124649051998118483909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38422083099367998745655939 57633124649051998118483909)
                ·
                  refine ⟨10806210871697249647215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57633124649051998118483909 10806210871697249647215733)
                  ·
                    refine ⟨1013082269221617154426475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10806210871697249647215733 1013082269221617154426475)
                    ·
                      rfl

theorem cell23_5918912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_5918912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918912 prefixEnd_5918912 := by exact prefixLift 5918912
  have htrace : WordTrace (prefixWord ++ tailWord_5918912) baseStart_5918912 baseEnd_5918912 := by
    simpa [prefixWord, tailWord_5918912, baseEnd_5918912] using wordTrace_append hprefix tailTrace_5918912
  have hstable : (prefixWord ++ tailWord_5918912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918912).length < 2 ^ (prefixWord ++ tailWord_5918912).sum := by decide
  have hdescent : baseEnd_5918912 < baseStart_5918912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918922 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_5918922 : Nat := 118140960795 + 5918922 * 2 ^ 59
def prefixEnd_5918922 : Nat := 4983230072969 + 3 ^ 40 * 5918922 * 2
def baseEnd_5918922 : Nat := 3039251942471396424154379

theorem tailTrace_5918922 : CollatzResearch.WordTrace tailWord_5918922 prefixEnd_5918922 3039251942471396424154379 := by
  unfold tailWord_5918922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53970205165690985060781755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143920547108509293495418013 53970205165690985060781755)
  ·
    refine ⟨80955307748536477591172633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53970205165690985060781755 80955307748536477591172633)
    ·
      refine ⟨60716480811402358193379475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80955307748536477591172633 60716480811402358193379475)
      ·
        refine ⟨91074721217103537290069213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60716480811402358193379475 91074721217103537290069213)
        ·
          refine ⟨34153020456413826483775955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91074721217103537290069213 34153020456413826483775955)
          ·
            refine ⟨51229530684620739725663933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34153020456413826483775955 51229530684620739725663933)
            ·
              refine ⟨19211074006732777397123975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51229530684620739725663933 19211074006732777397123975)
              ·
                refine ⟨28816611010099166095685963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19211074006732777397123975 28816611010099166095685963)
                ·
                  refine ⟨43224916515148749143528945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28816611010099166095685963 43224916515148749143528945)
                  ·
                    refine ⟨32418687386361561857646709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43224916515148749143528945 32418687386361561857646709)
                    ·
                      refine ⟨3039251942471396424154379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32418687386361561857646709 3039251942471396424154379)
                      ·
                        rfl

theorem cell23_5918922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_5918922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918922 prefixEnd_5918922 := by exact prefixLift 5918922
  have htrace : WordTrace (prefixWord ++ tailWord_5918922) baseStart_5918922 baseEnd_5918922 := by
    simpa [prefixWord, tailWord_5918922, baseEnd_5918922] using wordTrace_append hprefix tailTrace_5918922
  have hstable : (prefixWord ++ tailWord_5918922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918922).length < 2 ^ (prefixWord ++ tailWord_5918922).sum := by decide
  have hdescent : baseEnd_5918922 < baseStart_5918922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918949 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5918949 : Nat := 118140960795 + 5918949 * 2 ^ 59
def prefixEnd_5918949 : Nat := 4983230072969 + 3 ^ 40 * 5918949 * 2
def baseEnd_5918949 : Nat := 3039265806449067818516755

theorem tailTrace_5918949 : CollatzResearch.WordTrace tailWord_5918949 prefixEnd_5918949 3039265806449067818516755 := by
  unfold tailWord_5918949
  simp only [CollatzResearch.WordTrace]
  refine ⟨215881805433666123854359901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143921203622444082569573267 215881805433666123854359901)
  ·
    refine ⟨80955677037624796445384963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215881805433666123854359901 80955677037624796445384963)
    ·
      refine ⟨121433515556437194668077445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80955677037624796445384963 121433515556437194668077445)
      ·
        refine ⟨22768784166831974000264521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121433515556437194668077445 22768784166831974000264521)
        ·
          refine ⟨17076588125123980500198391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22768784166831974000264521 17076588125123980500198391)
          ·
            refine ⟨25614882187685970750297587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076588125123980500198391 25614882187685970750297587)
            ·
              refine ⟨38422323281528956125446381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614882187685970750297587 38422323281528956125446381)
              ·
                refine ⟨14408371230573358547042393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38422323281528956125446381 14408371230573358547042393)
                ·
                  refine ⟨10806278422930018910281795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14408371230573358547042393 10806278422930018910281795)
                  ·
                    refine ⟨16209417634395028365422693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10806278422930018910281795 16209417634395028365422693)
                    ·
                      refine ⟨3039265806449067818516755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16209417634395028365422693 3039265806449067818516755)
                      ·
                        rfl

theorem cell23_5918949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5918949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918949 prefixEnd_5918949 := by exact prefixLift 5918949
  have htrace : WordTrace (prefixWord ++ tailWord_5918949) baseStart_5918949 baseEnd_5918949 := by
    simpa [prefixWord, tailWord_5918949, baseEnd_5918949] using wordTrace_append hprefix tailTrace_5918949
  have hstable : (prefixWord ++ tailWord_5918949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918949).length < 2 ^ (prefixWord ++ tailWord_5918949).sum := by decide
  have hdescent : baseEnd_5918949 < baseStart_5918949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5918983 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5918983 : Nat := 118140960795 + 5918983 * 2 ^ 59
def prefixEnd_5918983 : Nat := 4983230072969 + 3 ^ 40 * 5918983 * 2
def baseEnd_5918983 : Nat := 3039283264791320685491599

theorem tailTrace_5918983 : CollatzResearch.WordTrace tailWord_5918983 prefixEnd_5918983 3039283264791320685491599 := by
  unfold tailWord_5918983
  simp only [CollatzResearch.WordTrace]
  refine ⟨215883045515542947661097603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143922030343695298440731735 215883045515542947661097603)
  ·
    refine ⟨323824568273314421491646405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215883045515542947661097603 323824568273314421491646405)
    ·
      refine ⟨60717106551246454029683701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323824568273314421491646405 60717106551246454029683701)
      ·
        refine ⟨5692228739179355065282847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60717106551246454029683701 5692228739179355065282847)
        ·
          refine ⟨8538343108769032597924271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692228739179355065282847 8538343108769032597924271)
          ·
            refine ⟨12807514663153548896886407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8538343108769032597924271 12807514663153548896886407)
            ·
              refine ⟨19211271994730323345329611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12807514663153548896886407 19211271994730323345329611)
              ·
                refine ⟨28816907992095485017994417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19211271994730323345329611 28816907992095485017994417)
                ·
                  refine ⟨21612680994071613763495813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28816907992095485017994417 21612680994071613763495813)
                  ·
                    refine ⟨4052377686388427580655465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21612680994071613763495813 4052377686388427580655465)
                    ·
                      refine ⟨3039283264791320685491599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052377686388427580655465 3039283264791320685491599)
                      ·
                        rfl

theorem cell23_5918983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5918983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5918983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5918983 prefixEnd_5918983 := by exact prefixLift 5918983
  have htrace : WordTrace (prefixWord ++ tailWord_5918983) baseStart_5918983 baseEnd_5918983 := by
    simpa [prefixWord, tailWord_5918983, baseEnd_5918983] using wordTrace_append hprefix tailTrace_5918983
  have hstable : (prefixWord ++ tailWord_5918983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5918983).length < 2 ^ (prefixWord ++ tailWord_5918983).sum := by decide
  have hdescent : baseEnd_5918983 < baseStart_5918983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5918983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919032 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_5919032 : Nat := 118140960795 + 5919032 * 2 ^ 59
def prefixEnd_5919032 : Nat := 4983230072969 + 3 ^ 40 * 5919032 * 2
def baseEnd_5919032 : Nat := 1013102808447796997926291

theorem tailTrace_5919032 : CollatzResearch.WordTrace tailWord_5919032 prefixEnd_5919032 1013102808447796997926291 := by
  unfold tailWord_5919032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107942416346182714514815675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143923221794910286019754233 107942416346182714514815675)
  ·
    refine ⟨161913624519274071772223513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107942416346182714514815675 161913624519274071772223513)
    ·
      refine ⟨121435218389455553829167635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161913624519274071772223513 121435218389455553829167635)
      ·
        refine ⟨182152827584183330743751453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121435218389455553829167635 182152827584183330743751453)
        ·
          refine ⟨68307310344068749028906795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182152827584183330743751453 68307310344068749028906795)
          ·
            refine ⟨102460965516103123543360193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68307310344068749028906795 102460965516103123543360193)
            ·
              refine ⟨76845724137077342657520145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102460965516103123543360193 76845724137077342657520145)
              ·
                refine ⟨57634293102808006993140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76845724137077342657520145 57634293102808006993140109)
                ·
                  refine ⟨21612859913553002622427541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57634293102808006993140109 21612859913553002622427541)
                  ·
                    refine ⟨1013102808447796997926291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21612859913553002622427541 1013102808447796997926291)
                    ·
                      rfl

theorem cell23_5919032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_5919032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919032 prefixEnd_5919032 := by exact prefixLift 5919032
  have htrace : WordTrace (prefixWord ++ tailWord_5919032) baseStart_5919032 baseEnd_5919032 := by
    simpa [prefixWord, tailWord_5919032, baseEnd_5919032] using wordTrace_append hprefix tailTrace_5919032
  have hstable : (prefixWord ++ tailWord_5919032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919032).length < 2 ^ (prefixWord ++ tailWord_5919032).sum := by decide
  have hdescent : baseEnd_5919032 < baseStart_5919032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919033 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5919033 : Nat := 118140960795 + 5919033 * 2 ^ 59
def prefixEnd_5919033 : Nat := 4983230072969 + 3 ^ 40 * 5919033 * 2
def baseEnd_5919033 : Nat := 3039308938824045489866369

theorem tailTrace_5919033 : CollatzResearch.WordTrace tailWord_5919033 prefixEnd_5919033 3039308938824045489866369 := by
  unfold tailWord_5919033
  simp only [CollatzResearch.WordTrace]
  refine ⟨215884869165361806200417753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143923246110241204133611835 215884869165361806200417753)
  ·
    refine ⟨161913651874021354650313315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215884869165361806200417753 161913651874021354650313315)
    ·
      refine ⟨242870477811032031975469973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161913651874021354650313315 242870477811032031975469973)
      ·
        refine ⟨11384553647392126498850155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242870477811032031975469973 11384553647392126498850155)
        ·
          refine ⟨17076830471088189748275233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384553647392126498850155 17076830471088189748275233)
          ·
            refine ⟨12807622853316142311206425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17076830471088189748275233 12807622853316142311206425)
            ·
              refine ⟨9605717139987106733404819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12807622853316142311206425 9605717139987106733404819)
              ·
                refine ⟨14408575709980660100107229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9605717139987106733404819 14408575709980660100107229)
                ·
                  refine ⟨5403215891242747537540211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14408575709980660100107229 5403215891242747537540211)
                  ·
                    refine ⟨8104823836864121306310317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5403215891242747537540211 8104823836864121306310317)
                    ·
                      refine ⟨3039308938824045489866369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104823836864121306310317 3039308938824045489866369)
                      ·
                        rfl

theorem cell23_5919033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5919033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919033 prefixEnd_5919033 := by exact prefixLift 5919033
  have htrace : WordTrace (prefixWord ++ tailWord_5919033) baseStart_5919033 baseEnd_5919033 := by
    simpa [prefixWord, tailWord_5919033, baseEnd_5919033] using wordTrace_append hprefix tailTrace_5919033
  have hstable : (prefixWord ++ tailWord_5919033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919033).length < 2 ^ (prefixWord ++ tailWord_5919033).sum := by decide
  have hdescent : baseEnd_5919033 < baseStart_5919033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919056 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_5919056 : Nat := 118140960795 + 5919056 * 2 ^ 59
def prefixEnd_5919056 : Nat := 4983230072969 + 3 ^ 40 * 5919056 * 2
def baseEnd_5919056 : Nat := 3039320748879098899878763

theorem tailTrace_5919056 : CollatzResearch.WordTrace tailWord_5919056 prefixEnd_5919056 3039320748879098899878763 := by
  unfold tailWord_5919056
  simp only [CollatzResearch.WordTrace]
  refine ⟨107942854022139240564252511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143923805362852320752336681 107942854022139240564252511)
  ·
    refine ⟨161914281033208860846378767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107942854022139240564252511 161914281033208860846378767)
    ·
      refine ⟨242871421549813291269568151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161914281033208860846378767 242871421549813291269568151)
      ·
        refine ⟨364307132324719936904352227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242871421549813291269568151 364307132324719936904352227)
        ·
          refine ⟨546460698487079905356528341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364307132324719936904352227 546460698487079905356528341)
          ·
            refine ⟨12807672620790935281793633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 546460698487079905356528341 12807672620790935281793633)
            ·
              refine ⟨9605754465593201461345225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12807672620790935281793633 9605754465593201461345225)
              ·
                refine ⟨7204315849194901096008919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605754465593201461345225 7204315849194901096008919)
                ·
                  refine ⟨10806473773792351644013379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204315849194901096008919 10806473773792351644013379)
                  ·
                    refine ⟨16209710660688527466020069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10806473773792351644013379 16209710660688527466020069)
                    ·
                      refine ⟨3039320748879098899878763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16209710660688527466020069 3039320748879098899878763)
                      ·
                        rfl

theorem cell23_5919056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_5919056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919056 prefixEnd_5919056 := by exact prefixLift 5919056
  have htrace : WordTrace (prefixWord ++ tailWord_5919056) baseStart_5919056 baseEnd_5919056 := by
    simpa [prefixWord, tailWord_5919056, baseEnd_5919056] using wordTrace_append hprefix tailTrace_5919056
  have hstable : (prefixWord ++ tailWord_5919056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919056).length < 2 ^ (prefixWord ++ tailWord_5919056).sum := by decide
  have hdescent : baseEnd_5919056 < baseStart_5919056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919076 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_5919076 : Nat := 118140960795 + 5919076 * 2 ^ 59
def prefixEnd_5919076 : Nat := 4983230072969 + 3 ^ 40 * 5919076 * 2
def baseEnd_5919076 : Nat := 3039331018492188821628671

theorem tailTrace_5919076 : CollatzResearch.WordTrace tailWord_5919076 prefixEnd_5919076 3039331018492188821628671 := by
  unfold tailWord_5919076
  simp only [CollatzResearch.WordTrace]
  refine ⟨107943218752103012272116541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143924291669470683029488721 107943218752103012272116541)
  ·
    refine ⟨40478707032038629602043703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107943218752103012272116541 40478707032038629602043703)
    ·
      refine ⟨60718060548057944403065555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40478707032038629602043703 60718060548057944403065555)
      ·
        refine ⟨91077090822086916604598333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60718060548057944403065555 91077090822086916604598333)
        ·
          refine ⟨34153909058282593726724375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91077090822086916604598333 34153909058282593726724375)
          ·
            refine ⟨51230863587423890590086563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34153909058282593726724375 51230863587423890590086563)
            ·
              refine ⟨76846295381135835885129845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51230863587423890590086563 76846295381135835885129845)
              ·
                refine ⟨7204340191981484614230923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76846295381135835885129845 7204340191981484614230923)
                ·
                  refine ⟨10806510287972226921346385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204340191981484614230923 10806510287972226921346385)
                  ·
                    refine ⟨8104882715979170191009789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10806510287972226921346385 8104882715979170191009789)
                    ·
                      refine ⟨3039331018492188821628671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8104882715979170191009789 3039331018492188821628671)
                      ·
                        rfl

theorem cell23_5919076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_5919076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919076 prefixEnd_5919076 := by exact prefixLift 5919076
  have htrace : WordTrace (prefixWord ++ tailWord_5919076) baseStart_5919076 baseEnd_5919076 := by
    simpa [prefixWord, tailWord_5919076, baseEnd_5919076] using wordTrace_append hprefix tailTrace_5919076
  have hstable : (prefixWord ++ tailWord_5919076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919076).length < 2 ^ (prefixWord ++ tailWord_5919076).sum := by decide
  have hdescent : baseEnd_5919076 < baseStart_5919076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919079 : List Nat := [1, 1, 5, 1, 3, 3, 9]
def baseStart_5919079 : Nat := 118140960795 + 5919079 * 2 ^ 59
def prefixEnd_5919079 : Nat := 4983230072969 + 3 ^ 40 * 5919079 * 2
def baseEnd_5919079 : Nat := 37522624184372250739397

theorem tailTrace_5919079 : CollatzResearch.WordTrace tailWord_5919079 prefixEnd_5919079 37522624184372250739397 := by
  unfold tailWord_5919079
  simp only [CollatzResearch.WordTrace]
  refine ⟨215886546923195156056592291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143924364615463437371061527 215886546923195156056592291)
  ·
    refine ⟨323829820384792734084888437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215886546923195156056592291 323829820384792734084888437)
    ·
      refine ⟨30359045661074318820458291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323829820384792734084888437 30359045661074318820458291)
      ·
        refine ⟨45538568491611478230687437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30359045661074318820458291 45538568491611478230687437)
        ·
          refine ⟨17076963184354304336507789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45538568491611478230687437 17076963184354304336507789)
          ·
            refine ⟨6403861194132864126190421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17076963184354304336507789 6403861194132864126190421)
            ·
              refine ⟨37522624184372250739397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6403861194132864126190421 37522624184372250739397)
              ·
                rfl

theorem cell23_5919079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 9].length) (baseStart_5919079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919079 prefixEnd_5919079 := by exact prefixLift 5919079
  have htrace : WordTrace (prefixWord ++ tailWord_5919079) baseStart_5919079 baseEnd_5919079 := by
    simpa [prefixWord, tailWord_5919079, baseEnd_5919079] using wordTrace_append hprefix tailTrace_5919079
  have hstable : (prefixWord ++ tailWord_5919079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919079).length < 2 ^ (prefixWord ++ tailWord_5919079).sum := by decide
  have hdescent : baseEnd_5919079 < baseStart_5919079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919090 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_5919090 : Nat := 118140960795 + 5919090 * 2 ^ 59
def prefixEnd_5919090 : Nat := 4983230072969 + 3 ^ 40 * 5919090 * 2
def baseEnd_5919090 : Nat := 3039338207221351766853607

theorem tailTrace_5919090 : CollatzResearch.WordTrace tailWord_5919090 prefixEnd_5919090 3039338207221351766853607 := by
  unfold tailWord_5919090
  simp only [CollatzResearch.WordTrace]
  refine ⟨53971737031538826233810681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143924632084103536623495149 53971737031538826233810681)
  ·
    refine ⟨40478802773654119675358011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53971737031538826233810681 40478802773654119675358011)
    ·
      refine ⟨60718204160481179513037017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40478802773654119675358011 60718204160481179513037017)
      ·
        refine ⟨45538653120360884634777763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60718204160481179513037017 45538653120360884634777763)
        ·
          refine ⟨68307979680541326952166645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45538653120360884634777763 68307979680541326952166645)
          ·
            refine ⟨6403873095050749401765623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68307979680541326952166645 6403873095050749401765623)
            ·
              refine ⟨9605809642576124102648435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403873095050749401765623 9605809642576124102648435)
              ·
                refine ⟨14408714463864186153972653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9605809642576124102648435 14408714463864186153972653)
                ·
                  refine ⟨5403267923949069807739745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14408714463864186153972653 5403267923949069807739745)
                  ·
                    refine ⟨4052450942961802355804809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5403267923949069807739745 4052450942961802355804809)
                    ·
                      refine ⟨3039338207221351766853607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052450942961802355804809 3039338207221351766853607)
                      ·
                        rfl

theorem cell23_5919090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_5919090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919090 prefixEnd_5919090 := by exact prefixLift 5919090
  have htrace : WordTrace (prefixWord ++ tailWord_5919090) baseStart_5919090 baseEnd_5919090 := by
    simpa [prefixWord, tailWord_5919090, baseEnd_5919090] using wordTrace_append hprefix tailTrace_5919090
  have hstable : (prefixWord ++ tailWord_5919090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919090).length < 2 ^ (prefixWord ++ tailWord_5919090).sum := by decide
  have hdescent : baseEnd_5919090 < baseStart_5919090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919159 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_5919159 : Nat := 118140960795 + 5919159 * 2 ^ 59
def prefixEnd_5919159 : Nat := 4983230072969 + 3 ^ 40 * 5919159 * 2
def baseEnd_5919159 : Nat := 3039373637386511996890789

theorem tailTrace_5919159 : CollatzResearch.WordTrace tailWord_5919159 prefixEnd_5919159 3039373637386511996890789 := by
  unfold tailWord_5919159
  simp only [CollatzResearch.WordTrace]
  refine ⟨215889464762905329719504531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143926309841936886479669687 215889464762905329719504531)
  ·
    refine ⟨323834197144357994579256797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215889464762905329719504531 323834197144357994579256797)
    ·
      refine ⟨121437823929134247967221299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323834197144357994579256797 121437823929134247967221299)
      ·
        refine ⟨182156735893701371950831949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121437823929134247967221299 182156735893701371950831949)
        ·
          refine ⟨68308775960138014481561981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182156735893701371950831949 68308775960138014481561981)
          ·
            refine ⟨25615790985051755430585743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68308775960138014481561981 25615790985051755430585743)
            ·
              refine ⟨38423686477577633145878615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25615790985051755430585743 38423686477577633145878615)
              ·
                refine ⟨57635529716366449718817923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38423686477577633145878615 57635529716366449718817923)
                ·
                  refine ⟨86453294574549674578226885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57635529716366449718817923 86453294574549674578226885)
                  ·
                    refine ⟨16209992732728063983417541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86453294574549674578226885 16209992732728063983417541)
                    ·
                      refine ⟨3039373637386511996890789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16209992732728063983417541 3039373637386511996890789)
                      ·
                        rfl

theorem cell23_5919159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_5919159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919159 prefixEnd_5919159 := by exact prefixLift 5919159
  have htrace : WordTrace (prefixWord ++ tailWord_5919159) baseStart_5919159 baseEnd_5919159 := by
    simpa [prefixWord, tailWord_5919159, baseEnd_5919159] using wordTrace_append hprefix tailTrace_5919159
  have hstable : (prefixWord ++ tailWord_5919159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919159).length < 2 ^ (prefixWord ++ tailWord_5919159).sum := by decide
  have hdescent : baseEnd_5919159 < baseStart_5919159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919179 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3]
def baseStart_5919179 : Nat := 118140960795 + 5919179 * 2 ^ 59
def prefixEnd_5919179 : Nat := 4983230072969 + 3 ^ 40 * 5919179 * 2
def baseEnd_5919179 : Nat := 3039383906999601918640697

theorem tailTrace_5919179 : CollatzResearch.WordTrace tailWord_5919179 prefixEnd_5919179 3039383906999601918640697 := by
  unfold tailWord_5919179
  simp only [CollatzResearch.WordTrace]
  refine ⟨215890194222832873135232591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143926796148555248756821727 215890194222832873135232591)
  ·
    refine ⟨323835291334249309702848887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215890194222832873135232591 323835291334249309702848887)
    ·
      refine ⟨485752937001373964554273331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323835291334249309702848887 485752937001373964554273331)
      ·
        refine ⟨728629405502060946831409997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485752937001373964554273331 728629405502060946831409997)
        ·
          refine ⟨273236027063272855061778749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728629405502060946831409997 273236027063272855061778749)
          ·
            refine ⟨102463510148727320648167031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273236027063272855061778749 102463510148727320648167031)
            ·
              refine ⟨153695265223090980972250547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102463510148727320648167031 153695265223090980972250547)
              ·
                refine ⟨230542897834636471458375821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153695265223090980972250547 230542897834636471458375821)
                ·
                  refine ⟨86453586687988676796890933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230542897834636471458375821 86453586687988676796890933)
                  ·
                    refine ⟨8105023751998938449708525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86453586687988676796890933 8105023751998938449708525)
                    ·
                      refine ⟨3039383906999601918640697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105023751998938449708525 3039383906999601918640697)
                      ·
                        rfl

theorem cell23_5919179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 3].length) (baseStart_5919179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919179 prefixEnd_5919179 := by exact prefixLift 5919179
  have htrace : WordTrace (prefixWord ++ tailWord_5919179) baseStart_5919179 baseEnd_5919179 := by
    simpa [prefixWord, tailWord_5919179, baseEnd_5919179] using wordTrace_append hprefix tailTrace_5919179
  have hstable : (prefixWord ++ tailWord_5919179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919179).length < 2 ^ (prefixWord ++ tailWord_5919179).sum := by decide
  have hdescent : baseEnd_5919179 < baseStart_5919179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919213 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5919213 : Nat := 118140960795 + 5919213 * 2 ^ 59
def prefixEnd_5919213 : Nat := 4983230072969 + 3 ^ 40 * 5919213 * 2
def baseEnd_5919213 : Nat := 3039401365341854785615541

theorem tailTrace_5919213 : CollatzResearch.WordTrace tailWord_5919213 prefixEnd_5919213 3039401365341854785615541 := by
  unfold tailWord_5919213
  simp only [CollatzResearch.WordTrace]
  refine ⟨215891434304709696941970293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143927622869806464627980195 215891434304709696941970293)
  ·
    refine ⟨20239821966066534088309715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215891434304709696941970293 20239821966066534088309715)
    ·
      refine ⟨30359732949099801132464573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20239821966066534088309715 30359732949099801132464573)
      ·
        refine ⟨11384899855912425424674215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30359732949099801132464573 11384899855912425424674215)
        ·
          refine ⟨17077349783868638137011323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384899855912425424674215 17077349783868638137011323)
          ·
            refine ⟨25616024675802957205516985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17077349783868638137011323 25616024675802957205516985)
            ·
              refine ⟨19212018506852217904137739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25616024675802957205516985 19212018506852217904137739)
              ·
                refine ⟨28818027760278326856206609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19212018506852217904137739 28818027760278326856206609)
                ·
                  refine ⟨21613520820208745142154957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28818027760278326856206609 21613520820208745142154957)
                  ·
                    refine ⟨8105070307578279428308109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21613520820208745142154957 8105070307578279428308109)
                    ·
                      refine ⟨3039401365341854785615541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105070307578279428308109 3039401365341854785615541)
                      ·
                        rfl

theorem cell23_5919213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5919213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919213 prefixEnd_5919213 := by exact prefixLift 5919213
  have htrace : WordTrace (prefixWord ++ tailWord_5919213) baseStart_5919213 baseEnd_5919213 := by
    simpa [prefixWord, tailWord_5919213, baseEnd_5919213] using wordTrace_append hprefix tailTrace_5919213
  have hstable : (prefixWord ++ tailWord_5919213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919213).length < 2 ^ (prefixWord ++ tailWord_5919213).sum := by decide
  have hdescent : baseEnd_5919213 < baseStart_5919213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919219 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_5919219 : Nat := 118140960795 + 5919219 * 2 ^ 59
def prefixEnd_5919219 : Nat := 4983230072969 + 3 ^ 40 * 5919219 * 2
def baseEnd_5919219 : Nat := 3039404446225781762140513

theorem tailTrace_5919219 : CollatzResearch.WordTrace tailWord_5919219 prefixEnd_5919219 3039404446225781762140513 := by
  unfold tailWord_5919219
  simp only [CollatzResearch.WordTrace]
  refine ⟨215891653142687959966688711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143927768761791973311125807 215891653142687959966688711)
  ·
    refine ⟨323837479714031939950033067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215891653142687959966688711 323837479714031939950033067)
    ·
      refine ⟨485756219571047909925049601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323837479714031939950033067 485756219571047909925049601)
      ·
        refine ⟨364317164678285932443787201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485756219571047909925049601 364317164678285932443787201)
        ·
          refine ⟨273237873508714449332840401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364317164678285932443787201 273237873508714449332840401)
          ·
            refine ⟨204928405131535836999630301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273237873508714449332840401 204928405131535836999630301)
            ·
              refine ⟨76848151924325938874861363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204928405131535836999630301 76848151924325938874861363)
              ·
                refine ⟨115272227886488908312292045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76848151924325938874861363 115272227886488908312292045)
                ·
                  refine ⟨43227085457433340617109517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115272227886488908312292045 43227085457433340617109517)
                  ·
                    refine ⟨16210157046537502731416069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43227085457433340617109517 16210157046537502731416069)
                    ·
                      refine ⟨3039404446225781762140513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16210157046537502731416069 3039404446225781762140513)
                      ·
                        rfl

theorem cell23_5919219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_5919219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919219 prefixEnd_5919219 := by exact prefixLift 5919219
  have htrace : WordTrace (prefixWord ++ tailWord_5919219) baseStart_5919219 baseEnd_5919219 := by
    simpa [prefixWord, tailWord_5919219, baseEnd_5919219] using wordTrace_append hprefix tailTrace_5919219
  have hstable : (prefixWord ++ tailWord_5919219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919219).length < 2 ^ (prefixWord ++ tailWord_5919219).sum := by decide
  have hdescent : baseEnd_5919219 < baseStart_5919219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919229 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5919229 : Nat := 118140960795 + 5919229 * 2 ^ 59
def prefixEnd_5919229 : Nat := 4983230072969 + 3 ^ 40 * 5919229 * 2
def baseEnd_5919229 : Nat := 1013136527010775574338489

theorem tailTrace_5919229 : CollatzResearch.WordTrace tailWord_5919229 prefixEnd_5919229 1013136527010775574338489 := by
  unfold tailWord_5919229
  simp only [CollatzResearch.WordTrace]
  refine ⟨215892017872651731674552741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143928011915101154449701827 215892017872651731674552741)
  ·
    refine ⟨40479753351122199688978639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215892017872651731674552741 40479753351122199688978639)
    ·
      refine ⟨60719630026683299533467959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40479753351122199688978639 60719630026683299533467959)
      ·
        refine ⟨91079445040024949300201939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60719630026683299533467959 91079445040024949300201939)
        ·
          refine ⟨136619167560037423950302909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91079445040024949300201939 136619167560037423950302909)
          ·
            refine ⟨51232187835014033981363591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136619167560037423950302909 51232187835014033981363591)
            ·
              refine ⟨76848281752521050972045387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51232187835014033981363591 76848281752521050972045387)
              ·
                refine ⟨115272422628781576458068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76848281752521050972045387 115272422628781576458068081)
                ·
                  refine ⟨86454316971586182343551061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115272422628781576458068081 86454316971586182343551061)
                  ·
                    refine ⟨1013136527010775574338489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86454316971586182343551061 1013136527010775574338489)
                    ·
                      rfl

theorem cell23_5919229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5919229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919229 prefixEnd_5919229 := by exact prefixLift 5919229
  have htrace : WordTrace (prefixWord ++ tailWord_5919229) baseStart_5919229 baseEnd_5919229 := by
    simpa [prefixWord, tailWord_5919229, baseEnd_5919229] using wordTrace_append hprefix tailTrace_5919229
  have hstable : (prefixWord ++ tailWord_5919229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919229).length < 2 ^ (prefixWord ++ tailWord_5919229).sum := by decide
  have hdescent : baseEnd_5919229 < baseStart_5919229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919249 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_5919249 : Nat := 118140960795 + 5919249 * 2 ^ 59
def prefixEnd_5919249 : Nat := 4983230072969 + 3 ^ 40 * 5919249 * 2
def baseEnd_5919249 : Nat := 3039419850645416644765375

theorem tailTrace_5919249 : CollatzResearch.WordTrace tailWord_5919249 prefixEnd_5919249 3039419850645416644765375 := by
  unfold tailWord_5919249
  simp only [CollatzResearch.WordTrace]
  refine ⟨215892747332579275090280801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143928498221719516726853867 215892747332579275090280801)
  ·
    refine ⟨161919560499434456317710601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215892747332579275090280801 161919560499434456317710601)
    ·
      refine ⟨121439670374575842238282951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161919560499434456317710601 121439670374575842238282951)
      ·
        refine ⟨182159505561863763357424427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121439670374575842238282951 182159505561863763357424427)
        ·
          refine ⟨273239258342795645036136641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182159505561863763357424427 273239258342795645036136641)
          ·
            refine ⟨204929443757096733777102481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273239258342795645036136641 204929443757096733777102481)
            ·
              refine ⟨153697082817822550332826861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204929443757096733777102481 153697082817822550332826861)
              ·
                refine ⟨57636406056683456374810073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153697082817822550332826861 57636406056683456374810073)
                ·
                  refine ⟨43227304542512592281107555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57636406056683456374810073 43227304542512592281107555)
                  ·
                    refine ⟨64840956813768888421661333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43227304542512592281107555 64840956813768888421661333)
                    ·
                      refine ⟨3039419850645416644765375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64840956813768888421661333 3039419850645416644765375)
                      ·
                        rfl

theorem cell23_5919249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_5919249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919249 prefixEnd_5919249 := by exact prefixLift 5919249
  have htrace : WordTrace (prefixWord ++ tailWord_5919249) baseStart_5919249 baseEnd_5919249 := by
    simpa [prefixWord, tailWord_5919249, baseEnd_5919249] using wordTrace_append hprefix tailTrace_5919249
  have hstable : (prefixWord ++ tailWord_5919249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919249).length < 2 ^ (prefixWord ++ tailWord_5919249).sum := by decide
  have hdescent : baseEnd_5919249 < baseStart_5919249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919299 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_5919299 : Nat := 118140960795 + 5919299 * 2 ^ 59
def prefixEnd_5919299 : Nat := 4983230072969 + 3 ^ 40 * 5919299 * 2
def baseEnd_5919299 : Nat := 3039445524678141449140145

theorem tailTrace_5919299 : CollatzResearch.WordTrace tailWord_5919299 prefixEnd_5919299 3039445524678141449140145 := by
  unfold tailWord_5919299
  simp only [CollatzResearch.WordTrace]
  refine ⟨215894570982398133629600951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143929713988265422419733967 215894570982398133629600951)
  ·
    refine ⟨323841856473597200444401427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215894570982398133629600951 323841856473597200444401427)
    ·
      refine ⟨485762784710395800666602141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323841856473597200444401427 485762784710395800666602141)
      ·
        refine ⟨182161044266398425249975803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485762784710395800666602141 182161044266398425249975803)
        ·
          refine ⟨273241566399597637874963705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182161044266398425249975803 273241566399597637874963705)
          ·
            refine ⟨204931174799698228406222779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273241566399597637874963705 204931174799698228406222779)
            ·
              refine ⟨307396762199547342609334169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204931174799698228406222779 307396762199547342609334169)
              ·
                refine ⟨230547571649660506957000627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307396762199547342609334169 230547571649660506957000627)
                ·
                  refine ⟨345821357474490760435500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230547571649660506957000627 345821357474490760435500941)
                  ·
                    refine ⟨129683009052934035163312853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345821357474490760435500941 129683009052934035163312853)
                    ·
                      refine ⟨3039445524678141449140145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129683009052934035163312853 3039445524678141449140145)
                      ·
                        rfl

theorem cell23_5919299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_5919299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919299 prefixEnd_5919299 := by exact prefixLift 5919299
  have htrace : WordTrace (prefixWord ++ tailWord_5919299) baseStart_5919299 baseEnd_5919299 := by
    simpa [prefixWord, tailWord_5919299, baseEnd_5919299] using wordTrace_append hprefix tailTrace_5919299
  have hstable : (prefixWord ++ tailWord_5919299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919299).length < 2 ^ (prefixWord ++ tailWord_5919299).sum := by decide
  have hdescent : baseEnd_5919299 < baseStart_5919299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919357 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_5919357 : Nat := 118140960795 + 5919357 * 2 ^ 59
def prefixEnd_5919357 : Nat := 4983230072969 + 3 ^ 40 * 5919357 * 2
def baseEnd_5919357 : Nat := 1013158435518700740738293

theorem tailTrace_5919357 : CollatzResearch.WordTrace tailWord_5919357 prefixEnd_5919357 1013158435518700740738293 := by
  unfold tailWord_5919357
  simp only [CollatzResearch.WordTrace]
  refine ⟨215896686416188009535212325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143931124277458673023474883 215896686416188009535212325)
  ·
    refine ⟨40480628703035251787852311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215896686416188009535212325 40480628703035251787852311)
    ·
      refine ⟨60720943054552877681778467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40480628703035251787852311 60720943054552877681778467)
      ·
        refine ⟨91081414581829316522667701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60720943054552877681778467 91081414581829316522667701)
        ·
          refine ⟨8538882617046498424000097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91081414581829316522667701 8538882617046498424000097)
          ·
            refine ⟨6404161962784873818000073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8538882617046498424000097 6404161962784873818000073)
            ·
              refine ⟨4803121472088655363500055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404161962784873818000073 4803121472088655363500055)
              ·
                refine ⟨7204682208132983045250083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803121472088655363500055 7204682208132983045250083)
                ·
                  refine ⟨10807023312199474567875125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204682208132983045250083 10807023312199474567875125)
                  ·
                    refine ⟨1013158435518700740738293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10807023312199474567875125 1013158435518700740738293)
                    ·
                      rfl

theorem cell23_5919357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_5919357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919357 prefixEnd_5919357 := by exact prefixLift 5919357
  have htrace : WordTrace (prefixWord ++ tailWord_5919357) baseStart_5919357 baseEnd_5919357 := by
    simpa [prefixWord, tailWord_5919357, baseEnd_5919357] using wordTrace_append hprefix tailTrace_5919357
  have hstable : (prefixWord ++ tailWord_5919357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919357).length < 2 ^ (prefixWord ++ tailWord_5919357).sum := by decide
  have hdescent : baseEnd_5919357 < baseStart_5919357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919360 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4]
def baseStart_5919360 : Nat := 118140960795 + 5919360 * 2 ^ 59
def prefixEnd_5919360 : Nat := 4983230072969 + 3 ^ 40 * 5919360 * 2
def baseEnd_5919360 : Nat := 3039476846998065710477365

theorem tailTrace_5919360 : CollatzResearch.WordTrace tailWord_5919360 prefixEnd_5919360 3039476846998065710477365 := by
  unfold tailWord_5919360
  simp only [CollatzResearch.WordTrace]
  refine ⟨107948397917588570523785767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143931197223451427365047689 107948397917588570523785767)
  ·
    refine ⟨161922596876382855785678651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107948397917588570523785767 161922596876382855785678651)
    ·
      refine ⟨242883895314574283678517977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161922596876382855785678651 242883895314574283678517977)
      ·
        refine ⟨182162921485930712758888483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242883895314574283678517977 182162921485930712758888483)
        ·
          refine ⟨273244382228896069138332725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182162921485930712758888483 273244382228896069138332725)
          ·
            refine ⟨25616660833959006481718693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273244382228896069138332725 25616660833959006481718693)
            ·
              refine ⟨4803123906367313715322255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25616660833959006481718693 4803123906367313715322255)
              ·
                refine ⟨7204685859550970572983383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803123906367313715322255 7204685859550970572983383)
                ·
                  refine ⟨10807028789326455859475075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204685859550970572983383 10807028789326455859475075)
                  ·
                    refine ⟨16210543183989683789212613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10807028789326455859475075 16210543183989683789212613)
                    ·
                      refine ⟨3039476846998065710477365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16210543183989683789212613 3039476846998065710477365)
                      ·
                        rfl

theorem cell23_5919360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_5919360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919360 prefixEnd_5919360 := by exact prefixLift 5919360
  have htrace : WordTrace (prefixWord ++ tailWord_5919360) baseStart_5919360 baseEnd_5919360 := by
    simpa [prefixWord, tailWord_5919360, baseEnd_5919360] using wordTrace_append hprefix tailTrace_5919360
  have hstable : (prefixWord ++ tailWord_5919360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919360).length < 2 ^ (prefixWord ++ tailWord_5919360).sum := by decide
  have hdescent : baseEnd_5919360 < baseStart_5919360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919370 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_5919370 : Nat := 118140960795 + 5919370 * 2 ^ 59
def prefixEnd_5919370 : Nat := 4983230072969 + 3 ^ 40 * 5919370 * 2
def baseEnd_5919370 : Nat := 1013160660601536890450773

theorem tailTrace_5919370 : CollatzResearch.WordTrace tailWord_5919370 prefixEnd_5919370 1013160660601536890450773 := by
  unfold tailWord_5919370
  simp only [CollatzResearch.WordTrace]
  refine ⟨53974290141285228188858891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143931440376760608503623709 53974290141285228188858891)
  ·
    refine ⟨80961435211927842283288337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53974290141285228188858891 80961435211927842283288337)
    ·
      refine ⟨60721076408945881712466253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80961435211927842283288337 60721076408945881712466253)
      ·
        refine ⟨22770403653354705642174845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60721076408945881712466253 22770403653354705642174845)
        ·
          refine ⟨8538901370008014615815567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22770403653354705642174845 8538901370008014615815567)
          ·
            refine ⟨12808352055012021923723351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8538901370008014615815567 12808352055012021923723351)
            ·
              refine ⟨19212528082518032885585027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808352055012021923723351 19212528082518032885585027)
              ·
                refine ⟨28818792123777049328377541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19212528082518032885585027 28818792123777049328377541)
                ·
                  refine ⟨5403523523208196749070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28818792123777049328377541 5403523523208196749070789)
                  ·
                    refine ⟨1013160660601536890450773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403523523208196749070789 1013160660601536890450773)
                    ·
                      rfl

theorem cell23_5919370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_5919370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919370 prefixEnd_5919370 := by exact prefixLift 5919370
  have htrace : WordTrace (prefixWord ++ tailWord_5919370) baseStart_5919370 baseEnd_5919370 := by
    simpa [prefixWord, tailWord_5919370, baseEnd_5919370] using wordTrace_append hprefix tailTrace_5919370
  have hstable : (prefixWord ++ tailWord_5919370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919370).length < 2 ^ (prefixWord ++ tailWord_5919370).sum := by decide
  have hdescent : baseEnd_5919370 < baseStart_5919370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919376 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_5919376 : Nat := 118140960795 + 5919376 * 2 ^ 59
def prefixEnd_5919376 : Nat := 4983230072969 + 3 ^ 40 * 5919376 * 2
def baseEnd_5919376 : Nat := 3039485062688537647877291

theorem tailTrace_5919376 : CollatzResearch.WordTrace tailWord_5919376 prefixEnd_5919376 3039485062688537647877291 := by
  unfold tailWord_5919376
  simp only [CollatzResearch.WordTrace]
  refine ⟨107948689701559587890076991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143931586268746117186769321 107948689701559587890076991)
  ·
    refine ⟨161923034552339381835115487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107948689701559587890076991 161923034552339381835115487)
    ·
      refine ⟨242884551828509072752673231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161923034552339381835115487 242884551828509072752673231)
      ·
        refine ⟨364326827742763609129009847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242884551828509072752673231 364326827742763609129009847)
        ·
          refine ⟨546490241614145413693514771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364326827742763609129009847 546490241614145413693514771)
          ·
            refine ⟨819735362421218120540272157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546490241614145413693514771 819735362421218120540272157)
            ·
              refine ⟨307400760907956795202602059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819735362421218120540272157 307400760907956795202602059)
              ·
                refine ⟨461101141361935192803903089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307400760907956795202602059 461101141361935192803903089)
                ·
                  refine ⟨345825856021451394602927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461101141361935192803903089 345825856021451394602927317)
                  ·
                    refine ⟨8105293500502767061006109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 345825856021451394602927317 8105293500502767061006109)
                    ·
                      refine ⟨3039485062688537647877291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105293500502767061006109 3039485062688537647877291)
                      ·
                        rfl

theorem cell23_5919376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_5919376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919376 prefixEnd_5919376 := by exact prefixLift 5919376
  have htrace : WordTrace (prefixWord ++ tailWord_5919376) baseStart_5919376 baseEnd_5919376 := by
    simpa [prefixWord, tailWord_5919376, baseEnd_5919376] using wordTrace_append hprefix tailTrace_5919376
  have hstable : (prefixWord ++ tailWord_5919376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919376).length < 2 ^ (prefixWord ++ tailWord_5919376).sum := by decide
  have hdescent : baseEnd_5919376 < baseStart_5919376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919380 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5919380 : Nat := 118140960795 + 5919380 * 2 ^ 59
def prefixEnd_5919380 : Nat := 4983230072969 + 3 ^ 40 * 5919380 * 2
def baseEnd_5919380 : Nat := 3039487116611155632227273

theorem tailTrace_5919380 : CollatzResearch.WordTrace tailWord_5919380 prefixEnd_5919380 3039487116611155632227273 := by
  unfold tailWord_5919380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107948762647552342231649797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143931683530069789642199729 107948762647552342231649797)
  ·
    refine ⟨20240392996416064168434337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107948762647552342231649797 20240392996416064168434337)
    ·
      refine ⟨15180294747312048126325753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20240392996416064168434337 15180294747312048126325753)
      ·
        refine ⟨11385221060484036094744315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15180294747312048126325753 11385221060484036094744315)
        ·
          refine ⟨17077831590726054142116473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385221060484036094744315 17077831590726054142116473)
          ·
            refine ⟨12808373693044540606587355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17077831590726054142116473 12808373693044540606587355)
            ·
              refine ⟨19212560539566810909881033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808373693044540606587355 19212560539566810909881033)
              ·
                refine ⟨14409420404675108182410775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19212560539566810909881033 14409420404675108182410775)
                ·
                  refine ⟨21614130607012662273616163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14409420404675108182410775 21614130607012662273616163)
                  ·
                    refine ⟨32421195910518993410424245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21614130607012662273616163 32421195910518993410424245)
                    ·
                      refine ⟨3039487116611155632227273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32421195910518993410424245 3039487116611155632227273)
                      ·
                        rfl

theorem cell23_5919380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5919380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919380 prefixEnd_5919380 := by exact prefixLift 5919380
  have htrace : WordTrace (prefixWord ++ tailWord_5919380) baseStart_5919380 baseEnd_5919380 := by
    simpa [prefixWord, tailWord_5919380, baseEnd_5919380] using wordTrace_append hprefix tailTrace_5919380
  have hstable : (prefixWord ++ tailWord_5919380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919380).length < 2 ^ (prefixWord ++ tailWord_5919380).sum := by decide
  have hdescent : baseEnd_5919380 < baseStart_5919380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919416 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_5919416 : Nat := 118140960795 + 5919416 * 2 ^ 59
def prefixEnd_5919416 : Nat := 4983230072969 + 3 ^ 40 * 5919416 * 2
def baseEnd_5919416 : Nat := 3039505601914717491377107

theorem tailTrace_5919416 : CollatzResearch.WordTrace tailWord_5919416 prefixEnd_5919416 3039505601914717491377107 := by
  unfold tailWord_5919416
  simp only [CollatzResearch.WordTrace]
  refine ⟨107949419161487131305805051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143932558881982841741073401 107949419161487131305805051)
  ·
    refine ⟨161924128742230696958707577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107949419161487131305805051 161924128742230696958707577)
    ·
      refine ⟨121443096556673022719030683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161924128742230696958707577 121443096556673022719030683)
      ·
        refine ⟨182164644835009534078546025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121443096556673022719030683 182164644835009534078546025)
        ·
          refine ⟨136623483626257150558909519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182164644835009534078546025 136623483626257150558909519)
          ·
            refine ⟨204935225439385725838364279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136623483626257150558909519 204935225439385725838364279)
            ·
              refine ⟨307402838159078588757546419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204935225439385725838364279 307402838159078588757546419)
              ·
                refine ⟨461104257238617883136319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307402838159078588757546419 461104257238617883136319629)
                ·
                  refine ⟨172914096464481706176119861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461104257238617883136319629 172914096464481706176119861)
                  ·
                    refine ⟨16210696543545159954011237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172914096464481706176119861 16210696543545159954011237)
                    ·
                      refine ⟨3039505601914717491377107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16210696543545159954011237 3039505601914717491377107)
                      ·
                        rfl

theorem cell23_5919416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_5919416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919416 prefixEnd_5919416 := by exact prefixLift 5919416
  have htrace : WordTrace (prefixWord ++ tailWord_5919416) baseStart_5919416 baseEnd_5919416 := by
    simpa [prefixWord, tailWord_5919416, baseEnd_5919416] using wordTrace_append hprefix tailTrace_5919416
  have hstable : (prefixWord ++ tailWord_5919416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919416).length < 2 ^ (prefixWord ++ tailWord_5919416).sum := by decide
  have hdescent : baseEnd_5919416 < baseStart_5919416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919444 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5919444 : Nat := 118140960795 + 5919444 * 2 ^ 59
def prefixEnd_5919444 : Nat := 4983230072969 + 3 ^ 40 * 5919444 * 2
def baseEnd_5919444 : Nat := 3039519979373043381826979

theorem tailTrace_5919444 : CollatzResearch.WordTrace tailWord_5919444 prefixEnd_5919444 3039519979373043381826979 := by
  unfold tailWord_5919444
  simp only [CollatzResearch.WordTrace]
  refine ⟨107949929783436411696814693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143933239711248548929086257 107949929783436411696814693)
  ·
    refine ⟨20240611834394327193152755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107949929783436411696814693 20240611834394327193152755)
    ·
      refine ⟨30360917751591490789729133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20240611834394327193152755 30360917751591490789729133)
      ·
        refine ⟨11385344156846809046148425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30360917751591490789729133 11385344156846809046148425)
        ·
          refine ⟨8539008117635106784611319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11385344156846809046148425 8539008117635106784611319)
          ·
            refine ⟨12808512176452660176916979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539008117635106784611319 12808512176452660176916979)
            ·
              refine ⟨19212768264678990265375469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808512176452660176916979 19212768264678990265375469)
              ·
                refine ⟨7204788099254621349515801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19212768264678990265375469 7204788099254621349515801)
                ·
                  refine ⟨5403591074440966012136851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7204788099254621349515801 5403591074440966012136851)
                  ·
                    refine ⟨8105386611661449018205277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5403591074440966012136851 8105386611661449018205277)
                    ·
                      refine ⟨3039519979373043381826979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105386611661449018205277 3039519979373043381826979)
                      ·
                        rfl

theorem cell23_5919444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5919444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919444 prefixEnd_5919444 := by exact prefixLift 5919444
  have htrace : WordTrace (prefixWord ++ tailWord_5919444) baseStart_5919444 baseEnd_5919444 := by
    simpa [prefixWord, tailWord_5919444, baseEnd_5919444] using wordTrace_append hprefix tailTrace_5919444
  have hstable : (prefixWord ++ tailWord_5919444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919444).length < 2 ^ (prefixWord ++ tailWord_5919444).sum := by decide
  have hdescent : baseEnd_5919444 < baseStart_5919444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919450 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_5919450 : Nat := 118140960795 + 5919450 * 2 ^ 59
def prefixEnd_5919450 : Nat := 4983230072969 + 3 ^ 40 * 5919450 * 2
def baseEnd_5919450 : Nat := 3039523060256970358351951

theorem tailTrace_5919450 : CollatzResearch.WordTrace tailWord_5919450 prefixEnd_5919450 3039523060256970358351951 := by
  unfold tailWord_5919450
  simp only [CollatzResearch.WordTrace]
  refine ⟨53975019601212771604586951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143933385603234057612231869 53975019601212771604586951)
  ·
    refine ⟨80962529401819157406880427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53975019601212771604586951 80962529401819157406880427)
    ·
      refine ⟨121443794102728736110320641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80962529401819157406880427 121443794102728736110320641)
      ·
        refine ⟨91082845577046552082740481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121443794102728736110320641 91082845577046552082740481)
        ·
          refine ⟨68312134182784914062055361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91082845577046552082740481 68312134182784914062055361)
          ·
            refine ⟨51234100637088685546541521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68312134182784914062055361 51234100637088685546541521)
            ·
              refine ⟨38425575477816514159906141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51234100637088685546541521 38425575477816514159906141)
              ·
                refine ⟨14409590804181192809964803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38425575477816514159906141 14409590804181192809964803)
                ·
                  refine ⟨21614386206271789214947205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14409590804181192809964803 21614386206271789214947205)
                  ·
                    refine ⟨4052697413675960477802601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21614386206271789214947205 4052697413675960477802601)
                    ·
                      refine ⟨3039523060256970358351951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052697413675960477802601 3039523060256970358351951)
                      ·
                        rfl

theorem cell23_5919450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_5919450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919450 prefixEnd_5919450 := by exact prefixLift 5919450
  have htrace : WordTrace (prefixWord ++ tailWord_5919450) baseStart_5919450 baseEnd_5919450 := by
    simpa [prefixWord, tailWord_5919450, baseEnd_5919450] using wordTrace_append hprefix tailTrace_5919450
  have hstable : (prefixWord ++ tailWord_5919450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919450).length < 2 ^ (prefixWord ++ tailWord_5919450).sum := by decide
  have hdescent : baseEnd_5919450 < baseStart_5919450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919456 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 9]
def baseStart_5919456 : Nat := 118140960795 + 5919456 * 2 ^ 59
def prefixEnd_5919456 : Nat := 4983230072969 + 3 ^ 40 * 5919456 * 2
def baseEnd_5919456 : Nat := 337725126793433037208547

theorem tailTrace_5919456 : CollatzResearch.WordTrace tailWord_5919456 prefixEnd_5919456 337725126793433037208547 := by
  unfold tailWord_5919456
  simp only [CollatzResearch.WordTrace]
  refine ⟨107950148621414674721533111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143933531495219566295377481 107950148621414674721533111)
  ·
    refine ⟨161925222932122012082299667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107950148621414674721533111 161925222932122012082299667)
    ·
      refine ⟨242887834398183018123449501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161925222932122012082299667 242887834398183018123449501)
      ·
        refine ⟨91082937899318631796293563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242887834398183018123449501 91082937899318631796293563)
        ·
          refine ⟨136624406848977947694440345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91082937899318631796293563 136624406848977947694440345)
          ·
            refine ⟨102468305136733460770830259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136624406848977947694440345 102468305136733460770830259)
            ·
              refine ⟨153702457705100191156245389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102468305136733460770830259 153702457705100191156245389)
              ·
                refine ⟨57638421639412571683592021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153702457705100191156245389 57638421639412571683592021)
                ·
                  refine ⟨337725126793433037208547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57638421639412571683592021 337725126793433037208547)
                  ·
                    rfl

theorem cell23_5919456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_5919456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919456 prefixEnd_5919456 := by exact prefixLift 5919456
  have htrace : WordTrace (prefixWord ++ tailWord_5919456) baseStart_5919456 baseEnd_5919456 := by
    simpa [prefixWord, tailWord_5919456, baseEnd_5919456] using wordTrace_append hprefix tailTrace_5919456
  have hstable : (prefixWord ++ tailWord_5919456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919456).length < 2 ^ (prefixWord ++ tailWord_5919456).sum := by decide
  have hdescent : baseEnd_5919456 < baseStart_5919456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919484 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_5919484 : Nat := 118140960795 + 5919484 * 2 ^ 59
def prefixEnd_5919484 : Nat := 4983230072969 + 3 ^ 40 * 5919484 * 2
def baseEnd_5919484 : Nat := 3039540518599223225326795

theorem tailTrace_5919484 : CollatzResearch.WordTrace tailWord_5919484 prefixEnd_5919484 3039540518599223225326795 := by
  unfold tailWord_5919484
  simp only [CollatzResearch.WordTrace]
  refine ⟨107950659243363955112542753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143934212324485273483390337 107950659243363955112542753)
  ·
    refine ⟨80962994432522966334407065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107950659243363955112542753 80962994432522966334407065)
    ·
      refine ⟨60722245824392224750805299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80962994432522966334407065 60722245824392224750805299)
      ·
        refine ⟨91083368736588337126207949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60722245824392224750805299 91083368736588337126207949)
        ·
          refine ⟨34156263276220626422327981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91083368736588337126207949 34156263276220626422327981)
          ·
            refine ⟨12808598728582734908372993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34156263276220626422327981 12808598728582734908372993)
            ·
              refine ⟨9606449046437051181279745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12808598728582734908372993 9606449046437051181279745)
              ·
                refine ⟨7204836784827788385959809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606449046437051181279745 7204836784827788385959809)
                ·
                  refine ⟨5403627588620841289469857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7204836784827788385959809 5403627588620841289469857)
                  ·
                    refine ⟨4052720691465630967102393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5403627588620841289469857 4052720691465630967102393)
                    ·
                      refine ⟨3039540518599223225326795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052720691465630967102393 3039540518599223225326795)
                      ·
                        rfl

theorem cell23_5919484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_5919484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919484 prefixEnd_5919484 := by exact prefixLift 5919484
  have htrace : WordTrace (prefixWord ++ tailWord_5919484) baseStart_5919484 baseEnd_5919484 := by
    simpa [prefixWord, tailWord_5919484, baseEnd_5919484] using wordTrace_append hprefix tailTrace_5919484
  have hstable : (prefixWord ++ tailWord_5919484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919484).length < 2 ^ (prefixWord ++ tailWord_5919484).sum := by decide
  have hdescent : baseEnd_5919484 < baseStart_5919484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919520 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_5919520 : Nat := 118140960795 + 5919520 * 2 ^ 59
def prefixEnd_5919520 : Nat := 4983230072969 + 3 ^ 40 * 5919520 * 2
def baseEnd_5919520 : Nat := 1013186334634261694825543

theorem tailTrace_5919520 : CollatzResearch.WordTrace tailWord_5919520 prefixEnd_5919520 1013186334634261694825543 := by
  unfold tailWord_5919520
  simp only [CollatzResearch.WordTrace]
  refine ⟨107951315757298744186698007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143935087676398325582264009 107951315757298744186698007)
  ·
    refine ⟨161926973635948116280047011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107951315757298744186698007 161926973635948116280047011)
    ·
      refine ⟨242890460453922174420070517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161926973635948116280047011 242890460453922174420070517)
      ·
        refine ⟨22770980667555203851881611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242890460453922174420070517 22770980667555203851881611)
        ·
          refine ⟨34156471001332805777822417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22770980667555203851881611 34156471001332805777822417)
          ·
            refine ⟨25617353250999604333366813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34156471001332805777822417 25617353250999604333366813)
            ·
              refine ⟨9606507469124851625012555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25617353250999604333366813 9606507469124851625012555)
              ·
                refine ⟨14409761203687277437518833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606507469124851625012555 14409761203687277437518833)
                ·
                  refine ⟨10807320902765458078139125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14409761203687277437518833 10807320902765458078139125)
                  ·
                    refine ⟨1013186334634261694825543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10807320902765458078139125 1013186334634261694825543)
                    ·
                      rfl

theorem cell23_5919520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_5919520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919520 prefixEnd_5919520 := by exact prefixLift 5919520
  have htrace : WordTrace (prefixWord ++ tailWord_5919520) baseStart_5919520 baseEnd_5919520 := by
    simpa [prefixWord, tailWord_5919520, baseEnd_5919520] using wordTrace_append hprefix tailTrace_5919520
  have hstable : (prefixWord ++ tailWord_5919520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919520).length < 2 ^ (prefixWord ++ tailWord_5919520).sum := by decide
  have hdescent : baseEnd_5919520 < baseStart_5919520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919580 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 8]
def baseStart_5919580 : Nat := 118140960795 + 5919580 * 2 ^ 59
def prefixEnd_5919580 : Nat := 4983230072969 + 3 ^ 40 * 5919580 * 2
def baseEnd_5919580 : Nat := 337732201415783872191817

theorem tailTrace_5919580 : CollatzResearch.WordTrace tailWord_5919580 prefixEnd_5919580 337732201415783872191817 := by
  unfold tailWord_5919580
  simp only [CollatzResearch.WordTrace]
  refine ⟨107952409947190059310290097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143936546596253412413720129 107952409947190059310290097)
  ·
    refine ⟨80964307460392544482717573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107952409947190059310290097 80964307460392544482717573)
    ·
      refine ⟨15180807648823602090509545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80964307460392544482717573 15180807648823602090509545)
      ·
        refine ⟨11385605736617701567882159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15180807648823602090509545 11385605736617701567882159)
        ·
          refine ⟨17078408604926552351823239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385605736617701567882159 17078408604926552351823239)
          ·
            refine ⟨25617612907389828527734859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078408604926552351823239 25617612907389828527734859)
            ·
              refine ⟨38426419361084742791602289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25617612907389828527734859 38426419361084742791602289)
              ·
                refine ⟨28819814520813557093701717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38426419361084742791602289 28819814520813557093701717)
                ·
                  refine ⟨337732201415783872191817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28819814520813557093701717 337732201415783872191817)
                  ·
                    rfl

theorem cell23_5919580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_5919580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919580 prefixEnd_5919580 := by exact prefixLift 5919580
  have htrace : WordTrace (prefixWord ++ tailWord_5919580) baseStart_5919580 baseEnd_5919580 := by
    simpa [prefixWord, tailWord_5919580, baseEnd_5919580] using wordTrace_append hprefix tailTrace_5919580
  have hstable : (prefixWord ++ tailWord_5919580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919580).length < 2 ^ (prefixWord ++ tailWord_5919580).sum := by decide
  have hdescent : baseEnd_5919580 < baseStart_5919580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919593 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_5919593 : Nat := 118140960795 + 5919593 * 2 ^ 59
def prefixEnd_5919593 : Nat := 4983230072969 + 3 ^ 40 * 5919593 * 2
def baseEnd_5919593 : Nat := 1013198829330187766287931

theorem tailTrace_5919593 : CollatzResearch.WordTrace tailWord_5919593 prefixEnd_5919593 1013198829330187766287931 := by
  unfold tailWord_5919593
  simp only [CollatzResearch.WordTrace]
  refine ⟨215905294043333021840803433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143936862695555347893868955 215905294043333021840803433)
  ·
    refine ⟨161928970532499766380602575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215905294043333021840803433 161928970532499766380602575)
    ·
      refine ⟨242893455798749649570903863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161928970532499766380602575 242893455798749649570903863)
      ·
        refine ⟨364340183698124474356355795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242893455798749649570903863 364340183698124474356355795)
        ·
          refine ⟨546510275547186711534533693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364340183698124474356355795 546510275547186711534533693)
          ·
            refine ⟨204941353330195016825450135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546510275547186711534533693 204941353330195016825450135)
            ·
              refine ⟨307412029995292525238175203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204941353330195016825450135 307412029995292525238175203)
              ·
                refine ⟨461118044992938787857262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307412029995292525238175203 461118044992938787857262805)
                ·
                  refine ⟨10807454179522002840404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 461118044992938787857262805 10807454179522002840404597)
                  ·
                    refine ⟨1013198829330187766287931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10807454179522002840404597 1013198829330187766287931)
                    ·
                      rfl

theorem cell23_5919593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_5919593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919593 prefixEnd_5919593 := by exact prefixLift 5919593
  have htrace : WordTrace (prefixWord ++ tailWord_5919593) baseStart_5919593 baseEnd_5919593 := by
    simpa [prefixWord, tailWord_5919593, baseEnd_5919593] using wordTrace_append hprefix tailTrace_5919593
  have hstable : (prefixWord ++ tailWord_5919593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919593).length < 2 ^ (prefixWord ++ tailWord_5919593).sum := by decide
  have hdescent : baseEnd_5919593 < baseStart_5919593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919614 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_5919614 : Nat := 118140960795 + 5919614 * 2 ^ 59
def prefixEnd_5919614 : Nat := 4983230072969 + 3 ^ 40 * 5919614 * 2
def baseEnd_5919614 : Nat := 337734141231589746300133

theorem tailTrace_5919614 : CollatzResearch.WordTrace tailWord_5919614 prefixEnd_5919614 337734141231589746300133 := by
  unfold tailWord_5919614
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988257497032117803414737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143937373317504628284878597 26988257497032117803414737)
  ·
    refine ⟨20241193122774088352561053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26988257497032117803414737 20241193122774088352561053)
    ·
      refine ⟨7590447421040283132210395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20241193122774088352561053 7590447421040283132210395)
      ·
        refine ⟨11385671131560424698315593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590447421040283132210395 11385671131560424698315593)
        ·
          refine ⟨8539253348670318523736695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11385671131560424698315593 8539253348670318523736695)
          ·
            refine ⟨12808880023005477785605043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539253348670318523736695 12808880023005477785605043)
            ·
              refine ⟨19213320034508216678407565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808880023005477785605043 19213320034508216678407565)
              ·
                refine ⟨7204995012940581254402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19213320034508216678407565 7204995012940581254402837)
                ·
                  refine ⟨337734141231589746300133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7204995012940581254402837 337734141231589746300133)
                  ·
                    rfl

theorem cell23_5919614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_5919614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919614 prefixEnd_5919614 := by exact prefixLift 5919614
  have htrace : WordTrace (prefixWord ++ tailWord_5919614) baseStart_5919614 baseEnd_5919614 := by
    simpa [prefixWord, tailWord_5919614, baseEnd_5919614] using wordTrace_append hprefix tailTrace_5919614
  have hstable : (prefixWord ++ tailWord_5919614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919614).length < 2 ^ (prefixWord ++ tailWord_5919614).sum := by decide
  have hdescent : baseEnd_5919614 < baseStart_5919614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919657 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_5919657 : Nat := 118140960795 + 5919657 * 2 ^ 59
def prefixEnd_5919657 : Nat := 4983230072969 + 3 ^ 40 * 5919657 * 2
def baseEnd_5919657 : Nat := 1013209783584150349487833

theorem tailTrace_5919657 : CollatzResearch.WordTrace tailWord_5919657 prefixEnd_5919657 1013209783584150349487833 := by
  unfold tailWord_5919657
  simp only [CollatzResearch.WordTrace]
  refine ⟨215907628315101160771133225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143938418876734107180755483 215907628315101160771133225)
  ·
    refine ⟨161930721236325870578349919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215907628315101160771133225 161930721236325870578349919)
    ·
      refine ⟨242896081854488805867524879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161930721236325870578349919 242896081854488805867524879)
      ·
        refine ⟨364344122781733208801287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242896081854488805867524879 364344122781733208801287319)
        ·
          refine ⟨546516184172599813201930979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364344122781733208801287319 546516184172599813201930979)
          ·
            refine ⟨819774276258899719802896469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546516184172599813201930979 819774276258899719802896469)
            ·
              refine ⟨9606729799908981091440193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 819774276258899719802896469 9606729799908981091440193)
              ·
                refine ⟨7205047349931735818580145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606729799908981091440193 7205047349931735818580145)
                ·
                  refine ⟨5403785512448801863935109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205047349931735818580145 5403785512448801863935109)
                  ·
                    refine ⟨1013209783584150349487833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403785512448801863935109 1013209783584150349487833)
                    ·
                      rfl

theorem cell23_5919657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_5919657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919657 prefixEnd_5919657 := by exact prefixLift 5919657
  have htrace : WordTrace (prefixWord ++ tailWord_5919657) baseStart_5919657 baseEnd_5919657 := by
    simpa [prefixWord, tailWord_5919657, baseEnd_5919657] using wordTrace_append hprefix tailTrace_5919657
  have hstable : (prefixWord ++ tailWord_5919657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919657).length < 2 ^ (prefixWord ++ tailWord_5919657).sum := by decide
  have hdescent : baseEnd_5919657 < baseStart_5919657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_5919663 : Nat := 118140960795 + 5919663 * 2 ^ 59
def prefixEnd_5919663 : Nat := 4983230072969 + 3 ^ 40 * 5919663 * 2
def baseEnd_5919663 : Nat := 3039632431636378024988471

theorem tailTrace_5919663 : CollatzResearch.WordTrace tailWord_5919663 prefixEnd_5919663 3039632431636378024988471 := by
  unfold tailWord_5919663
  simp only [CollatzResearch.WordTrace]
  refine ⟨215907847153079423795851643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143938564768719615863901095 215907847153079423795851643)
  ·
    refine ⟨323861770729619135693777465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215907847153079423795851643 323861770729619135693777465)
    ·
      refine ⟨242896328047214351770333099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323861770729619135693777465 242896328047214351770333099)
      ·
        refine ⟨364344492070821527655499649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242896328047214351770333099 364344492070821527655499649)
        ·
          refine ⟨273258369053116145741624737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364344492070821527655499649 273258369053116145741624737)
          ·
            refine ⟨204943776789837109306218553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273258369053116145741624737 204943776789837109306218553)
            ·
              refine ⟨153707832592377831979663915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204943776789837109306218553 153707832592377831979663915)
              ·
                refine ⟨230561748888566747969495873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153707832592377831979663915 230561748888566747969495873)
                ·
                  refine ⟨172921311666425060977121905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230561748888566747969495873 172921311666425060977121905)
                  ·
                    refine ⟨129690983749818795732841429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172921311666425060977121905 129690983749818795732841429)
                    ·
                      refine ⟨3039632431636378024988471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129690983749818795732841429 3039632431636378024988471)
                      ·
                        rfl

theorem cell23_5919663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_5919663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919663 prefixEnd_5919663 := by exact prefixLift 5919663
  have htrace : WordTrace (prefixWord ++ tailWord_5919663) baseStart_5919663 baseEnd_5919663 := by
    simpa [prefixWord, tailWord_5919663, baseEnd_5919663] using wordTrace_append hprefix tailTrace_5919663
  have hstable : (prefixWord ++ tailWord_5919663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919663).length < 2 ^ (prefixWord ++ tailWord_5919663).sum := by decide
  have hdescent : baseEnd_5919663 < baseStart_5919663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919697 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 3]
def baseStart_5919697 : Nat := 118140960795 + 5919697 * 2 ^ 59
def prefixEnd_5919697 : Nat := 4983230072969 + 3 ^ 40 * 5919697 * 2
def baseEnd_5919697 : Nat := 3039649889978630891963315

theorem tailTrace_5919697 : CollatzResearch.WordTrace tailWord_5919697 prefixEnd_5919697 3039649889978630891963315 := by
  unfold tailWord_5919697
  simp only [CollatzResearch.WordTrace]
  refine ⟨215909087234956247602589345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143939391489970831735059563 215909087234956247602589345)
  ·
    refine ⟨161931815426217185701942009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215909087234956247602589345 161931815426217185701942009)
    ·
      refine ⟨121448861569662889276456507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161931815426217185701942009 121448861569662889276456507)
      ·
        refine ⟨182173292354494333914684761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121448861569662889276456507 182173292354494333914684761)
        ·
          refine ⟨136629969265870750436013571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182173292354494333914684761 136629969265870750436013571)
          ·
            refine ⟨204944953898806125654020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136629969265870750436013571 204944953898806125654020357)
            ·
              refine ⟨38427178856026148560128817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204944953898806125654020357 38427178856026148560128817)
              ·
                refine ⟨28820384142019611420096613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38427178856026148560128817 28820384142019611420096613)
                ·
                  refine ⟨5403822026628677141268115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28820384142019611420096613 5403822026628677141268115)
                  ·
                    refine ⟨8105733039943015711902173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5403822026628677141268115 8105733039943015711902173)
                    ·
                      refine ⟨3039649889978630891963315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105733039943015711902173 3039649889978630891963315)
                      ·
                        rfl

theorem cell23_5919697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_5919697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919697 prefixEnd_5919697 := by exact prefixLift 5919697
  have htrace : WordTrace (prefixWord ++ tailWord_5919697) baseStart_5919697 baseEnd_5919697 := by
    simpa [prefixWord, tailWord_5919697, baseEnd_5919697] using wordTrace_append hprefix tailTrace_5919697
  have hstable : (prefixWord ++ tailWord_5919697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919697).length < 2 ^ (prefixWord ++ tailWord_5919697).sum := by decide
  have hdescent : baseEnd_5919697 < baseStart_5919697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919698 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5919698 : Nat := 118140960795 + 5919698 * 2 ^ 59
def prefixEnd_5919698 : Nat := 4983230072969 + 3 ^ 40 * 5919698 * 2
def baseEnd_5919698 : Nat := 3039650403459285388050811

theorem tailTrace_5919698 : CollatzResearch.WordTrace tailWord_5919698 prefixEnd_5919698 3039650403459285388050811 := by
  unfold tailWord_5919698
  simp only [CollatzResearch.WordTrace]
  refine ⟨53977280926988156193343937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143939415805301749848917165 53977280926988156193343937)
  ·
    refine ⟨40482960695241117145007953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53977280926988156193343937 40482960695241117145007953)
    ·
      refine ⟨30362220521430837858755965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40482960695241117145007953 30362220521430837858755965)
      ·
        refine ⟨11385832695536564197033487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30362220521430837858755965 11385832695536564197033487)
        ·
          refine ⟨17078749043304846295550231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385832695536564197033487 17078749043304846295550231)
          ·
            refine ⟨25618123564957269443325347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078749043304846295550231 25618123564957269443325347)
            ·
              refine ⟨38427185347435904164988021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25618123564957269443325347 38427185347435904164988021)
              ·
                refine ⟨3602548626322116015467627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38427185347435904164988021 3602548626322116015467627)
                ·
                  refine ⟨5403822939483174023201441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602548626322116015467627 5403822939483174023201441)
                  ·
                    refine ⟨4052867204612380517401081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5403822939483174023201441 4052867204612380517401081)
                    ·
                      refine ⟨3039650403459285388050811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4052867204612380517401081 3039650403459285388050811)
                      ·
                        rfl

theorem cell23_5919698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5919698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919698 prefixEnd_5919698 := by exact prefixLift 5919698
  have htrace : WordTrace (prefixWord ++ tailWord_5919698) baseStart_5919698 baseEnd_5919698 := by
    simpa [prefixWord, tailWord_5919698, baseEnd_5919698] using wordTrace_append hprefix tailTrace_5919698
  have hstable : (prefixWord ++ tailWord_5919698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919698).length < 2 ^ (prefixWord ++ tailWord_5919698).sum := by decide
  have hdescent : baseEnd_5919698 < baseStart_5919698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919720 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_5919720 : Nat := 118140960795 + 5919720 * 2 ^ 59
def prefixEnd_5919720 : Nat := 4983230072969 + 3 ^ 40 * 5919720 * 2
def baseEnd_5919720 : Nat := 3039661700033684301975709

theorem tailTrace_5919720 : CollatzResearch.WordTrace tailWord_5919720 prefixEnd_5919720 3039661700033684301975709 := by
  unfold tailWord_5919720
  simp only [CollatzResearch.WordTrace]
  refine ⟨107954963056936461265338307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143939950742581948353784409 107954963056936461265338307)
  ·
    refine ⟨161932444585404691898007461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107954963056936461265338307 161932444585404691898007461)
    ·
      refine ⟨30362333359763379730876399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161932444585404691898007461 30362333359763379730876399)
      ·
        refine ⟨45543500039645069596314599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30362333359763379730876399 45543500039645069596314599)
        ·
          refine ⟨68315250059467604394471899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45543500039645069596314599 68315250059467604394471899)
          ·
            refine ⟨102472875089201406591707849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68315250059467604394471899 102472875089201406591707849)
            ·
              refine ⟨76854656316901054943780887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102472875089201406591707849 76854656316901054943780887)
              ·
                refine ⟨115281984475351582415671331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76854656316901054943780887 115281984475351582415671331)
                ·
                  refine ⟨172922976713027373623506997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115281984475351582415671331 172922976713027373623506997)
                  ·
                    refine ⟨16211529066846316277203781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172922976713027373623506997 16211529066846316277203781)
                    ·
                      refine ⟨3039661700033684301975709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16211529066846316277203781 3039661700033684301975709)
                      ·
                        rfl

theorem cell23_5919720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_5919720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919720 prefixEnd_5919720 := by exact prefixLift 5919720
  have htrace : WordTrace (prefixWord ++ tailWord_5919720) baseStart_5919720 baseEnd_5919720 := by
    simpa [prefixWord, tailWord_5919720, baseEnd_5919720] using wordTrace_append hprefix tailTrace_5919720
  have hstable : (prefixWord ++ tailWord_5919720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919720).length < 2 ^ (prefixWord ++ tailWord_5919720).sum := by decide
  have hdescent : baseEnd_5919720 < baseStart_5919720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919770 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_5919770 : Nat := 118140960795 + 5919770 * 2 ^ 59
def prefixEnd_5919770 : Nat := 4983230072969 + 3 ^ 40 * 5919770 * 2
def baseEnd_5919770 : Nat := 3039687374066409106350479

theorem tailTrace_5919770 : CollatzResearch.WordTrace tailWord_5919770 prefixEnd_5919770 3039687374066409106350479 := by
  unfold tailWord_5919770
  simp only [CollatzResearch.WordTrace]
  refine ⟨53977937440922945267499191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143941166509127854046664509 53977937440922945267499191)
  ·
    refine ⟨80966906161384417901248787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53977937440922945267499191 80966906161384417901248787)
    ·
      refine ⟨121450359242076626851873181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80966906161384417901248787 121450359242076626851873181)
      ·
        refine ⟨45543884715778735069452443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121450359242076626851873181 45543884715778735069452443)
        ·
          refine ⟨68315827073668102604178665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45543884715778735069452443 68315827073668102604178665)
          ·
            refine ⟨51236870305251076953133999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68315827073668102604178665 51236870305251076953133999)
            ·
              refine ⟨76855305457876615429700999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51236870305251076953133999 76855305457876615429700999)
              ·
                refine ⟨115282958186814923144551499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76855305457876615429700999 115282958186814923144551499)
                ·
                  refine ⟨172924437280222384716827249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115282958186814923144551499 172924437280222384716827249)
                  ·
                    refine ⟨129693327960166788537620437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172924437280222384716827249 129693327960166788537620437)
                    ·
                      refine ⟨3039687374066409106350479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129693327960166788537620437 3039687374066409106350479)
                      ·
                        rfl

theorem cell23_5919770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_5919770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919770 prefixEnd_5919770 := by exact prefixLift 5919770
  have htrace : WordTrace (prefixWord ++ tailWord_5919770) baseStart_5919770 baseEnd_5919770 := by
    simpa [prefixWord, tailWord_5919770, baseEnd_5919770] using wordTrace_append hprefix tailTrace_5919770
  have hstable : (prefixWord ++ tailWord_5919770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919770).length < 2 ^ (prefixWord ++ tailWord_5919770).sum := by decide
  have hdescent : baseEnd_5919770 < baseStart_5919770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919777 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 7]
def baseStart_5919777 : Nat := 118140960795 + 5919777 * 2 ^ 59
def prefixEnd_5919777 : Nat := 4983230072969 + 3 ^ 40 * 5919777 * 2
def baseEnd_5919777 : Nat := 337743440936776730995883

theorem tailTrace_5919777 : CollatzResearch.WordTrace tailWord_5919777 prefixEnd_5919777 337743440936776730995883 := by
  unfold tailWord_5919777
  simp only [CollatzResearch.WordTrace]
  refine ⟨215912005074666421265501585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143941336716444280843667723 215912005074666421265501585)
  ·
    refine ⟨161934003805999815949126189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215912005074666421265501585 161934003805999815949126189)
    ·
      refine ⟨60725251427249930980922321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161934003805999815949126189 60725251427249930980922321)
      ·
        refine ⟨45543938570437448235691741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60725251427249930980922321 45543938570437448235691741)
        ·
          refine ⟨17078976963914043088384403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45543938570437448235691741 17078976963914043088384403)
          ·
            refine ⟨25618465445871064632576605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078976963914043088384403 25618465445871064632576605)
            ·
              refine ⟨9606924542201649237216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25618465445871064632576605 9606924542201649237216227)
              ·
                refine ⟨14410386813302473855824341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606924542201649237216227 14410386813302473855824341)
                ·
                  refine ⟨337743440936776730995883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14410386813302473855824341 337743440936776730995883)
                  ·
                    rfl

theorem cell23_5919777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_5919777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919777 prefixEnd_5919777 := by exact prefixLift 5919777
  have htrace : WordTrace (prefixWord ++ tailWord_5919777) baseStart_5919777 baseEnd_5919777 := by
    simpa [prefixWord, tailWord_5919777, baseEnd_5919777] using wordTrace_append hprefix tailTrace_5919777
  have hstable : (prefixWord ++ tailWord_5919777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919777).length < 2 ^ (prefixWord ++ tailWord_5919777).sum := by decide
  have hdescent : baseEnd_5919777 < baseStart_5919777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919838 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5919838 : Nat := 118140960795 + 5919838 * 2 ^ 59
def prefixEnd_5919838 : Nat := 4983230072969 + 3 ^ 40 * 5919838 * 2
def baseEnd_5919838 : Nat := 3039722290750914840300167

theorem tailTrace_5919838 : CollatzResearch.WordTrace tailWord_5919838 prefixEnd_5919838 3039722290750914840300167 := by
  unfold tailWord_5919838
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989278740930678585434021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143942819951630285788981445 26989278740930678585434021)
  ·
    refine ⟨5060489763924502234768879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26989278740930678585434021 5060489763924502234768879)
    ·
      refine ⟨7590734645886753352153319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060489763924502234768879 7590734645886753352153319)
      ·
        refine ⟨11386101968830130028229979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590734645886753352153319 11386101968830130028229979)
        ·
          refine ⟨17079152953245195042344969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386101968830130028229979 17079152953245195042344969)
          ·
            refine ⟨12809364714933896281758727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17079152953245195042344969 12809364714933896281758727)
            ·
              refine ⟨19214047072400844422638091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12809364714933896281758727 19214047072400844422638091)
              ·
                refine ⟨28821070608601266633957137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19214047072400844422638091 28821070608601266633957137)
                ·
                  refine ⟨21615802956450949975467853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28821070608601266633957137 21615802956450949975467853)
                  ·
                    refine ⟨8105926108669106240800445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21615802956450949975467853 8105926108669106240800445)
                    ·
                      refine ⟨3039722290750914840300167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105926108669106240800445 3039722290750914840300167)
                      ·
                        rfl

theorem cell23_5919838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5919838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919838 prefixEnd_5919838 := by exact prefixLift 5919838
  have htrace : WordTrace (prefixWord ++ tailWord_5919838) baseStart_5919838 baseEnd_5919838 := by
    simpa [prefixWord, tailWord_5919838, baseEnd_5919838] using wordTrace_append hprefix tailTrace_5919838
  have hstable : (prefixWord ++ tailWord_5919838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919838).length < 2 ^ (prefixWord ++ tailWord_5919838).sum := by decide
  have hdescent : baseEnd_5919838 < baseStart_5919838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919854 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_5919854 : Nat := 118140960795 + 5919854 * 2 ^ 59
def prefixEnd_5919854 : Nat := 4983230072969 + 3 ^ 40 * 5919854 * 2
def baseEnd_5919854 : Nat := 1013243502147128925900031

theorem tailTrace_5919854 : CollatzResearch.WordTrace tailWord_5919854 prefixEnd_5919854 1013243502147128925900031 := by
  unfold tailWord_5919854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989351686923432927006827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143943208996924975610703077 26989351686923432927006827)
  ·
    refine ⟨40484027530385149390510241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26989351686923432927006827 40484027530385149390510241)
    ·
      refine ⟨30363020647788862042882681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40484027530385149390510241 30363020647788862042882681)
      ·
        refine ⟨22772265485841646532162011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30363020647788862042882681 22772265485841646532162011)
        ·
          refine ⟨34158398228762469798243017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772265485841646532162011 34158398228762469798243017)
          ·
            refine ⟨25618798671571852348682263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34158398228762469798243017 25618798671571852348682263)
            ·
              refine ⟨38428198007357778523023395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25618798671571852348682263 38428198007357778523023395)
              ·
                refine ⟨57642297011036667784535093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38428198007357778523023395 57642297011036667784535093)
                ·
                  refine ⟨5403965344784687604800165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57642297011036667784535093 5403965344784687604800165)
                  ·
                    refine ⟨1013243502147128925900031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5403965344784687604800165 1013243502147128925900031)
                    ·
                      rfl

theorem cell23_5919854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_5919854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919854 prefixEnd_5919854 := by exact prefixLift 5919854
  have htrace : WordTrace (prefixWord ++ tailWord_5919854) baseStart_5919854 baseEnd_5919854 := by
    simpa [prefixWord, tailWord_5919854, baseEnd_5919854] using wordTrace_append hprefix tailTrace_5919854
  have hstable : (prefixWord ++ tailWord_5919854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919854).length < 2 ^ (prefixWord ++ tailWord_5919854).sum := by decide
  have hdescent : baseEnd_5919854 < baseStart_5919854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919861 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5919861 : Nat := 118140960795 + 5919861 * 2 ^ 59
def prefixEnd_5919861 : Nat := 4983230072969 + 3 ^ 40 * 5919861 * 2
def baseEnd_5919861 : Nat := 3039734100805968250312561

theorem tailTrace_5919861 : CollatzResearch.WordTrace tailWord_5919861 prefixEnd_5919861 3039734100805968250312561 := by
  unfold tailWord_5919861
  simp only [CollatzResearch.WordTrace]
  refine ⟨215915068806362103611559437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143943379204241402407706291 215915068806362103611559437)
  ·
    refine ⟨80968150802385788854334789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215915068806362103611559437 80968150802385788854334789)
    ·
      refine ⟨15181528275447335410187773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80968150802385788854334789 15181528275447335410187773)
      ·
        refine ⟨5693073103292750778820415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15181528275447335410187773 5693073103292750778820415)
        ·
          refine ⟨8539609654939126168230623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693073103292750778820415 8539609654939126168230623)
          ·
            refine ⟨12809414482408689252345935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539609654939126168230623 12809414482408689252345935)
            ·
              refine ⟨19214121723613033878518903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12809414482408689252345935 19214121723613033878518903)
              ·
                refine ⟨28821182585419550817778355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19214121723613033878518903 28821182585419550817778355)
                ·
                  refine ⟨43231773878129326226667533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28821182585419550817778355 43231773878129326226667533)
                  ·
                    refine ⟨16211915204298497335000325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43231773878129326226667533 16211915204298497335000325)
                    ·
                      refine ⟨3039734100805968250312561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16211915204298497335000325 3039734100805968250312561)
                      ·
                        rfl

theorem cell23_5919861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5919861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919861 prefixEnd_5919861 := by exact prefixLift 5919861
  have htrace : WordTrace (prefixWord ++ tailWord_5919861) baseStart_5919861 baseEnd_5919861 := by
    simpa [prefixWord, tailWord_5919861, baseEnd_5919861] using wordTrace_append hprefix tailTrace_5919861
  have hstable : (prefixWord ++ tailWord_5919861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919861).length < 2 ^ (prefixWord ++ tailWord_5919861).sum := by decide
  have hdescent : baseEnd_5919861 < baseStart_5919861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919864 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_5919864 : Nat := 118140960795 + 5919864 * 2 ^ 59
def prefixEnd_5919864 : Nat := 4983230072969 + 3 ^ 40 * 5919864 * 2
def baseEnd_5919864 : Nat := 3039735641247931738575047

theorem tailTrace_5919864 : CollatzResearch.WordTrace tailWord_5919864 prefixEnd_5919864 3039735641247931738575047 := by
  unfold tailWord_5919864
  simp only [CollatzResearch.WordTrace]
  refine ⟨107957589112675617561959323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143943452150234156749279097 107957589112675617561959323)
  ·
    refine ⟨161936383669013426342938985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107957589112675617561959323 161936383669013426342938985)
    ·
      refine ⟨121452287751760069757204239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161936383669013426342938985 121452287751760069757204239)
      ·
        refine ⟨182178431627640104635806359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121452287751760069757204239 182178431627640104635806359)
        ·
          refine ⟨273267647441460156953709539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182178431627640104635806359 273267647441460156953709539)
          ·
            refine ⟨409901471162190235430564309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273267647441460156953709539 409901471162190235430564309)
            ·
              refine ⟨9607065730363833642903851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 409901471162190235430564309 9607065730363833642903851)
              ·
                refine ⟨14410598595545750464355777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9607065730363833642903851 14410598595545750464355777)
                ·
                  refine ⟨10807948946659312848266833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14410598595545750464355777 10807948946659312848266833)
                  ·
                    refine ⟨8105961709994484636200125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10807948946659312848266833 8105961709994484636200125)
                    ·
                      refine ⟨3039735641247931738575047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8105961709994484636200125 3039735641247931738575047)
                      ·
                        rfl

theorem cell23_5919864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_5919864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919864 prefixEnd_5919864 := by exact prefixLift 5919864
  have htrace : WordTrace (prefixWord ++ tailWord_5919864) baseStart_5919864 baseEnd_5919864 := by
    simpa [prefixWord, tailWord_5919864, baseEnd_5919864] using wordTrace_append hprefix tailTrace_5919864
  have hstable : (prefixWord ++ tailWord_5919864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919864).length < 2 ^ (prefixWord ++ tailWord_5919864).sum := by decide
  have hdescent : baseEnd_5919864 < baseStart_5919864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919904 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2]
def baseStart_5919904 : Nat := 118140960795 + 5919904 * 2 ^ 59
def prefixEnd_5919904 : Nat := 4983230072969 + 3 ^ 40 * 5919904 * 2
def baseEnd_5919904 : Nat := 3039756180474111582074863

theorem tailTrace_5919904 : CollatzResearch.WordTrace tailWord_5919904 prefixEnd_5919904 3039756180474111582074863 := by
  unfold tailWord_5919904
  simp only [CollatzResearch.WordTrace]
  refine ⟨107958318572603160977687383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143944424763470881303583177 107958318572603160977687383)
  ·
    refine ⟨161937477858904741466531075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107958318572603160977687383 161937477858904741466531075)
    ·
      refine ⟨242906216788357112199796613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161937477858904741466531075 242906216788357112199796613)
      ·
        refine ⟨45544915647816958537461865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242906216788357112199796613 45544915647816958537461865)
        ·
          refine ⟨34158686735862718903096399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45544915647816958537461865 34158686735862718903096399)
          ·
            refine ⟨51238030103794078354644599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34158686735862718903096399 51238030103794078354644599)
            ·
              refine ⟨76857045155691117531966899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51238030103794078354644599 76857045155691117531966899)
              ·
                refine ⟨115285567733536676297950349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76857045155691117531966899 115285567733536676297950349)
                ·
                  refine ⟨43232087900076253611731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115285567733536676297950349 43232087900076253611731381)
                  ·
                    refine ⟨4053008240632148776099817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43232087900076253611731381 4053008240632148776099817)
                    ·
                      refine ⟨3039756180474111582074863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053008240632148776099817 3039756180474111582074863)
                      ·
                        rfl

theorem cell23_5919904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_5919904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919904 prefixEnd_5919904 := by exact prefixLift 5919904
  have htrace : WordTrace (prefixWord ++ tailWord_5919904) baseStart_5919904 baseEnd_5919904 := by
    simpa [prefixWord, tailWord_5919904, baseEnd_5919904] using wordTrace_append hprefix tailTrace_5919904
  have hstable : (prefixWord ++ tailWord_5919904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919904).length < 2 ^ (prefixWord ++ tailWord_5919904).sum := by decide
  have hdescent : baseEnd_5919904 < baseStart_5919904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919921 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5919921 : Nat := 118140960795 + 5919921 * 2 ^ 59
def prefixEnd_5919921 : Nat := 4983230072969 + 3 ^ 40 * 5919921 * 2
def baseEnd_5919921 : Nat := 3039764909645238015562285

theorem tailTrace_5919921 : CollatzResearch.WordTrace tailWord_5919921 prefixEnd_5919921 3039764909645238015562285 := by
  unfold tailWord_5919921
  simp only [CollatzResearch.WordTrace]
  refine ⟨215917257186144733858743617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143944838124096489239162411 215917257186144733858743617)
  ·
    refine ⟨161937942889608550394057713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215917257186144733858743617 161937942889608550394057713)
    ·
      refine ⟨121453457167206412795543285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161937942889608550394057713 121453457167206412795543285)
      ·
        refine ⟨11386261609425601199582183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121453457167206412795543285 11386261609425601199582183)
        ·
          refine ⟨17079392414138401799373275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386261609425601199582183 17079392414138401799373275)
          ·
            refine ⟨25619088621207602699059913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17079392414138401799373275 25619088621207602699059913)
            ·
              refine ⟨19214316465905702024294935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25619088621207602699059913 19214316465905702024294935)
              ·
                refine ⟨28821474698858553036442403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19214316465905702024294935 28821474698858553036442403)
                ·
                  refine ⟨43232212048287829554663605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28821474698858553036442403 43232212048287829554663605)
                  ·
                    refine ⟨4053019879526984020749713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43232212048287829554663605 4053019879526984020749713)
                    ·
                      refine ⟨3039764909645238015562285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053019879526984020749713 3039764909645238015562285)
                      ·
                        rfl

theorem cell23_5919921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5919921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919921 prefixEnd_5919921 := by exact prefixLift 5919921
  have htrace : WordTrace (prefixWord ++ tailWord_5919921) baseStart_5919921 baseEnd_5919921 := by
    simpa [prefixWord, tailWord_5919921, baseEnd_5919921] using wordTrace_append hprefix tailTrace_5919921
  have hstable : (prefixWord ++ tailWord_5919921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919921).length < 2 ^ (prefixWord ++ tailWord_5919921).sum := by decide
  have hdescent : baseEnd_5919921 < baseStart_5919921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919927 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 6]
def baseStart_5919927 : Nat := 118140960795 + 5919927 * 2 ^ 59
def prefixEnd_5919927 : Nat := 4983230072969 + 3 ^ 40 * 5919927 * 2
def baseEnd_5919927 : Nat := 1013255996843054997362419

theorem tailTrace_5919927 : CollatzResearch.WordTrace tailWord_5919927 prefixEnd_5919927 1013255996843054997362419 := by
  unfold tailWord_5919927
  simp only [CollatzResearch.WordTrace]
  refine ⟨215917476024122996883462035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143944984016081997922308023 215917476024122996883462035)
  ·
    refine ⟨323876214036184495325193053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215917476024122996883462035 323876214036184495325193053)
    ·
      refine ⟨121453580263569185746947395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323876214036184495325193053 121453580263569185746947395)
      ·
        refine ⟨182180370395353778620421093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121453580263569185746947395 182180370395353778620421093)
        ·
          refine ⟨34158819449128833491328955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182180370395353778620421093 34158819449128833491328955)
          ·
            refine ⟨51238229173693250236993433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34158819449128833491328955 51238229173693250236993433)
            ·
              refine ⟨38428671880269937677745075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51238229173693250236993433 38428671880269937677745075)
              ·
                refine ⟨57643007820404906516617613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38428671880269937677745075 57643007820404906516617613)
                ·
                  refine ⟨21616127932651839943731605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57643007820404906516617613 21616127932651839943731605)
                  ·
                    refine ⟨1013255996843054997362419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21616127932651839943731605 1013255996843054997362419)
                    ·
                      rfl

theorem cell23_5919927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_5919927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919927 prefixEnd_5919927 := by exact prefixLift 5919927
  have htrace : WordTrace (prefixWord ++ tailWord_5919927) baseStart_5919927 baseEnd_5919927 := by
    simpa [prefixWord, tailWord_5919927, baseEnd_5919927] using wordTrace_append hprefix tailTrace_5919927
  have hstable : (prefixWord ++ tailWord_5919927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919927).length < 2 ^ (prefixWord ++ tailWord_5919927).sum := by decide
  have hdescent : baseEnd_5919927 < baseStart_5919927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919944 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_5919944 : Nat := 118140960795 + 5919944 * 2 ^ 59
def prefixEnd_5919944 : Nat := 4983230072969 + 3 ^ 40 * 5919944 * 2
def baseEnd_5919944 : Nat := 1013258906566763808524893

theorem tailTrace_5919944 : CollatzResearch.WordTrace tailWord_5919944 prefixEnd_5919944 1013258906566763808524893 := by
  unfold tailWord_5919944
  simp only [CollatzResearch.WordTrace]
  refine ⟨107959048032530704393415443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143945397376707605857887257 107959048032530704393415443)
  ·
    refine ⟨161938572048796056590123165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107959048032530704393415443 161938572048796056590123165)
    ·
      refine ⟨60726964518298521221296187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161938572048796056590123165 60726964518298521221296187)
      ·
        refine ⟨91090446777447781831944281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60726964518298521221296187 91090446777447781831944281)
        ·
          refine ⟨68317835083085836373958211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91090446777447781831944281 68317835083085836373958211)
          ·
            refine ⟨102476752624628754560937317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68317835083085836373958211 102476752624628754560937317)
            ·
              refine ⟨19214391117117891480175747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102476752624628754560937317 19214391117117891480175747)
              ·
                refine ⟨28821586675676837220263621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19214391117117891480175747 28821586675676837220263621)
                ·
                  refine ⟨5404047501689406978799429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28821586675676837220263621 5404047501689406978799429)
                  ·
                    refine ⟨1013258906566763808524893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404047501689406978799429 1013258906566763808524893)
                    ·
                      rfl

theorem cell23_5919944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_5919944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919944 prefixEnd_5919944 := by exact prefixLift 5919944
  have htrace : WordTrace (prefixWord ++ tailWord_5919944) baseStart_5919944 baseEnd_5919944 := by
    simpa [prefixWord, tailWord_5919944, baseEnd_5919944] using wordTrace_append hprefix tailTrace_5919944
  have hstable : (prefixWord ++ tailWord_5919944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919944).length < 2 ^ (prefixWord ++ tailWord_5919944).sum := by decide
  have hdescent : baseEnd_5919944 < baseStart_5919944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919947 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_5919947 : Nat := 118140960795 + 5919947 * 2 ^ 59
def prefixEnd_5919947 : Nat := 4983230072969 + 3 ^ 40 * 5919947 * 2
def baseEnd_5919947 : Nat := 3039778260142254913837165

theorem tailTrace_5919947 : CollatzResearch.WordTrace tailWord_5919947 prefixEnd_5919947 3039778260142254913837165 := by
  unfold tailWord_5919947
  simp only [CollatzResearch.WordTrace]
  refine ⟨215918205484050540299190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143945470322700360199460063 215918205484050540299190095)
  ·
    refine ⟨323877308226075810448785143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215918205484050540299190095 323877308226075810448785143)
    ·
      refine ⟨485815962339113715673177715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323877308226075810448785143 485815962339113715673177715)
      ·
        refine ⟨728723943508670573509766573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485815962339113715673177715 728723943508670573509766573)
        ·
          refine ⟨273271478815751465066162465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728723943508670573509766573 273271478815751465066162465)
          ·
            refine ⟨204953609111813598799621849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273271478815751465066162465 204953609111813598799621849)
            ·
              refine ⟨153715206833860199099716387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204953609111813598799621849 153715206833860199099716387)
              ·
                refine ⟨230572810250790298649574581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153715206833860199099716387 230572810250790298649574581)
                ·
                  refine ⟨21616200961011590498397617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230572810250790298649574581 21616200961011590498397617)
                  ·
                    refine ⟨16212150720758692873798213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21616200961011590498397617 16212150720758692873798213)
                    ·
                      refine ⟨3039778260142254913837165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16212150720758692873798213 3039778260142254913837165)
                      ·
                        rfl

theorem cell23_5919947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_5919947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919947 prefixEnd_5919947 := by exact prefixLift 5919947
  have htrace : WordTrace (prefixWord ++ tailWord_5919947) baseStart_5919947 baseEnd_5919947 := by
    simpa [prefixWord, tailWord_5919947, baseEnd_5919947] using wordTrace_append hprefix tailTrace_5919947
  have hstable : (prefixWord ++ tailWord_5919947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919947).length < 2 ^ (prefixWord ++ tailWord_5919947).sum := by decide
  have hdescent : baseEnd_5919947 < baseStart_5919947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919951 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 3, 2, 2]
def baseStart_5919951 : Nat := 118140960795 + 5919951 * 2 ^ 59
def prefixEnd_5919951 : Nat := 4983230072969 + 3 ^ 40 * 5919951 * 2
def baseEnd_5919951 : Nat := 3039780314064872898187147

theorem tailTrace_5919951 : CollatzResearch.WordTrace tailWord_5919951 prefixEnd_5919951 3039780314064872898187147 := by
  unfold tailWord_5919951
  simp only [CollatzResearch.WordTrace]
  refine ⟨215918351376036048982335707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143945567584024032654890471 215918351376036048982335707)
  ·
    refine ⟨323877527064054073473503561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215918351376036048982335707 323877527064054073473503561)
    ·
      refine ⟨242908145298040555105127671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323877527064054073473503561 242908145298040555105127671)
      ·
        refine ⟨364362217947060832657691507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242908145298040555105127671 364362217947060832657691507)
        ·
          refine ⟨546543326920591248986537261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364362217947060832657691507 546543326920591248986537261)
          ·
            refine ⟨204953747595221718369951473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546543326920591248986537261 204953747595221718369951473)
            ·
              refine ⟨153715310696416288777463605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204953747595221718369951473 153715310696416288777463605)
              ·
                refine ⟨14410810377789027072887213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153715310696416288777463605 14410810377789027072887213)
                ·
                  refine ⟨5404053891670885152332705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14410810377789027072887213 5404053891670885152332705)
                  ·
                    refine ⟨4053040418753163864249529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404053891670885152332705 4053040418753163864249529)
                    ·
                      refine ⟨3039780314064872898187147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053040418753163864249529 3039780314064872898187147)
                      ·
                        rfl

theorem cell23_5919951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2, 2].length) (baseStart_5919951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919951 prefixEnd_5919951 := by exact prefixLift 5919951
  have htrace : WordTrace (prefixWord ++ tailWord_5919951) baseStart_5919951 baseEnd_5919951 := by
    simpa [prefixWord, tailWord_5919951, baseEnd_5919951] using wordTrace_append hprefix tailTrace_5919951
  have hstable : (prefixWord ++ tailWord_5919951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919951).length < 2 ^ (prefixWord ++ tailWord_5919951).sum := by decide
  have hdescent : baseEnd_5919951 < baseStart_5919951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919954 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5919954 : Nat := 118140960795 + 5919954 * 2 ^ 59
def prefixEnd_5919954 : Nat := 4983230072969 + 3 ^ 40 * 5919954 * 2
def baseEnd_5919954 : Nat := 3039781854506836386449633

theorem tailTrace_5919954 : CollatzResearch.WordTrace tailWord_5919954 prefixEnd_5919954 3039781854506836386449633 := by
  unfold tailWord_5919954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53979615198756295123673729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143945640530016786996463277 53979615198756295123673729)
  ·
    refine ⟨40484711399067221342755297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53979615198756295123673729 40484711399067221342755297)
    ·
      refine ⟨30363533549300416007066473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40484711399067221342755297 30363533549300416007066473)
      ·
        refine ⟨22772650161975312005299855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30363533549300416007066473 22772650161975312005299855)
        ·
          refine ⟨34158975242962968007949783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772650161975312005299855 34158975242962968007949783)
          ·
            refine ⟨51238462864444452011924675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34158975242962968007949783 51238462864444452011924675)
            ·
              refine ⟨76857694296666678017887013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51238462864444452011924675 76857694296666678017887013)
              ·
                refine ⟨14410817680625002128353815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76857694296666678017887013 14410817680625002128353815)
                ·
                  refine ⟨21616226520937503192530723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14410817680625002128353815 21616226520937503192530723)
                  ·
                    refine ⟨32424339781406254788796085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21616226520937503192530723 32424339781406254788796085)
                    ·
                      refine ⟨3039781854506836386449633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32424339781406254788796085 3039781854506836386449633)
                      ·
                        rfl

theorem cell23_5919954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5919954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919954 prefixEnd_5919954 := by exact prefixLift 5919954
  have htrace : WordTrace (prefixWord ++ tailWord_5919954) baseStart_5919954 baseEnd_5919954 := by
    simpa [prefixWord, tailWord_5919954, baseEnd_5919954] using wordTrace_append hprefix tailTrace_5919954
  have hstable : (prefixWord ++ tailWord_5919954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919954).length < 2 ^ (prefixWord ++ tailWord_5919954).sum := by decide
  have hdescent : baseEnd_5919954 < baseStart_5919954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919965 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5919965 : Nat := 118140960795 + 5919965 * 2 ^ 59
def prefixEnd_5919965 : Nat := 4983230072969 + 3 ^ 40 * 5919965 * 2
def baseEnd_5919965 : Nat := 1013262500931345281137361

theorem tailTrace_5919965 : CollatzResearch.WordTrace tailWord_5919965 prefixEnd_5919965 1013262500931345281137361 := by
  unfold tailWord_5919965
  simp only [CollatzResearch.WordTrace]
  refine ⟨215918861997985329373345349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143945907998656886248896899 215918861997985329373345349)
  ·
    refine ⟨40484786624622249257502253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215918861997985329373345349 40484786624622249257502253)
    ·
      refine ⟨15181794984233343471563345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40484786624622249257502253 15181794984233343471563345)
      ·
        refine ⟨11386346238175007603672509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15181794984233343471563345 11386346238175007603672509)
        ·
          refine ⟨4269879839315627851377191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11386346238175007603672509 4269879839315627851377191)
          ·
            refine ⟨6404819758973441777065787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269879839315627851377191 6404819758973441777065787)
            ·
              refine ⟨9607229638460162665598681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404819758973441777065787 9607229638460162665598681)
              ·
                refine ⟨7205422228845121999199011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9607229638460162665598681 7205422228845121999199011)
                ·
                  refine ⟨10808133343267682998798517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205422228845121999199011 10808133343267682998798517)
                  ·
                    refine ⟨1013262500931345281137361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10808133343267682998798517 1013262500931345281137361)
                    ·
                      rfl

theorem cell23_5919965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5919965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919965 prefixEnd_5919965 := by exact prefixLift 5919965
  have htrace : WordTrace (prefixWord ++ tailWord_5919965) baseStart_5919965 baseEnd_5919965 := by
    simpa [prefixWord, tailWord_5919965, baseEnd_5919965] using wordTrace_append hprefix tailTrace_5919965
  have hstable : (prefixWord ++ tailWord_5919965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919965).length < 2 ^ (prefixWord ++ tailWord_5919965).sum := by decide
  have hdescent : baseEnd_5919965 < baseStart_5919965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919981 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5919981 : Nat := 118140960795 + 5919981 * 2 ^ 59
def prefixEnd_5919981 : Nat := 4983230072969 + 3 ^ 40 * 5919981 * 2
def baseEnd_5919981 : Nat := 3039795718484507780812009

theorem tailTrace_5919981 : CollatzResearch.WordTrace tailWord_5919981 prefixEnd_5919981 3039795718484507780812009 := by
  unfold tailWord_5919981
  simp only [CollatzResearch.WordTrace]
  refine ⟨215919445565927364105927797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143946297043951576070618531 215919445565927364105927797)
  ·
    refine ⟨20242448021805690384930731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215919445565927364105927797 20242448021805690384930731)
    ·
      refine ⟨30363672032708535577396097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20242448021805690384930731 30363672032708535577396097)
      ·
        refine ⟨22772754024531401683047073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30363672032708535577396097 22772754024531401683047073)
        ·
          refine ⟨17079565518398551262285305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22772754024531401683047073 17079565518398551262285305)
          ·
            refine ⟨12809674138798913446713979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17079565518398551262285305 12809674138798913446713979)
            ·
              refine ⟨19214511208198370170070969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12809674138798913446713979 19214511208198370170070969)
              ·
                refine ⟨14410883406148777627553227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19214511208198370170070969 14410883406148777627553227)
                ·
                  refine ⟨21616325109223166441329841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14410883406148777627553227 21616325109223166441329841)
                  ·
                    refine ⟨16212243831917374830997381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21616325109223166441329841 16212243831917374830997381)
                    ·
                      refine ⟨3039795718484507780812009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16212243831917374830997381 3039795718484507780812009)
                      ·
                        rfl

theorem cell23_5919981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5919981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919981 prefixEnd_5919981 := by exact prefixLift 5919981
  have htrace : WordTrace (prefixWord ++ tailWord_5919981) baseStart_5919981 baseEnd_5919981 := by
    simpa [prefixWord, tailWord_5919981, baseEnd_5919981] using wordTrace_append hprefix tailTrace_5919981
  have hstable : (prefixWord ++ tailWord_5919981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919981).length < 2 ^ (prefixWord ++ tailWord_5919981).sum := by decide
  have hdescent : baseEnd_5919981 < baseStart_5919981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5919997 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_5919997 : Nat := 118140960795 + 5919997 * 2 ^ 59
def prefixEnd_5919997 : Nat := 4983230072969 + 3 ^ 40 * 5919997 * 2
def baseEnd_5919997 : Nat := 3039803934174979718211935

theorem tailTrace_5919997 : CollatzResearch.WordTrace tailWord_5919997 prefixEnd_5919997 3039803934174979718211935 := by
  unfold tailWord_5919997
  simp only [CollatzResearch.WordTrace]
  refine ⟨215920029133869398838510245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143946686089246265892340163 215920029133869398838510245)
  ·
    refine ⟨40485005462600512282220671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215920029133869398838510245 40485005462600512282220671)
    ·
      refine ⟨60727508193900768423331007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40485005462600512282220671 60727508193900768423331007)
      ·
        refine ⟨91091262290851152634996511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60727508193900768423331007 91091262290851152634996511)
        ·
          refine ⟨136636893436276728952494767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91091262290851152634996511 136636893436276728952494767)
          ·
            refine ⟨204955340154415093428742151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136636893436276728952494767 204955340154415093428742151)
            ·
              refine ⟨307433010231622640143113227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204955340154415093428742151 307433010231622640143113227)
              ·
                refine ⟨461149515347433960214669841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307433010231622640143113227 461149515347433960214669841)
                ·
                  refine ⟨345862136510575470161002381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461149515347433960214669841 345862136510575470161002381)
                  ·
                    refine ⟨129698301191465801310375893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345862136510575470161002381 129698301191465801310375893)
                    ·
                      refine ⟨3039803934174979718211935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129698301191465801310375893 3039803934174979718211935)
                      ·
                        rfl

theorem cell23_5919997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_5919997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5919997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5919997 prefixEnd_5919997 := by exact prefixLift 5919997
  have htrace : WordTrace (prefixWord ++ tailWord_5919997) baseStart_5919997 baseEnd_5919997 := by
    simpa [prefixWord, tailWord_5919997, baseEnd_5919997] using wordTrace_append hprefix tailTrace_5919997
  have hstable : (prefixWord ++ tailWord_5919997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5919997).length < 2 ^ (prefixWord ++ tailWord_5919997).sum := by decide
  have hdescent : baseEnd_5919997 < baseStart_5919997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5919997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920004 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5920004 : Nat := 118140960795 + 5920004 * 2 ^ 59
def prefixEnd_5920004 : Nat := 4983230072969 + 3 ^ 40 * 5920004 * 2
def baseEnd_5920004 : Nat := 1013269176179853730274801

theorem tailTrace_5920004 : CollatzResearch.WordTrace tailWord_5920004 prefixEnd_5920004 1013269176179853730274801 := by
  unfold tailWord_5920004
  simp only [CollatzResearch.WordTrace]
  refine ⟨107960142222422019517007533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143946856296562692689343377 107960142222422019517007533)
  ·
    refine ⟨40485053333408257318877825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107960142222422019517007533 40485053333408257318877825)
    ·
      refine ⟨30363790000056192989158369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40485053333408257318877825 30363790000056192989158369)
      ·
        refine ⟨22772842500042144741868777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30363790000056192989158369 22772842500042144741868777)
        ·
          refine ⟨17079631875031608556401583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22772842500042144741868777 17079631875031608556401583)
          ·
            refine ⟨25619447812547412834602375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17079631875031608556401583 25619447812547412834602375)
            ·
              refine ⟨38429171718821119251903563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25619447812547412834602375 38429171718821119251903563)
              ·
                refine ⟨57643757578231678877855345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38429171718821119251903563 57643757578231678877855345)
                ·
                  refine ⟨43232818183673759158391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57643757578231678877855345 43232818183673759158391509)
                  ·
                    refine ⟨1013269176179853730274801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43232818183673759158391509 1013269176179853730274801)
                    ·
                      rfl

theorem cell23_5920004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5920004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920004 prefixEnd_5920004 := by exact prefixLift 5920004
  have htrace : WordTrace (prefixWord ++ tailWord_5920004) baseStart_5920004 baseEnd_5920004 := by
    simpa [prefixWord, tailWord_5920004, baseEnd_5920004] using wordTrace_append hprefix tailTrace_5920004
  have hstable : (prefixWord ++ tailWord_5920004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920004).length < 2 ^ (prefixWord ++ tailWord_5920004).sum := by decide
  have hdescent : baseEnd_5920004 < baseStart_5920004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920011 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 3, 3, 2]
def baseStart_5920011 : Nat := 118140960795 + 5920011 * 2 ^ 59
def prefixEnd_5920011 : Nat := 4983230072969 + 3 ^ 40 * 5920011 * 2
def baseEnd_5920011 : Nat := 3039811122904142663436871

theorem tailTrace_5920011 : CollatzResearch.WordTrace tailWord_5920011 prefixEnd_5920011 3039811122904142663436871 := by
  unfold tailWord_5920011
  simp only [CollatzResearch.WordTrace]
  refine ⟨215920539755818679229519887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143947026503879119486346591 215920539755818679229519887)
  ·
    refine ⟨323880809633728018844279831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215920539755818679229519887 323880809633728018844279831)
    ·
      refine ⟨485821214450592028266419747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323880809633728018844279831 485821214450592028266419747)
      ·
        refine ⟨728731821675888042399629621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485821214450592028266419747 728731821675888042399629621)
        ·
          refine ⟨68318608282114503974965277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 728731821675888042399629621 68318608282114503974965277)
          ·
            refine ⟨25619478105792938990611979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68318608282114503974965277 25619478105792938990611979)
            ·
              refine ⟨38429217158689408485917969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25619478105792938990611979 38429217158689408485917969)
              ·
                refine ⟨28821912869017056364438477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38429217158689408485917969 28821912869017056364438477)
                ·
                  refine ⟨10808217325881396136664429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28821912869017056364438477 10808217325881396136664429)
                  ·
                    refine ⟨4053081497205523551249161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10808217325881396136664429 4053081497205523551249161)
                    ·
                      refine ⟨3039811122904142663436871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053081497205523551249161 3039811122904142663436871)
                      ·
                        rfl

theorem cell23_5920011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3, 2].length) (baseStart_5920011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920011 prefixEnd_5920011 := by exact prefixLift 5920011
  have htrace : WordTrace (prefixWord ++ tailWord_5920011) baseStart_5920011 baseEnd_5920011 := by
    simpa [prefixWord, tailWord_5920011, baseEnd_5920011] using wordTrace_append hprefix tailTrace_5920011
  have hstable : (prefixWord ++ tailWord_5920011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920011).length < 2 ^ (prefixWord ++ tailWord_5920011).sum := by decide
  have hdescent : baseEnd_5920011 < baseStart_5920011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920047 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 11]
def baseStart_5920047 : Nat := 118140960795 + 5920047 * 2 ^ 59
def prefixEnd_5920047 : Nat := 4983230072969 + 3 ^ 40 * 5920047 * 2
def baseEnd_5920047 : Nat := 337758845356411613620745

theorem tailTrace_5920047 : CollatzResearch.WordTrace tailWord_5920047 prefixEnd_5920047 337758845356411613620745 := by
  unfold tailWord_5920047
  simp only [CollatzResearch.WordTrace]
  refine ⟨215921852783688257377830395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143947901855792171585220263 215921852783688257377830395)
  ·
    refine ⟨323882779175532386066745593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215921852783688257377830395 323882779175532386066745593)
    ·
      refine ⟨242912084381649289550059195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323882779175532386066745593 242912084381649289550059195)
      ·
        refine ⟨364368126572473934325088793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242912084381649289550059195 364368126572473934325088793)
        ·
          refine ⟨273276094929355450743816595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364368126572473934325088793 273276094929355450743816595)
          ·
            refine ⟨409914142394033176115724893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273276094929355450743816595 409914142394033176115724893)
            ·
              refine ⟨153717803397762441043396835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409914142394033176115724893 153717803397762441043396835)
              ·
                refine ⟨230576705096643661565095253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153717803397762441043396835 230576705096643661565095253)
                ·
                  refine ⟨337758845356411613620745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 230576705096643661565095253 337758845356411613620745)
                  ·
                    rfl

theorem cell23_5920047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 11].length) (baseStart_5920047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920047 prefixEnd_5920047 := by exact prefixLift 5920047
  have htrace : WordTrace (prefixWord ++ tailWord_5920047) baseStart_5920047 baseEnd_5920047 := by
    simpa [prefixWord, tailWord_5920047, baseEnd_5920047] using wordTrace_append hprefix tailTrace_5920047
  have hstable : (prefixWord ++ tailWord_5920047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920047).length < 2 ^ (prefixWord ++ tailWord_5920047).sum := by decide
  have hdescent : baseEnd_5920047 < baseStart_5920047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920058 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_5920058 : Nat := 118140960795 + 5920058 * 2 ^ 59
def prefixEnd_5920058 : Nat := 4983230072969 + 3 ^ 40 * 5920058 * 2
def baseEnd_5920058 : Nat := 3039835256494903979549155

theorem tailTrace_5920058 : CollatzResearch.WordTrace tailWord_5920058 prefixEnd_5920058 3039835256494903979549155 := by
  unfold tailWord_5920058
  simp only [CollatzResearch.WordTrace]
  refine ⟨53980563496662101564120207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143948169324432270837653885 53980563496662101564120207)
  ·
    refine ⟨80970845244993152346180311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53980563496662101564120207 80970845244993152346180311)
    ·
      refine ⟨121456267867489728519270467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80970845244993152346180311 121456267867489728519270467)
      ·
        refine ⟨182184401801234592778905701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121456267867489728519270467 182184401801234592778905701)
        ·
          refine ⟨34159575337731486146044819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182184401801234592778905701 34159575337731486146044819)
          ·
            refine ⟨51239363006597229219067229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34159575337731486146044819 51239363006597229219067229)
            ·
              refine ⟨19214761127473960957150211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51239363006597229219067229 19214761127473960957150211)
              ·
                refine ⟨28822141691210941435725317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19214761127473960957150211 28822141691210941435725317)
                ·
                  refine ⟨5404151567102051519198497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28822141691210941435725317 5404151567102051519198497)
                  ·
                    refine ⟨4053113675326538639398873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404151567102051519198497 4053113675326538639398873)
                    ·
                      refine ⟨3039835256494903979549155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053113675326538639398873 3039835256494903979549155)
                      ·
                        rfl

theorem cell23_5920058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_5920058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920058 prefixEnd_5920058 := by exact prefixLift 5920058
  have htrace : WordTrace (prefixWord ++ tailWord_5920058) baseStart_5920058 baseEnd_5920058 := by
    simpa [prefixWord, tailWord_5920058, baseEnd_5920058] using wordTrace_append hprefix tailTrace_5920058
  have hstable : (prefixWord ++ tailWord_5920058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920058).length < 2 ^ (prefixWord ++ tailWord_5920058).sum := by decide
  have hdescent : baseEnd_5920058 < baseStart_5920058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920064 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 7]
def baseStart_5920064 : Nat := 118140960795 + 5920064 * 2 ^ 59
def prefixEnd_5920064 : Nat := 4983230072969 + 3 ^ 40 * 5920064 * 2
def baseEnd_5920064 : Nat := 337759815264314550674903

theorem tailTrace_5920064 : CollatzResearch.WordTrace tailWord_5920064 prefixEnd_5920064 337759815264314550674903 := by
  unfold tailWord_5920064
  simp only [CollatzResearch.WordTrace]
  refine ⟨107961236412313334640599623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143948315216417779520799497 107961236412313334640599623)
  ·
    refine ⟨161941854618470001960899435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107961236412313334640599623 161941854618470001960899435)
    ·
      refine ⟨242912781927705002941349153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161941854618470001960899435 242912781927705002941349153)
      ·
        refine ⟨182184586445778752206011865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242912781927705002941349153 182184586445778752206011865)
        ·
          refine ⟨136638439834334064154508899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182184586445778752206011865 136638439834334064154508899)
          ·
            refine ⟨204957659751501096231763349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136638439834334064154508899 204957659751501096231763349)
            ·
              refine ⟨9607390300851613885863907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204957659751501096231763349 9607390300851613885863907)
              ·
                refine ⟨14411085451277420828795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9607390300851613885863907 14411085451277420828795861)
                ·
                  refine ⟨337759815264314550674903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14411085451277420828795861 337759815264314550674903)
                  ·
                    rfl

theorem cell23_5920064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_5920064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920064 prefixEnd_5920064 := by exact prefixLift 5920064
  have htrace : WordTrace (prefixWord ++ tailWord_5920064) baseStart_5920064 baseEnd_5920064 := by
    simpa [prefixWord, tailWord_5920064, baseEnd_5920064] using wordTrace_append hprefix tailTrace_5920064
  have hstable : (prefixWord ++ tailWord_5920064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920064).length < 2 ^ (prefixWord ++ tailWord_5920064).sum := by decide
  have hdescent : baseEnd_5920064 < baseStart_5920064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920148 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5920148 : Nat := 118140960795 + 5920148 * 2 ^ 59
def prefixEnd_5920148 : Nat := 4983230072969 + 3 ^ 40 * 5920148 * 2
def baseEnd_5920148 : Nat := 3039881469753808627423741

theorem tailTrace_5920148 : CollatzResearch.WordTrace tailWord_5920148 prefixEnd_5920148 3039881469753808627423741 := by
  unfold tailWord_5920148
  simp only [CollatzResearch.WordTrace]
  refine ⟨107962768278161175813628549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143950357704214901084838065 107962768278161175813628549)
  ·
    refine ⟨20243019052155220465055353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107962768278161175813628549 20243019052155220465055353)
    ·
      refine ⟨15182264289116415348791515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20243019052155220465055353 15182264289116415348791515)
      ·
        refine ⟨22773396433674623023187273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15182264289116415348791515 22773396433674623023187273)
        ·
          refine ⟨17080047325255967267390455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22773396433674623023187273 17080047325255967267390455)
          ·
            refine ⟨25620070987883950901085683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17080047325255967267390455 25620070987883950901085683)
            ·
              refine ⟨38430106481825926351628525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25620070987883950901085683 38430106481825926351628525)
              ·
                refine ⟨14411289930684722381860697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38430106481825926351628525 14411289930684722381860697)
                ·
                  refine ⟨10808467448013541786395523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14411289930684722381860697 10808467448013541786395523)
                  ·
                    refine ⟨16212701172020312679593285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10808467448013541786395523 16212701172020312679593285)
                    ·
                      refine ⟨3039881469753808627423741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16212701172020312679593285 3039881469753808627423741)
                      ·
                        rfl

theorem cell23_5920148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5920148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920148 prefixEnd_5920148 := by exact prefixLift 5920148
  have htrace : WordTrace (prefixWord ++ tailWord_5920148) baseStart_5920148 baseEnd_5920148 := by
    simpa [prefixWord, tailWord_5920148, baseEnd_5920148] using wordTrace_append hprefix tailTrace_5920148
  have hstable : (prefixWord ++ tailWord_5920148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920148).length < 2 ^ (prefixWord ++ tailWord_5920148).sum := by decide
  have hdescent : baseEnd_5920148 < baseStart_5920148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920201 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_5920201 : Nat := 118140960795 + 5920201 * 2 ^ 59
def prefixEnd_5920201 : Nat := 4983230072969 + 3 ^ 40 * 5920201 * 2
def baseEnd_5920201 : Nat := 1013302894742832306686999

theorem tailTrace_5920201 : CollatzResearch.WordTrace tailWord_5920201 prefixEnd_5920201 1013302894742832306686999 := by
  unfold tailWord_5920201
  simp only [CollatzResearch.WordTrace]
  refine ⟨215927469625130341678936457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143951646416753561119290971 215927469625130341678936457)
  ·
    refine ⟨161945602218847756259202343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215927469625130341678936457 161945602218847756259202343)
    ·
      refine ⟨242918403328271634388803515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161945602218847756259202343 242918403328271634388803515)
      ·
        refine ⟨364377604992407451583205273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242918403328271634388803515 364377604992407451583205273)
        ·
          refine ⟨273283203744305588687403955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364377604992407451583205273 273283203744305588687403955)
          ·
            refine ⟨409924805616458383031105933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273283203744305588687403955 409924805616458383031105933)
            ·
              refine ⟨153721802106171893636664725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409924805616458383031105933 153721802106171893636664725)
              ·
                refine ⟨7205709473726807514218659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153721802106171893636664725 7205709473726807514218659)
                ·
                  refine ⟨10808564210590211271327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205709473726807514218659 10808564210590211271327989)
                  ·
                    refine ⟨1013302894742832306686999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10808564210590211271327989 1013302894742832306686999)
                    ·
                      rfl

theorem cell23_5920201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_5920201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920201 prefixEnd_5920201 := by exact prefixLift 5920201
  have htrace : WordTrace (prefixWord ++ tailWord_5920201) baseStart_5920201 baseEnd_5920201 := by
    simpa [prefixWord, tailWord_5920201, baseEnd_5920201] using wordTrace_append hprefix tailTrace_5920201
  have hstable : (prefixWord ++ tailWord_5920201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920201).length < 2 ^ (prefixWord ++ tailWord_5920201).sum := by decide
  have hdescent : baseEnd_5920201 < baseStart_5920201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920218 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_5920218 : Nat := 118140960795 + 5920218 * 2 ^ 59
def prefixEnd_5920218 : Nat := 4983230072969 + 3 ^ 40 * 5920218 * 2
def baseEnd_5920218 : Nat := 1013305804466541117849473

theorem tailTrace_5920218 : CollatzResearch.WordTrace tailWord_5920218 prefixEnd_5920218 1013305804466541117849473 := by
  unfold tailWord_5920218
  simp only [CollatzResearch.WordTrace]
  refine ⟨53982022416517188395576327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143952059777379169054870205 53982022416517188395576327)
  ·
    refine ⟨80973033624775782593364491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53982022416517188395576327 80973033624775782593364491)
    ·
      refine ⟨121459550437163673890046737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80973033624775782593364491 121459550437163673890046737)
      ·
        refine ⟨91094662827872755417535053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121459550437163673890046737 91094662827872755417535053)
        ·
          refine ⟨34160498560452283281575645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91094662827872755417535053 34160498560452283281575645)
          ·
            refine ⟨12810186960169606230590867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34160498560452283281575645 12810186960169606230590867)
            ·
              refine ⟨19215280440254409345886301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12810186960169606230590867 19215280440254409345886301)
              ·
                refine ⟨7205730165095403504707363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19215280440254409345886301 7205730165095403504707363)
                ·
                  refine ⟨10808595247643105257061045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205730165095403504707363 10808595247643105257061045)
                  ·
                    refine ⟨1013305804466541117849473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10808595247643105257061045 1013305804466541117849473)
                    ·
                      rfl

theorem cell23_5920218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_5920218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920218 prefixEnd_5920218 := by exact prefixLift 5920218
  have htrace : WordTrace (prefixWord ++ tailWord_5920218) baseStart_5920218 baseEnd_5920218 := by
    simpa [prefixWord, tailWord_5920218, baseEnd_5920218] using wordTrace_append hprefix tailTrace_5920218
  have hstable : (prefixWord ++ tailWord_5920218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920218).length < 2 ^ (prefixWord ++ tailWord_5920218).sum := by decide
  have hdescent : baseEnd_5920218 < baseStart_5920218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920241 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_5920241 : Nat := 118140960795 + 5920241 * 2 ^ 59
def prefixEnd_5920241 : Nat := 4983230072969 + 3 ^ 40 * 5920241 * 2
def baseEnd_5920241 : Nat := 3039929223454676763560813

theorem tailTrace_5920241 : CollatzResearch.WordTrace tailWord_5920241 prefixEnd_5920241 3039929223454676763560813 := by
  unfold tailWord_5920241
  simp only [CollatzResearch.WordTrace]
  refine ⟨215928928544985428510392577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143952619029990285673595051 215928928544985428510392577)
  ·
    refine ⟨161946696408739071382794433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215928928544985428510392577 161946696408739071382794433)
    ·
      refine ⟨121460022306554303537095825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161946696408739071382794433 121460022306554303537095825)
      ·
        refine ⟨91095016729915727652821869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121460022306554303537095825 91095016729915727652821869)
        ·
          refine ⟨34160631273718397869808201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91095016729915727652821869 34160631273718397869808201)
          ·
            refine ⟨25620473455288798402356151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34160631273718397869808201 25620473455288798402356151)
            ·
              refine ⟨38430710182933197603534227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25620473455288798402356151 38430710182933197603534227)
              ·
                refine ⟨57646065274399796405301341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38430710182933197603534227 57646065274399796405301341)
                ·
                  refine ⟨21617274477899923651988003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57646065274399796405301341 21617274477899923651988003)
                  ·
                    refine ⟨32425911716849885477982005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21617274477899923651988003 32425911716849885477982005)
                    ·
                      refine ⟨3039929223454676763560813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32425911716849885477982005 3039929223454676763560813)
                      ·
                        rfl

theorem cell23_5920241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_5920241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920241 prefixEnd_5920241 := by exact prefixLift 5920241
  have htrace : WordTrace (prefixWord ++ tailWord_5920241) baseStart_5920241 baseEnd_5920241 := by
    simpa [prefixWord, tailWord_5920241, baseEnd_5920241] using wordTrace_append hprefix tailTrace_5920241
  have hstable : (prefixWord ++ tailWord_5920241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920241).length < 2 ^ (prefixWord ++ tailWord_5920241).sum := by decide
  have hdescent : baseEnd_5920241 < baseStart_5920241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920248 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_5920248 : Nat := 118140960795 + 5920248 * 2 ^ 59
def prefixEnd_5920248 : Nat := 4983230072969 + 3 ^ 40 * 5920248 * 2
def baseEnd_5920248 : Nat := 1013310939273086078724427

theorem tailTrace_5920248 : CollatzResearch.WordTrace tailWord_5920248 prefixEnd_5920248 1013310939273086078724427 := by
  unfold tailWord_5920248
  simp only [CollatzResearch.WordTrace]
  refine ⟨107964591927980034352948699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143952789237306712470598265 107964591927980034352948699)
  ·
    refine ⟨161946887891970051529423049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107964591927980034352948699 161946887891970051529423049)
    ·
      refine ⟨121460165918977538647067287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161946887891970051529423049 121460165918977538647067287)
      ·
        refine ⟨182190248878466307970600931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121460165918977538647067287 182190248878466307970600931)
        ·
          refine ⟨273285373317699461955901397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182190248878466307970600931 273285373317699461955901397)
          ·
            refine ⟨6405125937133581139591439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 273285373317699461955901397 6405125937133581139591439)
            ·
              refine ⟨9607688905700371709387159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405125937133581139591439 9607688905700371709387159)
              ·
                refine ⟨14411533358550557564080739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9607688905700371709387159 14411533358550557564080739)
                ·
                  refine ⟨21617300037825836346121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14411533358550557564080739 21617300037825836346121109)
                  ·
                    refine ⟨1013310939273086078724427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21617300037825836346121109 1013310939273086078724427)
                    ·
                      rfl

theorem cell23_5920248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_5920248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920248 prefixEnd_5920248 := by exact prefixLift 5920248
  have htrace : WordTrace (prefixWord ++ tailWord_5920248) baseStart_5920248 baseEnd_5920248 := by
    simpa [prefixWord, tailWord_5920248, baseEnd_5920248] using wordTrace_append hprefix tailTrace_5920248
  have hstable : (prefixWord ++ tailWord_5920248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920248).length < 2 ^ (prefixWord ++ tailWord_5920248).sum := by decide
  have hdescent : baseEnd_5920248 < baseStart_5920248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920326 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5920326 : Nat := 118140960795 + 5920326 * 2 ^ 59
def prefixEnd_5920326 : Nat := 4983230072969 + 3 ^ 40 * 5920326 * 2
def baseEnd_5920326 : Nat := 3039972869310308930997923

theorem tailTrace_5920326 : CollatzResearch.WordTrace tailWord_5920326 prefixEnd_5920326 3039972869310308930997923 := by
  unfold tailWord_5920326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747875898427421500851151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143954685833118325351491221 6747875898427421500851151)
  ·
    refine ⟨10121813847641132251276727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747875898427421500851151 10121813847641132251276727)
    ·
      refine ⟨15182720771461698376915091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10121813847641132251276727 15182720771461698376915091)
      ·
        refine ⟨22774081157192547565372637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15182720771461698376915091 22774081157192547565372637)
        ·
          refine ⟨8540280433947205337014739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22774081157192547565372637 8540280433947205337014739)
          ·
            refine ⟨12810420650920808005522109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8540280433947205337014739 12810420650920808005522109)
            ·
              refine ⟨4803907744095303002070791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12810420650920808005522109 4803907744095303002070791)
              ·
                refine ⟨7205861616142954503106187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803907744095303002070791 7205861616142954503106187)
                ·
                  refine ⟨10808792424214431754659281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205861616142954503106187 10808792424214431754659281)
                  ·
                    refine ⟨8106594318160823815994461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10808792424214431754659281 8106594318160823815994461)
                    ·
                      refine ⟨3039972869310308930997923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8106594318160823815994461 3039972869310308930997923)
                      ·
                        rfl

theorem cell23_5920326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5920326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920326 prefixEnd_5920326 := by exact prefixLift 5920326
  have htrace : WordTrace (prefixWord ++ tailWord_5920326) baseStart_5920326 baseEnd_5920326 := by
    simpa [prefixWord, tailWord_5920326, baseEnd_5920326] using wordTrace_append hprefix tailTrace_5920326
  have hstable : (prefixWord ++ tailWord_5920326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920326).length < 2 ^ (prefixWord ++ tailWord_5920326).sum := by decide
  have hdescent : baseEnd_5920326 < baseStart_5920326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920341 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5920341 : Nat := 118140960795 + 5920341 * 2 ^ 59
def prefixEnd_5920341 : Nat := 4983230072969 + 3 ^ 40 * 5920341 * 2
def baseEnd_5920341 : Nat := 3039980571520126372310353

theorem tailTrace_5920341 : CollatzResearch.WordTrace tailWord_5920341 prefixEnd_5920341 3039980571520126372310353 := by
  unfold tailWord_5920341
  simp only [CollatzResearch.WordTrace]
  refine ⟨215932575844623145589032877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143955050563082097059355251 215932575844623145589032877)
  ·
    refine ⟨80974715941733679595887329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215932575844623145589032877 80974715941733679595887329)
    ·
      refine ⟨60731036956300259696915497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80974715941733679595887329 60731036956300259696915497)
      ·
        refine ⟨45548277717225194772686623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60731036956300259696915497 45548277717225194772686623)
        ·
          refine ⟨68322416575837792159029935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45548277717225194772686623 68322416575837792159029935)
          ·
            refine ⟨102483624863756688238544903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68322416575837792159029935 102483624863756688238544903)
            ·
              refine ⟨153725437295635032357817355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102483624863756688238544903 153725437295635032357817355)
              ·
                refine ⟨230588155943452548536726033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153725437295635032357817355 230588155943452548536726033)
                ·
                  refine ⟨172941116957589411402544525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230588155943452548536726033 172941116957589411402544525)
                  ·
                    refine ⟨64852918859096029275954197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172941116957589411402544525 64852918859096029275954197)
                    ·
                      refine ⟨3039980571520126372310353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64852918859096029275954197 3039980571520126372310353)
                      ·
                        rfl

theorem cell23_5920341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5920341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920341 prefixEnd_5920341 := by exact prefixLift 5920341
  have htrace : WordTrace (prefixWord ++ tailWord_5920341) baseStart_5920341 baseEnd_5920341 := by
    simpa [prefixWord, tailWord_5920341, baseEnd_5920341] using wordTrace_append hprefix tailTrace_5920341
  have hstable : (prefixWord ++ tailWord_5920341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920341).length < 2 ^ (prefixWord ++ tailWord_5920341).sum := by decide
  have hdescent : baseEnd_5920341 < baseStart_5920341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920345 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 4, 2, 2]
def baseStart_5920345 : Nat := 118140960795 + 5920345 * 2 ^ 59
def prefixEnd_5920345 : Nat := 4983230072969 + 3 ^ 40 * 5920345 * 2
def baseEnd_5920345 : Nat := 3039982625442744356660335

theorem tailTrace_5920345 : CollatzResearch.WordTrace tailWord_5920345 prefixEnd_5920345 3039982625442744356660335 := by
  unfold tailWord_5920345
  simp only [CollatzResearch.WordTrace]
  refine ⟨215932721736608654272178489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143955147824405769514785659 215932721736608654272178489)
  ·
    refine ⟨161949541302456490704133867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215932721736608654272178489 161949541302456490704133867)
    ·
      refine ⟨242924311953684736056200801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161949541302456490704133867 242924311953684736056200801)
      ·
        refine ⟨182193233965263552042150601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242924311953684736056200801 182193233965263552042150601)
        ·
          refine ⟨136644925473947664031612951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182193233965263552042150601 136644925473947664031612951)
          ·
            refine ⟨204967388210921496047419427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136644925473947664031612951 204967388210921496047419427)
            ·
              refine ⟨307451082316382244071129141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204967388210921496047419427 307451082316382244071129141)
              ·
                refine ⟨28823538967160835381668357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307451082316382244071129141 28823538967160835381668357)
                ·
                  refine ⟨5404413556342656634062817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28823538967160835381668357 5404413556342656634062817)
                  ·
                    refine ⟨4053310167256992475547113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404413556342656634062817 4053310167256992475547113)
                    ·
                      refine ⟨3039982625442744356660335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053310167256992475547113 3039982625442744356660335)
                      ·
                        rfl

theorem cell23_5920345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_5920345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920345 prefixEnd_5920345 := by exact prefixLift 5920345
  have htrace : WordTrace (prefixWord ++ tailWord_5920345) baseStart_5920345 baseEnd_5920345 := by
    simpa [prefixWord, tailWord_5920345, baseEnd_5920345] using wordTrace_append hprefix tailTrace_5920345
  have hstable : (prefixWord ++ tailWord_5920345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920345).length < 2 ^ (prefixWord ++ tailWord_5920345).sum := by decide
  have hdescent : baseEnd_5920345 < baseStart_5920345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920362 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5920362 : Nat := 118140960795 + 5920362 * 2 ^ 59
def prefixEnd_5920362 : Nat := 4983230072969 + 3 ^ 40 * 5920362 * 2
def baseEnd_5920362 : Nat := 3039991354613870790147757

theorem tailTrace_5920362 : CollatzResearch.WordTrace tailWord_5920362 prefixEnd_5920362 3039991354613870790147757 := by
  unfold tailWord_5920362
  simp only [CollatzResearch.WordTrace]
  refine ⟨53983335444386766543886835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143955561185031377450364893 53983335444386766543886835)
  ·
    refine ⟨80975003166580149815830253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53983335444386766543886835 80975003166580149815830253)
    ·
      refine ⟨30365626187467556180936345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80975003166580149815830253 30365626187467556180936345)
      ·
        refine ⟨22774219640600667135702259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30365626187467556180936345 22774219640600667135702259)
        ·
          refine ⟨34161329460901000703553389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22774219640600667135702259 34161329460901000703553389)
          ·
            refine ⟨12810498547837875263832521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34161329460901000703553389 12810498547837875263832521)
            ·
              refine ⟨9607873910878406447874391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12810498547837875263832521 9607873910878406447874391)
              ·
                refine ⟨14411810866317609671811587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9607873910878406447874391 14411810866317609671811587)
                ·
                  refine ⟨21617716299476414507717381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14411810866317609671811587 21617716299476414507717381)
                  ·
                    refine ⟨4053321806151827720197009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21617716299476414507717381 4053321806151827720197009)
                    ·
                      refine ⟨3039991354613870790147757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053321806151827720197009 3039991354613870790147757)
                      ·
                        rfl

theorem cell23_5920362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5920362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920362 prefixEnd_5920362 := by exact prefixLift 5920362
  have htrace : WordTrace (prefixWord ++ tailWord_5920362) baseStart_5920362 baseEnd_5920362 := by
    simpa [prefixWord, tailWord_5920362, baseEnd_5920362] using wordTrace_append hprefix tailTrace_5920362
  have hstable : (prefixWord ++ tailWord_5920362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920362).length < 2 ^ (prefixWord ++ tailWord_5920362).sum := by decide
  have hdescent : baseEnd_5920362 < baseStart_5920362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920368 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 7]
def baseStart_5920368 : Nat := 118140960795 + 5920368 * 2 ^ 59
def prefixEnd_5920368 : Nat := 4983230072969 + 3 ^ 40 * 5920368 * 2
def baseEnd_5920368 : Nat := 337777159499755307408081

theorem tailTrace_5920368 : CollatzResearch.WordTrace tailWord_5920368 prefixEnd_5920368 337777159499755307408081 := by
  unfold tailWord_5920368
  simp only [CollatzResearch.WordTrace]
  refine ⟨107966780307762664600132879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143955707077016886133510505 107966780307762664600132879)
  ·
    refine ⟨161950170461643996900199319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107966780307762664600132879 161950170461643996900199319)
    ·
      refine ⟨242925255692465995350298979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161950170461643996900199319 242925255692465995350298979)
      ·
        refine ⟨364387883538698993025448469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242925255692465995350298979 364387883538698993025448469)
        ·
          refine ⟨17080682040876515298067897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 364387883538698993025448469 17080682040876515298067897)
          ·
            refine ⟨12810511530657386473550923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17080682040876515298067897 12810511530657386473550923)
            ·
              refine ⟨19215767295986079710326385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12810511530657386473550923 19215767295986079710326385)
              ·
                refine ⟨14411825471989559782744789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19215767295986079710326385 14411825471989559782744789)
                ·
                  refine ⟨337777159499755307408081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14411825471989559782744789 337777159499755307408081)
                  ·
                    rfl

theorem cell23_5920368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_5920368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920368 prefixEnd_5920368 := by exact prefixLift 5920368
  have htrace : WordTrace (prefixWord ++ tailWord_5920368) baseStart_5920368 baseEnd_5920368 := by
    simpa [prefixWord, tailWord_5920368, baseEnd_5920368] using wordTrace_append hprefix tailTrace_5920368
  have hstable : (prefixWord ++ tailWord_5920368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920368).length < 2 ^ (prefixWord ++ tailWord_5920368).sum := by decide
  have hdescent : baseEnd_5920368 < baseStart_5920368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920385 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 5]
def baseStart_5920385 : Nat := 118140960795 + 5920385 * 2 ^ 59
def prefixEnd_5920385 : Nat := 4983230072969 + 3 ^ 40 * 5920385 * 2
def baseEnd_5920385 : Nat := 337778129407658244462239

theorem tailTrace_5920385 : CollatzResearch.WordTrace tailWord_5920385 prefixEnd_5920385 337778129407658244462239 := by
  unfold tailWord_5920385
  simp only [CollatzResearch.WordTrace]
  refine ⟨215934180656463741103634609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143956120437642494069089739 215934180656463741103634609)
  ·
    refine ⟨161950635492347805827725957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215934180656463741103634609 161950635492347805827725957)
    ·
      refine ⟨30365744154815213592698617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161950635492347805827725957 30365744154815213592698617)
      ·
        refine ⟨22774308116111410194523963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30365744154815213592698617 22774308116111410194523963)
        ·
          refine ⟨34161462174167115291785945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22774308116111410194523963 34161462174167115291785945)
          ·
            refine ⟨25621096630625336468839459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34161462174167115291785945 25621096630625336468839459)
            ·
              refine ⟨38431644945938004703259189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25621096630625336468839459 38431644945938004703259189)
              ·
                refine ⟨3602966713681687940930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38431644945938004703259189 3602966713681687940930549)
                ·
                  refine ⟨337778129407658244462239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3602966713681687940930549 337778129407658244462239)
                  ·
                    rfl

theorem cell23_5920385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 5].length) (baseStart_5920385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920385 prefixEnd_5920385 := by exact prefixLift 5920385
  have htrace : WordTrace (prefixWord ++ tailWord_5920385) baseStart_5920385 baseEnd_5920385 := by
    simpa [prefixWord, tailWord_5920385, baseEnd_5920385] using wordTrace_append hprefix tailTrace_5920385
  have hstable : (prefixWord ++ tailWord_5920385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920385).length < 2 ^ (prefixWord ++ tailWord_5920385).sum := by decide
  have hdescent : baseEnd_5920385 < baseStart_5920385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920455 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_5920455 : Nat := 118140960795 + 5920455 * 2 ^ 59
def prefixEnd_5920455 : Nat := 4983230072969 + 3 ^ 40 * 5920455 * 2
def baseEnd_5920455 : Nat := 3040039108314738926284829

theorem tailTrace_5920455 : CollatzResearch.WordTrace tailWord_5920455 prefixEnd_5920455 3040039108314738926284829 := by
  unfold tailWord_5920455
  simp only [CollatzResearch.WordTrace]
  refine ⟨215936733766210143058682819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143957822510806762039121879 215936733766210143058682819)
  ·
    refine ⟨323905100649315214588024229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215936733766210143058682819 323905100649315214588024229)
    ·
      refine ⟨60732206371746602735254543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323905100649315214588024229 60732206371746602735254543)
      ·
        refine ⟨91098309557619904102881815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60732206371746602735254543 91098309557619904102881815)
        ·
          refine ⟨136647464336429856154322723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91098309557619904102881815 136647464336429856154322723)
          ·
            refine ⟨204971196504644784231484085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136647464336429856154322723 204971196504644784231484085)
            ·
              refine ⟨19216049672310448521701633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204971196504644784231484085 19216049672310448521701633)
              ·
                refine ⟨14412037254232836391276225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19216049672310448521701633 14412037254232836391276225)
                ·
                  refine ⟨10809027940674627293457169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14412037254232836391276225 10809027940674627293457169)
                  ·
                    refine ⟨8106770955505970470092877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10809027940674627293457169 8106770955505970470092877)
                    ·
                      refine ⟨3040039108314738926284829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8106770955505970470092877 3040039108314738926284829)
                      ·
                        rfl

theorem cell23_5920455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_5920455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920455 prefixEnd_5920455 := by exact prefixLift 5920455
  have htrace : WordTrace (prefixWord ++ tailWord_5920455) baseStart_5920455 baseEnd_5920455 := by
    simpa [prefixWord, tailWord_5920455, baseEnd_5920455] using wordTrace_append hprefix tailTrace_5920455
  have hstable : (prefixWord ++ tailWord_5920455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920455).length < 2 ^ (prefixWord ++ tailWord_5920455).sum := by decide
  have hdescent : baseEnd_5920455 < baseStart_5920455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920535 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 6]
def baseStart_5920535 : Nat := 118140960795 + 5920535 * 2 ^ 59
def prefixEnd_5920535 : Nat := 4983230072969 + 3 ^ 40 * 5920535 * 2
def baseEnd_5920535 : Nat := 1013360062255699537761487

theorem tailTrace_5920535 : CollatzResearch.WordTrace tailWord_5920535 prefixEnd_5920535 1013360062255699537761487 := by
  unfold tailWord_5920535
  simp only [CollatzResearch.WordTrace]
  refine ⟨215939651605920316721595059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143959767737280211147730039 215939651605920316721595059)
  ·
    refine ⟨323909477408880475082392589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215939651605920316721595059 323909477408880475082392589)
    ·
      refine ⟨121466054028330178155897221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323909477408880475082392589 121466054028330178155897221)
      ·
        refine ⟨22774885130311908404230729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121466054028330178155897221 22774885130311908404230729)
        ·
          refine ⟨17081163847733931303173047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22774885130311908404230729 17081163847733931303173047)
          ·
            refine ⟨25621745771600896954759571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081163847733931303173047 25621745771600896954759571)
            ·
              refine ⟨38432618657401345432139357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25621745771600896954759571 38432618657401345432139357)
              ·
                refine ⟨14412231996525504537052259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38432618657401345432139357 14412231996525504537052259)
                ·
                  refine ⟨21618347994788256805578389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14412231996525504537052259 21618347994788256805578389)
                  ·
                    refine ⟨1013360062255699537761487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21618347994788256805578389 1013360062255699537761487)
                    ·
                      rfl

theorem cell23_5920535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_5920535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920535 prefixEnd_5920535 := by exact prefixLift 5920535
  have htrace : WordTrace (prefixWord ++ tailWord_5920535) baseStart_5920535 baseEnd_5920535 := by
    simpa [prefixWord, tailWord_5920535, baseEnd_5920535] using wordTrace_append hprefix tailTrace_5920535
  have hstable : (prefixWord ++ tailWord_5920535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920535).length < 2 ^ (prefixWord ++ tailWord_5920535).sum := by decide
  have hdescent : baseEnd_5920535 < baseStart_5920535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920565 : List Nat := [1, 3, 3, 1, 4, 1, 10]
def baseStart_5920565 : Nat := 118140960795 + 5920565 * 2 ^ 59
def prefixEnd_5920565 : Nat := 4983230072969 + 3 ^ 40 * 5920565 * 2
def baseEnd_5920565 : Nat := 37532044335638685134683

theorem tailTrace_5920565 : CollatzResearch.WordTrace tailWord_5920565 prefixEnd_5920565 37532044335638685134683 := by
  unfold tailWord_5920565
  simp only [CollatzResearch.WordTrace]
  refine ⟨215940745795811631845187149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143960497197207754563458099 215940745795811631845187149)
  ·
    refine ⟨80977779673429361941945181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215940745795811631845187149 80977779673429361941945181)
    ·
      refine ⟨30366667377536010728229443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80977779673429361941945181 30366667377536010728229443)
      ·
        refine ⟨45550001066304016092344165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30366667377536010728229443 45550001066304016092344165)
        ·
          refine ⟨8540625199932003017314531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45550001066304016092344165 8540625199932003017314531)
          ·
            refine ⟨12810937799898004525971797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8540625199932003017314531 12810937799898004525971797)
            ·
              refine ⟨37532044335638685134683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12810937799898004525971797 37532044335638685134683)
              ·
                rfl

theorem cell23_5920565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 10].length) (baseStart_5920565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920565 prefixEnd_5920565 := by exact prefixLift 5920565
  have htrace : WordTrace (prefixWord ++ tailWord_5920565) baseStart_5920565 baseEnd_5920565 := by
    simpa [prefixWord, tailWord_5920565, baseEnd_5920565] using wordTrace_append hprefix tailTrace_5920565
  have hstable : (prefixWord ++ tailWord_5920565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920565).length < 2 ^ (prefixWord ++ tailWord_5920565).sum := by decide
  have hdescent : baseEnd_5920565 < baseStart_5920565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920569 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_5920569 : Nat := 118140960795 + 5920569 * 2 ^ 59
def prefixEnd_5920569 : Nat := 4983230072969 + 3 ^ 40 * 5920569 * 2
def baseEnd_5920569 : Nat := 1013365881703117160086435

theorem tailTrace_5920569 : CollatzResearch.WordTrace tailWord_5920569 prefixEnd_5920569 1013365881703117160086435 := by
  unfold tailWord_5920569
  simp only [CollatzResearch.WordTrace]
  refine ⟨215940891687797140528332761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143960594458531427018888507 215940891687797140528332761)
  ·
    refine ⟨161955668765847855396249571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215940891687797140528332761 161955668765847855396249571)
    ·
      refine ⟨242933503148771783094374357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161955668765847855396249571 242933503148771783094374357)
      ·
        refine ⟨5693753980049338666274399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 242933503148771783094374357 5693753980049338666274399)
        ·
          refine ⟨8540630970074007999411599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693753980049338666274399 8540630970074007999411599)
          ·
            refine ⟨12810946455111011999117399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8540630970074007999411599 12810946455111011999117399)
            ·
              refine ⟨19216419682666517998676099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12810946455111011999117399 19216419682666517998676099)
              ·
                refine ⟨28824629523999776998014149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19216419682666517998676099 28824629523999776998014149)
                ·
                  refine ⟨5404618035749958187127653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28824629523999776998014149 5404618035749958187127653)
                  ·
                    refine ⟨1013365881703117160086435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404618035749958187127653 1013365881703117160086435)
                    ·
                      rfl

theorem cell23_5920569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_5920569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920569 prefixEnd_5920569 := by exact prefixLift 5920569
  have htrace : WordTrace (prefixWord ++ tailWord_5920569) baseStart_5920569 baseEnd_5920569 := by
    simpa [prefixWord, tailWord_5920569, baseEnd_5920569] using wordTrace_append hprefix tailTrace_5920569
  have hstable : (prefixWord ++ tailWord_5920569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920569).length < 2 ^ (prefixWord ++ tailWord_5920569).sum := by decide
  have hdescent : baseEnd_5920569 < baseStart_5920569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920589 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5920589 : Nat := 118140960795 + 5920589 * 2 ^ 59
def prefixEnd_5920589 : Nat := 4983230072969 + 3 ^ 40 * 5920589 * 2
def baseEnd_5920589 : Nat := 3040107914722441402009213

theorem tailTrace_5920589 : CollatzResearch.WordTrace tailWord_5920589 prefixEnd_5920589 3040107914722441402009213 := by
  unfold tailWord_5920589
  simp only [CollatzResearch.WordTrace]
  refine ⟨215941621147724683944060821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143961080765149789296040547 215941621147724683944060821)
  ·
    refine ⟨10122263491299594559877851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 215941621147724683944060821 10122263491299594559877851)
    ·
      refine ⟨15183395236949391839816777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10122263491299594559877851 15183395236949391839816777)
      ·
        refine ⟨11387546427712043879862583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183395236949391839816777 11387546427712043879862583)
        ·
          refine ⟨17081319641568065819793875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11387546427712043879862583 17081319641568065819793875)
          ·
            refine ⟨25621979462352098729690813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081319641568065819793875 25621979462352098729690813)
            ·
              refine ⟨9608242298382037023634055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25621979462352098729690813 9608242298382037023634055)
              ·
                refine ⟨14412363447573055535451083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608242298382037023634055 14412363447573055535451083)
                ·
                  refine ⟨21618545171359583303176625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14412363447573055535451083 21618545171359583303176625)
                  ·
                    refine ⟨16213908878519687477382469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21618545171359583303176625 16213908878519687477382469)
                    ·
                      refine ⟨3040107914722441402009213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16213908878519687477382469 3040107914722441402009213)
                      ·
                        rfl

theorem cell23_5920589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5920589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920589 prefixEnd_5920589 := by exact prefixLift 5920589
  have htrace : WordTrace (prefixWord ++ tailWord_5920589) baseStart_5920589 baseEnd_5920589 := by
    simpa [prefixWord, tailWord_5920589, baseEnd_5920589] using wordTrace_append hprefix tailTrace_5920589
  have hstable : (prefixWord ++ tailWord_5920589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920589).length < 2 ^ (prefixWord ++ tailWord_5920589).sum := by decide
  have hdescent : baseEnd_5920589 < baseStart_5920589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920599 : List Nat := [1, 1, 3, 2, 6, 1, 2, 7]
def baseStart_5920599 : Nat := 118140960795 + 5920599 * 2 ^ 59
def prefixEnd_5920599 : Nat := 4983230072969 + 3 ^ 40 * 5920599 * 2
def baseEnd_5920599 : Nat := 112596779612184680106821

theorem tailTrace_5920599 : CollatzResearch.WordTrace tailWord_5920599 prefixEnd_5920599 112596779612184680106821 := by
  unfold tailWord_5920599
  simp only [CollatzResearch.WordTrace]
  refine ⟨215941985877688455651924851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143961323918458970434616567 215941985877688455651924851)
  ·
    refine ⟨323912978816532683477887277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215941985877688455651924851 323912978816532683477887277)
    ·
      refine ⟨121467367056199756304207729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323912978816532683477887277 121467367056199756304207729)
      ·
        refine ⟨91100525292149817228155797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121467367056199756304207729 91100525292149817228155797)
        ·
          refine ⟨4270337123069522682569803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91100525292149817228155797 4270337123069522682569803)
          ·
            refine ⟨6405505684604284023854705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270337123069522682569803 6405505684604284023854705)
            ·
              refine ⟨4804129263453213017891029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405505684604284023854705 4804129263453213017891029)
              ·
                refine ⟨112596779612184680106821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4804129263453213017891029 112596779612184680106821)
                ·
                  rfl

theorem cell23_5920599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 7].length) (baseStart_5920599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920599 prefixEnd_5920599 := by exact prefixLift 5920599
  have htrace : WordTrace (prefixWord ++ tailWord_5920599) baseStart_5920599 baseEnd_5920599 := by
    simpa [prefixWord, tailWord_5920599, baseEnd_5920599] using wordTrace_append hprefix tailTrace_5920599
  have hstable : (prefixWord ++ tailWord_5920599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920599).length < 2 ^ (prefixWord ++ tailWord_5920599).sum := by decide
  have hdescent : baseEnd_5920599 < baseStart_5920599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920610 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_5920610 : Nat := 118140960795 + 5920610 * 2 ^ 59
def prefixEnd_5920610 : Nat := 4983230072969 + 3 ^ 40 * 5920610 * 2
def baseEnd_5920610 : Nat := 3040118697816185819846617

theorem tailTrace_5920610 : CollatzResearch.WordTrace tailWord_5920610 prefixEnd_5920610 3040118697816185819846617 := by
  unfold tailWord_5920610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53985596770162151132643821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143961591387099069687050189 53985596770162151132643821)
  ·
    refine ⟨20244598788810806674741433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53985596770162151132643821 20244598788810806674741433)
    ·
      refine ⟨15183449091608105006056075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20244598788810806674741433 15183449091608105006056075)
      ·
        refine ⟨22775173637412157509084113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15183449091608105006056075 22775173637412157509084113)
        ·
          refine ⟨17081380228059118131813085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22775173637412157509084113 17081380228059118131813085)
          ·
            refine ⟨6405517585522169299429907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17081380228059118131813085 6405517585522169299429907)
            ·
              refine ⟨9608276378283253949144861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405517585522169299429907 9608276378283253949144861)
              ·
                refine ⟨3603103641856220230929323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608276378283253949144861 3603103641856220230929323)
                ·
                  refine ⟨5404655462784330346393985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603103641856220230929323 5404655462784330346393985)
                  ·
                    refine ⟨4053491597088247759795489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404655462784330346393985 4053491597088247759795489)
                    ·
                      refine ⟨3040118697816185819846617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053491597088247759795489 3040118697816185819846617)
                      ·
                        rfl

theorem cell23_5920610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_5920610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920610 prefixEnd_5920610 := by exact prefixLift 5920610
  have htrace : WordTrace (prefixWord ++ tailWord_5920610) baseStart_5920610 baseEnd_5920610 := by
    simpa [prefixWord, tailWord_5920610, baseEnd_5920610] using wordTrace_append hprefix tailTrace_5920610
  have hstable : (prefixWord ++ tailWord_5920610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920610).length < 2 ^ (prefixWord ++ tailWord_5920610).sum := by decide
  have hdescent : baseEnd_5920610 < baseStart_5920610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920635 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3]
def baseStart_5920635 : Nat := 118140960795 + 5920635 * 2 ^ 59
def prefixEnd_5920635 : Nat := 4983230072969 + 3 ^ 40 * 5920635 * 2
def baseEnd_5920635 : Nat := 3040131534832548222034001

theorem tailTrace_5920635 : CollatzResearch.WordTrace tailWord_5920635 prefixEnd_5920635 3040131534832548222034001 := by
  unfold tailWord_5920635
  simp only [CollatzResearch.WordTrace]
  refine ⟨215943298905558033800235359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143962199270372022533490239 215943298905558033800235359)
  ·
    refine ⟨323914948358337050700353039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215943298905558033800235359 323914948358337050700353039)
    ·
      refine ⟨485872422537505576050529559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323914948358337050700353039 485872422537505576050529559)
      ·
        refine ⟨728808633806258364075794339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485872422537505576050529559 728808633806258364075794339)
        ·
          refine ⟨1093212950709387546113691509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728808633806258364075794339 1093212950709387546113691509)
          ·
            refine ⟨102488714129005082448158579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1093212950709387546113691509 102488714129005082448158579)
            ·
              refine ⟨153733071193507623672237869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102488714129005082448158579 153733071193507623672237869)
              ·
                refine ⟨57649901697565358877089201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153733071193507623672237869 57649901697565358877089201)
                ·
                  refine ⟨43237426273174019157816901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57649901697565358877089201 43237426273174019157816901)
                  ·
                    refine ⟨8107017426220128592090669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43237426273174019157816901 8107017426220128592090669)
                    ·
                      refine ⟨3040131534832548222034001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107017426220128592090669 3040131534832548222034001)
                      ·
                        rfl

theorem cell23_5920635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 3].length) (baseStart_5920635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920635 prefixEnd_5920635 := by exact prefixLift 5920635
  have htrace : WordTrace (prefixWord ++ tailWord_5920635) baseStart_5920635 baseEnd_5920635 := by
    simpa [prefixWord, tailWord_5920635, baseEnd_5920635] using wordTrace_append hprefix tailTrace_5920635
  have hstable : (prefixWord ++ tailWord_5920635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920635).length < 2 ^ (prefixWord ++ tailWord_5920635).sum := by decide
  have hdescent : baseEnd_5920635 < baseStart_5920635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920645 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_5920645 : Nat := 118140960795 + 5920645 * 2 ^ 59
def prefixEnd_5920645 : Nat := 4983230072969 + 3 ^ 40 * 5920645 * 2
def baseEnd_5920645 : Nat := 3040136669639093182908955

theorem tailTrace_5920645 : CollatzResearch.WordTrace tailWord_5920645 prefixEnd_5920645 3040136669639093182908955 := by
  unfold tailWord_5920645
  simp only [CollatzResearch.WordTrace]
  refine ⟨215943663635521805508099389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143962442423681203672066259 215943663635521805508099389)
  ·
    refine ⟨80978873863320677065537271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215943663635521805508099389 80978873863320677065537271)
    ·
      refine ⟨121468310794981015598305907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80978873863320677065537271 121468310794981015598305907)
      ·
        refine ⟨182202466192471523397458861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121468310794981015598305907 182202466192471523397458861)
        ·
          refine ⟨68325924822176821274047073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182202466192471523397458861 68325924822176821274047073)
          ·
            refine ⟨51244443616632615955535305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68325924822176821274047073 51244443616632615955535305)
            ·
              refine ⟨38433332712474461966651479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51244443616632615955535305 38433332712474461966651479)
              ·
                refine ⟨57649999068711692949977219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38433332712474461966651479 57649999068711692949977219)
                ·
                  refine ⟨86474998603067539424965829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57649999068711692949977219 86474998603067539424965829)
                  ·
                    refine ⟨16214062238075163642181093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86474998603067539424965829 16214062238075163642181093)
                    ·
                      refine ⟨3040136669639093182908955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16214062238075163642181093 3040136669639093182908955)
                      ·
                        rfl

theorem cell23_5920645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_5920645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920645 prefixEnd_5920645 := by exact prefixLift 5920645
  have htrace : WordTrace (prefixWord ++ tailWord_5920645) baseStart_5920645 baseEnd_5920645 := by
    simpa [prefixWord, tailWord_5920645, baseEnd_5920645] using wordTrace_append hprefix tailTrace_5920645
  have hstable : (prefixWord ++ tailWord_5920645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920645).length < 2 ^ (prefixWord ++ tailWord_5920645).sum := by decide
  have hdescent : baseEnd_5920645 < baseStart_5920645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920672 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 5]
def baseStart_5920672 : Nat := 118140960795 + 5920672 * 2 ^ 59
def prefixEnd_5920672 : Nat := 4983230072969 + 3 ^ 40 * 5920672 * 2
def baseEnd_5920672 : Nat := 337794503735196064141259

theorem tailTrace_5920672 : CollatzResearch.WordTrace tailWord_5920672 prefixEnd_5920672 337794503735196064141259 := by
  unfold tailWord_5920672
  simp only [CollatzResearch.WordTrace]
  refine ⟨107972324203211994559666135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143963098937615992746221513 107972324203211994559666135)
  ·
    refine ⟨161958486304817991839499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107972324203211994559666135 161958486304817991839499203)
    ·
      refine ⟨242937729457226987759248805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161958486304817991839499203 242937729457226987759248805)
      ·
        refine ⟨45550824273230060204859151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242937729457226987759248805 45550824273230060204859151)
        ·
          refine ⟨68326236409845090307288727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45550824273230060204859151 68326236409845090307288727)
          ·
            refine ⟨102489354614767635460933091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68326236409845090307288727 102489354614767635460933091)
            ·
              refine ⟨153734031922151453191399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102489354614767635460933091 153734031922151453191399637)
              ·
                refine ⟨3603141373175424684173429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153734031922151453191399637 3603141373175424684173429)
                ·
                  refine ⟨337794503735196064141259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603141373175424684173429 337794503735196064141259)
                  ·
                    rfl

theorem cell23_5920672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 5].length) (baseStart_5920672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920672 prefixEnd_5920672 := by exact prefixLift 5920672
  have htrace : WordTrace (prefixWord ++ tailWord_5920672) baseStart_5920672 baseEnd_5920672 := by
    simpa [prefixWord, tailWord_5920672, baseEnd_5920672] using wordTrace_append hprefix tailTrace_5920672
  have hstable : (prefixWord ++ tailWord_5920672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920672).length < 2 ^ (prefixWord ++ tailWord_5920672).sum := by decide
  have hdescent : baseEnd_5920672 < baseStart_5920672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920689 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 5]
def baseStart_5920689 : Nat := 118140960795 + 5920689 * 2 ^ 59
def prefixEnd_5920689 : Nat := 4983230072969 + 3 ^ 40 * 5920689 * 2
def baseEnd_5920689 : Nat := 337795473643099001195417

theorem tailTrace_5920689 : CollatzResearch.WordTrace tailWord_5920689 prefixEnd_5920689 337795473643099001195417 := by
  unfold tailWord_5920689
  simp only [CollatzResearch.WordTrace]
  refine ⟨215945268447362401022701121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143963512298241600681800747 215945268447362401022701121)
  ·
    refine ⟨161958951335521800767025841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215945268447362401022701121 161958951335521800767025841)
    ·
      refine ⟨121469213501641350575269381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161958951335521800767025841 121469213501641350575269381)
      ·
        refine ⟨22775477531557753232863009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121469213501641350575269381 22775477531557753232863009)
        ·
          refine ⟨17081608148668314924647257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22775477531557753232863009 17081608148668314924647257)
          ·
            refine ⟨12811206111501236193485443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17081608148668314924647257 12811206111501236193485443)
            ·
              refine ⟨19216809167251854290228165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12811206111501236193485443 19216809167251854290228165)
              ·
                refine ⟨3603151718859722679417781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19216809167251854290228165 3603151718859722679417781)
                ·
                  refine ⟨337795473643099001195417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603151718859722679417781 337795473643099001195417)
                  ·
                    rfl

theorem cell23_5920689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 5].length) (baseStart_5920689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920689 prefixEnd_5920689 := by exact prefixLift 5920689
  have htrace : WordTrace (prefixWord ++ tailWord_5920689) baseStart_5920689 baseEnd_5920689 := by
    simpa [prefixWord, tailWord_5920689, baseEnd_5920689] using wordTrace_append hprefix tailTrace_5920689
  have hstable : (prefixWord ++ tailWord_5920689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920689).length < 2 ^ (prefixWord ++ tailWord_5920689).sum := by decide
  have hdescent : baseEnd_5920689 < baseStart_5920689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920739 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5920739 : Nat := 118140960795 + 5920739 * 2 ^ 59
def prefixEnd_5920739 : Nat := 4983230072969 + 3 ^ 40 * 5920739 * 2
def baseEnd_5920739 : Nat := 3040184936820615815133523

theorem tailTrace_5920739 : CollatzResearch.WordTrace tailWord_5920739 prefixEnd_5920739 3040184936820615815133523 := by
  unfold tailWord_5920739
  simp only [CollatzResearch.WordTrace]
  refine ⟨215947092097181259562021271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143964728064787506374680847 215947092097181259562021271)
  ·
    refine ⟨323920638145771889343031907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215947092097181259562021271 323920638145771889343031907)
    ·
      refine ⟨485880957218657834014547861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323920638145771889343031907 485880957218657834014547861)
      ·
        refine ⟨22775669869624585969431931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 485880957218657834014547861 22775669869624585969431931)
        ·
          refine ⟨34163504804436878954147897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22775669869624585969431931 34163504804436878954147897)
          ·
            refine ⟨25622628603327659215610923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34163504804436878954147897 25622628603327659215610923)
            ·
              refine ⟨38433942904991488823416385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25622628603327659215610923 38433942904991488823416385)
              ·
                refine ⟨28825457178743616617562289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38433942904991488823416385 28825457178743616617562289)
                ·
                  refine ⟨21619092884057712463171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28825457178743616617562289 21619092884057712463171717)
                  ·
                    refine ⟨4053579915760821086844697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21619092884057712463171717 4053579915760821086844697)
                    ·
                      refine ⟨3040184936820615815133523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053579915760821086844697 3040184936820615815133523)
                      ·
                        rfl

theorem cell23_5920739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5920739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920739 prefixEnd_5920739 := by exact prefixLift 5920739
  have htrace : WordTrace (prefixWord ++ tailWord_5920739) baseStart_5920739 baseEnd_5920739 := by
    simpa [prefixWord, tailWord_5920739, baseEnd_5920739] using wordTrace_append hprefix tailTrace_5920739
  have hstable : (prefixWord ++ tailWord_5920739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920739).length < 2 ^ (prefixWord ++ tailWord_5920739).sum := by decide
  have hdescent : baseEnd_5920739 < baseStart_5920739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920766 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_5920766 : Nat := 118140960795 + 5920766 * 2 ^ 59
def prefixEnd_5920766 : Nat := 4983230072969 + 3 ^ 40 * 5920766 * 2
def baseEnd_5920766 : Nat := 1013399600266095736498633

theorem tailTrace_5920766 : CollatzResearch.WordTrace tailWord_5920766 prefixEnd_5920766 1013399600266095736498633 := by
  unfold tailWord_5920766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993509608510430396656769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143965384578722295448836101 26993509608510430396656769)
  ·
    refine ⟨20245132206382822797492577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26993509608510430396656769 20245132206382822797492577)
    ·
      refine ⟨15183849154787117098119433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20245132206382822797492577 15183849154787117098119433)
      ·
        refine ⟨11387886866090337823589575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183849154787117098119433 11387886866090337823589575)
        ·
          refine ⟨17081830299135506735384363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11387886866090337823589575 17081830299135506735384363)
          ·
            refine ⟨25622745448703260103076545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081830299135506735384363 25622745448703260103076545)
            ·
              refine ⟨19217059086527445077307409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25622745448703260103076545 19217059086527445077307409)
              ·
                refine ⟨14412794314895583807980557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19217059086527445077307409 14412794314895583807980557)
                ·
                  refine ⟨5404797868085843927992709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14412794314895583807980557 5404797868085843927992709)
                  ·
                    refine ⟨1013399600266095736498633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404797868085843927992709 1013399600266095736498633)
                    ·
                      rfl

theorem cell23_5920766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_5920766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920766 prefixEnd_5920766 := by exact prefixLift 5920766
  have htrace : WordTrace (prefixWord ++ tailWord_5920766) baseStart_5920766 baseEnd_5920766 := by
    simpa [prefixWord, tailWord_5920766, baseEnd_5920766] using wordTrace_append hprefix tailTrace_5920766
  have hstable : (prefixWord ++ tailWord_5920766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920766).length < 2 ^ (prefixWord ++ tailWord_5920766).sum := by decide
  have hdescent : baseEnd_5920766 < baseStart_5920766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920774 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5920774 : Nat := 118140960795 + 5920774 * 2 ^ 59
def prefixEnd_5920774 : Nat := 4983230072969 + 3 ^ 40 * 5920774 * 2
def baseEnd_5920774 : Nat := 337800323182613686466207

theorem tailTrace_5920774 : CollatzResearch.WordTrace tailWord_5920774 prefixEnd_5920774 337800323182613686466207 := by
  unfold tailWord_5920774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748386520376701891860793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143965579101369640359696917 6748386520376701891860793)
  ·
    refine ⟨5061289890282526418895595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6748386520376701891860793 5061289890282526418895595)
    ·
      refine ⟨7591934835423789628343393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061289890282526418895595 7591934835423789628343393)
      ·
        refine ⟨5693951126567842221257545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7591934835423789628343393 5693951126567842221257545)
        ·
          refine ⟨4270463344925881665943159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693951126567842221257545 4270463344925881665943159)
          ·
            refine ⟨6405695017388822498914739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270463344925881665943159 6405695017388822498914739)
            ·
              refine ⟨9608542526083233748372109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405695017388822498914739 9608542526083233748372109)
              ·
                refine ⟨3603203447281212655639541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608542526083233748372109 3603203447281212655639541)
                ·
                  refine ⟨337800323182613686466207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603203447281212655639541 337800323182613686466207)
                  ·
                    rfl

theorem cell23_5920774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5920774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920774 prefixEnd_5920774 := by exact prefixLift 5920774
  have htrace : WordTrace (prefixWord ++ tailWord_5920774) baseStart_5920774 baseEnd_5920774 := by
    simpa [prefixWord, tailWord_5920774, baseEnd_5920774] using wordTrace_append hprefix tailTrace_5920774
  have hstable : (prefixWord ++ tailWord_5920774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920774).length < 2 ^ (prefixWord ++ tailWord_5920774).sum := by decide
  have hdescent : baseEnd_5920774 < baseStart_5920774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920829 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5920829 : Nat := 118140960795 + 5920829 * 2 ^ 59
def prefixEnd_5920829 : Nat := 4983230072969 + 3 ^ 40 * 5920829 * 2
def baseEnd_5920829 : Nat := 3040231150079520463008109

theorem tailTrace_5920829 : CollatzResearch.WordTrace tailWord_5920829 prefixEnd_5920829 3040231150079520463008109 := by
  unfold tailWord_5920829
  simp only [CollatzResearch.WordTrace]
  refine ⟨215950374666855204932797541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143966916444570136621865027 215950374666855204932797541)
  ·
    refine ⟨40490695250035350924899539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215950374666855204932797541 40490695250035350924899539)
    ·
      refine ⟨60736042875053026387349309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40490695250035350924899539 60736042875053026387349309)
      ·
        refine ⟨22776016078144884895255991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60736042875053026387349309 22776016078144884895255991)
        ·
          refine ⟨34164024117217327342883987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22776016078144884895255991 34164024117217327342883987)
          ·
            refine ⟨51246036175825991014325981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34164024117217327342883987 51246036175825991014325981)
            ·
              refine ⟨19217263565934746630372243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51246036175825991014325981 19217263565934746630372243)
              ·
                refine ⟨28825895348902119945558365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19217263565934746630372243 28825895348902119945558365)
                ·
                  refine ⟨10809710755838294979584387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28825895348902119945558365 10809710755838294979584387)
                  ·
                    refine ⟨16214566133757442469376581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10809710755838294979584387 16214566133757442469376581)
                    ·
                      refine ⟨3040231150079520463008109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16214566133757442469376581 3040231150079520463008109)
                      ·
                        rfl

theorem cell23_5920829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5920829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920829 prefixEnd_5920829 := by exact prefixLift 5920829
  have htrace : WordTrace (prefixWord ++ tailWord_5920829) baseStart_5920829 baseEnd_5920829 := by
    simpa [prefixWord, tailWord_5920829, baseEnd_5920829] using wordTrace_append hprefix tailTrace_5920829
  have hstable : (prefixWord ++ tailWord_5920829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920829).length < 2 ^ (prefixWord ++ tailWord_5920829).sum := by decide
  have hdescent : baseEnd_5920829 < baseStart_5920829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920833 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_5920833 : Nat := 118140960795 + 5920833 * 2 ^ 59
def prefixEnd_5920833 : Nat := 4983230072969 + 3 ^ 40 * 5920833 * 2
def baseEnd_5920833 : Nat := 3040233204002138447358091

theorem tailTrace_5920833 : CollatzResearch.WordTrace tailWord_5920833 prefixEnd_5920833 3040233204002138447358091 := by
  unfold tailWord_5920833
  simp only [CollatzResearch.WordTrace]
  refine ⟨215950520558840713615943153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143967013705893809077295435 215950520558840713615943153)
  ·
    refine ⟨161962890419130535211957365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215950520558840713615943153 161962890419130535211957365)
    ·
      refine ⟨15184020976793487676121003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161962890419130535211957365 15184020976793487676121003)
      ·
        refine ⟨22776031465190231514181505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15184020976793487676121003 22776031465190231514181505)
        ·
          refine ⟨17082023598892673635636129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22776031465190231514181505 17082023598892673635636129)
          ·
            refine ⟨12811517699169505226727097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17082023598892673635636129 12811517699169505226727097)
            ·
              refine ⟨9608638274377128920045323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811517699169505226727097 9608638274377128920045323)
              ·
                refine ⟨14412957411565693380067985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608638274377128920045323 14412957411565693380067985)
                ·
                  refine ⟨10809718058674270035050989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14412957411565693380067985 10809718058674270035050989)
                  ·
                    refine ⟨4053644272002851263144121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10809718058674270035050989 4053644272002851263144121)
                    ·
                      refine ⟨3040233204002138447358091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053644272002851263144121 3040233204002138447358091)
                      ·
                        rfl

theorem cell23_5920833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_5920833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920833 prefixEnd_5920833 := by exact prefixLift 5920833
  have htrace : WordTrace (prefixWord ++ tailWord_5920833) baseStart_5920833 baseEnd_5920833 := by
    simpa [prefixWord, tailWord_5920833, baseEnd_5920833] using wordTrace_append hprefix tailTrace_5920833
  have hstable : (prefixWord ++ tailWord_5920833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920833).length < 2 ^ (prefixWord ++ tailWord_5920833).sum := by decide
  have hdescent : baseEnd_5920833 < baseStart_5920833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920856 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_5920856 : Nat := 118140960795 + 5920856 * 2 ^ 59
def prefixEnd_5920856 : Nat := 4983230072969 + 3 ^ 40 * 5920856 * 2
def baseEnd_5920856 : Nat := 1013415004685730619123495

theorem tailTrace_5920856 : CollatzResearch.WordTrace tailWord_5920856 prefixEnd_5920856 1013415004685730619123495 := by
  unfold tailWord_5920856
  simp only [CollatzResearch.WordTrace]
  refine ⟨107975679718878694272015211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143967572958504925696020281 107975679718878694272015211)
  ·
    refine ⟨161963519578318041408022817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107975679718878694272015211 161963519578318041408022817)
    ·
      refine ⟨121472639683738531056017113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161963519578318041408022817 121472639683738531056017113)
      ·
        refine ⟨91104479762803898292012835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121472639683738531056017113 91104479762803898292012835)
        ·
          refine ⟨136656719644205847438019253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91104479762803898292012835 136656719644205847438019253)
          ·
            refine ⟨12811567466644298197314305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136656719644205847438019253 12811567466644298197314305)
            ·
              refine ⟨9608675599983223647985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811567466644298197314305 9608675599983223647985729)
              ·
                refine ⟨7206506699987417735989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9608675599983223647985729 7206506699987417735989297)
                ·
                  refine ⟨5404880024990563301991973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7206506699987417735989297 5404880024990563301991973)
                  ·
                    refine ⟨1013415004685730619123495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5404880024990563301991973 1013415004685730619123495)
                    ·
                      rfl

theorem cell23_5920856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_5920856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920856 prefixEnd_5920856 := by exact prefixLift 5920856
  have htrace : WordTrace (prefixWord ++ tailWord_5920856) baseStart_5920856 baseEnd_5920856 := by
    simpa [prefixWord, tailWord_5920856, baseEnd_5920856] using wordTrace_append hprefix tailTrace_5920856
  have hstable : (prefixWord ++ tailWord_5920856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920856).length < 2 ^ (prefixWord ++ tailWord_5920856).sum := by decide
  have hdescent : baseEnd_5920856 < baseStart_5920856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920869 : List Nat := [1, 3, 1, 3, 2, 4, 1, 8]
def baseStart_5920869 : Nat := 118140960795 + 5920869 * 2 ^ 59
def prefixEnd_5920869 : Nat := 4983230072969 + 3 ^ 40 * 5920869 * 2
def baseEnd_5920869 : Nat := 112601914418729640981775

theorem tailTrace_5920869 : CollatzResearch.WordTrace tailWord_5920869 prefixEnd_5920869 112601914418729640981775 := by
  unfold tailWord_5920869
  simp only [CollatzResearch.WordTrace]
  refine ⟨215951833586710291764253661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143967889057806861176169107 215951833586710291764253661)
  ·
    refine ⟨80981937595016359411595123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215951833586710291764253661 80981937595016359411595123)
    ·
      refine ⟨121472906392524539117392685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80981937595016359411595123 121472906392524539117392685)
      ·
        refine ⟨45552339897196702169022257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121472906392524539117392685 45552339897196702169022257)
        ·
          refine ⟨34164254922897526626766693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45552339897196702169022257 34164254922897526626766693)
          ·
            refine ⟨6405797798043286242518755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34164254922897526626766693 6405797798043286242518755)
            ·
              refine ⟨9608696697064929363778133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405797798043286242518755 9608696697064929363778133)
              ·
                refine ⟨112601914418729640981775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9608696697064929363778133 112601914418729640981775)
                ·
                  rfl

theorem cell23_5920869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 8].length) (baseStart_5920869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920869 prefixEnd_5920869 := by exact prefixLift 5920869
  have htrace : WordTrace (prefixWord ++ tailWord_5920869) baseStart_5920869 baseEnd_5920869 := by
    simpa [prefixWord, tailWord_5920869, baseEnd_5920869] using wordTrace_append hprefix tailTrace_5920869
  have hstable : (prefixWord ++ tailWord_5920869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920869).length < 2 ^ (prefixWord ++ tailWord_5920869).sum := by decide
  have hdescent : baseEnd_5920869 < baseStart_5920869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920879 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_5920879 : Nat := 118140960795 + 5920879 * 2 ^ 59
def prefixEnd_5920879 : Nat := 4983230072969 + 3 ^ 40 * 5920879 * 2
def baseEnd_5920879 : Nat := 3040256824112245267382879

theorem tailTrace_5920879 : CollatzResearch.WordTrace tailWord_5920879 prefixEnd_5920879 3040256824112245267382879 := by
  unfold tailWord_5920879
  simp only [CollatzResearch.WordTrace]
  refine ⟨215952198316674063472117691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143968132211116042314745127 215952198316674063472117691)
  ·
    refine ⟨323928297475011095208176537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215952198316674063472117691 323928297475011095208176537)
    ·
      refine ⟨242946223106258321406132403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323928297475011095208176537 242946223106258321406132403)
      ·
        refine ⟨364419334659387482109198605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242946223106258321406132403 364419334659387482109198605)
        ·
          refine ⟨136657250497270305790949477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364419334659387482109198605 136657250497270305790949477)
          ·
            refine ⟨25623234468238182335803027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136657250497270305790949477 25623234468238182335803027)
            ·
              refine ⟨38434851702357273503704541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25623234468238182335803027 38434851702357273503704541)
              ·
                refine ⟨14413069388383977563889203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38434851702357273503704541 14413069388383977563889203)
                ·
                  refine ⟨21619604082575966345833805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14413069388383977563889203 21619604082575966345833805)
                  ·
                    refine ⟨8107351530965987379687677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21619604082575966345833805 8107351530965987379687677)
                    ·
                      refine ⟨3040256824112245267382879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107351530965987379687677 3040256824112245267382879)
                      ·
                        rfl

theorem cell23_5920879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_5920879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920879 prefixEnd_5920879 := by exact prefixLift 5920879
  have htrace : WordTrace (prefixWord ++ tailWord_5920879) baseStart_5920879 baseEnd_5920879 := by
    simpa [prefixWord, tailWord_5920879, baseEnd_5920879] using wordTrace_append hprefix tailTrace_5920879
  have hstable : (prefixWord ++ tailWord_5920879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920879).length < 2 ^ (prefixWord ++ tailWord_5920879).sum := by decide
  have hdescent : baseEnd_5920879 < baseStart_5920879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920886 : List Nat := [5, 1, 1, 2, 1, 3, 3, 7]
def baseStart_5920886 : Nat := 118140960795 + 5920886 * 2 ^ 59
def prefixEnd_5920886 : Nat := 4983230072969 + 3 ^ 40 * 5920886 * 2
def baseEnd_5920886 : Nat := 112602237721363953333161

theorem tailTrace_5920886 : CollatzResearch.WordTrace tailWord_5920886 prefixEnd_5920886 112602237721363953333161 := by
  unfold tailWord_5920886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497028351728043979226407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143968302418432469111748341 13497028351728043979226407)
  ·
    refine ⟨20245542527592065968839611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13497028351728043979226407 20245542527592065968839611)
    ·
      refine ⟨30368313791388098953259417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20245542527592065968839611 30368313791388098953259417)
      ·
        refine ⟨22776235343541074214944563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30368313791388098953259417 22776235343541074214944563)
        ·
          refine ⟨34164353015311611322416845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22776235343541074214944563 34164353015311611322416845)
          ·
            refine ⟨12811632380741854245906317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34164353015311611322416845 12811632380741854245906317)
            ·
              refine ⟨4804362142778195342214869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12811632380741854245906317 4804362142778195342214869)
              ·
                refine ⟨112602237721363953333161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4804362142778195342214869 112602237721363953333161)
                ·
                  rfl

theorem cell23_5920886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_5920886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920886 prefixEnd_5920886 := by exact prefixLift 5920886
  have htrace : WordTrace (prefixWord ++ tailWord_5920886) baseStart_5920886 baseEnd_5920886 := by
    simpa [prefixWord, tailWord_5920886, baseEnd_5920886] using wordTrace_append hprefix tailTrace_5920886
  have hstable : (prefixWord ++ tailWord_5920886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920886).length < 2 ^ (prefixWord ++ tailWord_5920886).sum := by decide
  have hdescent : baseEnd_5920886 < baseStart_5920886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920897 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5920897 : Nat := 118140960795 + 5920897 * 2 ^ 59
def prefixEnd_5920897 : Nat := 4983230072969 + 3 ^ 40 * 5920897 * 2
def baseEnd_5920897 : Nat := 3040266066764026196957797

theorem tailTrace_5920897 : CollatzResearch.WordTrace tailWord_5920897 prefixEnd_5920897 3040266066764026196957797 := by
  unfold tailWord_5920897
  simp only [CollatzResearch.WordTrace]
  refine ⟨215952854830608852546272945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143968569887072568364181963 215952854830608852546272945)
  ·
    refine ⟨161964641122956639409704709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215952854830608852546272945 161964641122956639409704709)
    ·
      refine ⟨30368370210554369889319633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161964641122956639409704709 30368370210554369889319633)
      ·
        refine ⟨22776277657915777416989725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30368370210554369889319633 22776277657915777416989725)
        ·
          refine ⟨8541104121718416531371147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22776277657915777416989725 8541104121718416531371147)
          ·
            refine ⟨12811656182577624797056721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541104121718416531371147 12811656182577624797056721)
            ·
              refine ⟨9608742136933218597792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12811656182577624797056721 9608742136933218597792541)
              ·
                refine ⟨3603278301349956974172203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608742136933218597792541 3603278301349956974172203)
                ·
                  refine ⟨5404917452024935461258305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603278301349956974172203 5404917452024935461258305)
                  ·
                    refine ⟨4053688089018701595943729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404917452024935461258305 4053688089018701595943729)
                    ·
                      refine ⟨3040266066764026196957797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053688089018701595943729 3040266066764026196957797)
                      ·
                        rfl

theorem cell23_5920897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5920897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920897 prefixEnd_5920897 := by exact prefixLift 5920897
  have htrace : WordTrace (prefixWord ++ tailWord_5920897) baseStart_5920897 baseEnd_5920897 := by
    simpa [prefixWord, tailWord_5920897, baseEnd_5920897] using wordTrace_append hprefix tailTrace_5920897
  have hstable : (prefixWord ++ tailWord_5920897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920897).length < 2 ^ (prefixWord ++ tailWord_5920897).sum := by decide
  have hdescent : baseEnd_5920897 < baseStart_5920897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920912 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_5920912 : Nat := 118140960795 + 5920912 * 2 ^ 59
def prefixEnd_5920912 : Nat := 4983230072969 + 3 ^ 40 * 5920912 * 2
def baseEnd_5920912 : Nat := 1013424589657947879423409

theorem tailTrace_5920912 : CollatzResearch.WordTrace tailWord_5920912 prefixEnd_5920912 1013424589657947879423409 := by
  unfold tailWord_5920912
  simp only [CollatzResearch.WordTrace]
  refine ⟨107976700962777255054034495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143968934617036340072045993 107976700962777255054034495)
  ·
    refine ⟨161965051444165882581051743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107976700962777255054034495 161965051444165882581051743)
    ·
      refine ⟨242947577166248823871577615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161965051444165882581051743 242947577166248823871577615)
      ·
        refine ⟨364421365749373235807366423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242947577166248823871577615 364421365749373235807366423)
        ·
          refine ⟨546632048624059853711049635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364421365749373235807366423 546632048624059853711049635)
          ·
            refine ⟨819948072936089780566574453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546632048624059853711049635 819948072936089780566574453)
            ·
              refine ⟨76870131837758416928116355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 819948072936089780566574453 76870131837758416928116355)
              ·
                refine ⟨115305197756637625392174533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76870131837758416928116355 115305197756637625392174533)
                ·
                  refine ⟨21619724579369554761032725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115305197756637625392174533 21619724579369554761032725)
                  ·
                    refine ⟨1013424589657947879423409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21619724579369554761032725 1013424589657947879423409)
                    ·
                      rfl

theorem cell23_5920912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_5920912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920912 prefixEnd_5920912 := by exact prefixLift 5920912
  have htrace : WordTrace (prefixWord ++ tailWord_5920912) baseStart_5920912 baseEnd_5920912 := by
    simpa [prefixWord, tailWord_5920912, baseEnd_5920912] using wordTrace_append hprefix tailTrace_5920912
  have hstable : (prefixWord ++ tailWord_5920912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920912).length < 2 ^ (prefixWord ++ tailWord_5920912).sum := by decide
  have hdescent : baseEnd_5920912 < baseStart_5920912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920929 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_5920929 : Nat := 118140960795 + 5920929 * 2 ^ 59
def prefixEnd_5920929 : Nat := 4983230072969 + 3 ^ 40 * 5920929 * 2
def baseEnd_5920929 : Nat := 1013427499381656690585883

theorem tailTrace_5920929 : CollatzResearch.WordTrace tailWord_5920929 prefixEnd_5920929 1013427499381656690585883 := by
  unfold tailWord_5920929
  simp only [CollatzResearch.WordTrace]
  refine ⟨215954021966492922011437841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143969347977661948007625227 215954021966492922011437841)
  ·
    refine ⟨161965516474869691508578381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215954021966492922011437841 161965516474869691508578381)
    ·
      refine ⟨60737068678076134315716893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161965516474869691508578381 60737068678076134315716893)
      ·
        refine ⟨22776400754278550368393835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60737068678076134315716893 22776400754278550368393835)
        ·
          refine ⟨34164601131417825552590753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22776400754278550368393835 34164601131417825552590753)
          ·
            refine ⟨25623450848563369164443065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34164601131417825552590753 25623450848563369164443065)
            ·
              refine ⟨19217588136422526873332299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25623450848563369164443065 19217588136422526873332299)
              ·
                refine ⟨28826382204633790309998449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19217588136422526873332299 28826382204633790309998449)
                ·
                  refine ⟨21619786653475342732498837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28826382204633790309998449 21619786653475342732498837)
                  ·
                    refine ⟨1013427499381656690585883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21619786653475342732498837 1013427499381656690585883)
                    ·
                      rfl

theorem cell23_5920929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_5920929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920929 prefixEnd_5920929 := by exact prefixLift 5920929
  have htrace : WordTrace (prefixWord ++ tailWord_5920929) baseStart_5920929 baseEnd_5920929 := by
    simpa [prefixWord, tailWord_5920929, baseEnd_5920929] using wordTrace_append hprefix tailTrace_5920929
  have hstable : (prefixWord ++ tailWord_5920929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920929).length < 2 ^ (prefixWord ++ tailWord_5920929).sum := by decide
  have hdescent : baseEnd_5920929 < baseStart_5920929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920948 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5920948 : Nat := 118140960795 + 5920948 * 2 ^ 59
def prefixEnd_5920948 : Nat := 4983230072969 + 3 ^ 40 * 5920948 * 2
def baseEnd_5920948 : Nat := 3040292254277405497420063

theorem tailTrace_5920948 : CollatzResearch.WordTrace tailWord_5920948 prefixEnd_5920948 3040292254277405497420063 := by
  unfold tailWord_5920948
  simp only [CollatzResearch.WordTrace]
  refine ⟨107977357476712044128189749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143969809968949392170919665 107977357476712044128189749)
  ·
    refine ⟨10122877263441754137017789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107977357476712044128189749 10122877263441754137017789)
    ·
      refine ⟨3796078973790657801381671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10122877263441754137017789 3796078973790657801381671)
      ·
        refine ⟨5694118460685986702072507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796078973790657801381671 5694118460685986702072507)
        ·
          refine ⟨8541177691028980053108761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694118460685986702072507 8541177691028980053108761)
          ·
            refine ⟨6405883268271735039831571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8541177691028980053108761 6405883268271735039831571)
            ·
              refine ⟨9608824902407602559747357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405883268271735039831571 9608824902407602559747357)
              ·
                refine ⟨3603309338402850959905259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608824902407602559747357 3603309338402850959905259)
                ·
                  refine ⟨5404964007604276439857889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603309338402850959905259 5404964007604276439857889)
                  ·
                    refine ⟨4053723005703207329893417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5404964007604276439857889 4053723005703207329893417)
                    ·
                      refine ⟨3040292254277405497420063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053723005703207329893417 3040292254277405497420063)
                      ·
                        rfl

theorem cell23_5920948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5920948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920948 prefixEnd_5920948 := by exact prefixLift 5920948
  have htrace : WordTrace (prefixWord ++ tailWord_5920948) baseStart_5920948 baseEnd_5920948 := by
    simpa [prefixWord, tailWord_5920948, baseEnd_5920948] using wordTrace_append hprefix tailTrace_5920948
  have hstable : (prefixWord ++ tailWord_5920948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920948).length < 2 ^ (prefixWord ++ tailWord_5920948).sum := by decide
  have hdescent : baseEnd_5920948 < baseStart_5920948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920956 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5920956 : Nat := 118140960795 + 5920956 * 2 ^ 59
def prefixEnd_5920956 : Nat := 4983230072969 + 3 ^ 40 * 5920956 * 2
def baseEnd_5920956 : Nat := 3040296362122641466120025

theorem tailTrace_5920956 : CollatzResearch.WordTrace tailWord_5920956 prefixEnd_5920956 3040296362122641466120025 := by
  unfold tailWord_5920956
  simp only [CollatzResearch.WordTrace]
  refine ⟨107977503368697552811335361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143970004491596737081780481 107977503368697552811335361)
  ·
    refine ⟨80983127526523164608501521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107977503368697552811335361 80983127526523164608501521)
    ·
      refine ⟨60737345644892373456376141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80983127526523164608501521 60737345644892373456376141)
      ·
        refine ⟨22776504616834640046141053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60737345644892373456376141 22776504616834640046141053)
        ·
          refine ⟨8541189231312990017302895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22776504616834640046141053 8541189231312990017302895)
          ·
            refine ⟨12811783846969485025954343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541189231312990017302895 12811783846969485025954343)
            ·
              refine ⟨19217675770454227538931515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12811783846969485025954343 19217675770454227538931515)
              ·
                refine ⟨28826513655681341308397273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19217675770454227538931515 28826513655681341308397273)
                ·
                  refine ⟨21619885241761005981297955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28826513655681341308397273 21619885241761005981297955)
                  ·
                    refine ⟨32429827862641508971946933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21619885241761005981297955 32429827862641508971946933)
                    ·
                      refine ⟨3040296362122641466120025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32429827862641508971946933 3040296362122641466120025)
                      ·
                        rfl

theorem cell23_5920956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5920956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920956 prefixEnd_5920956 := by exact prefixLift 5920956
  have htrace : WordTrace (prefixWord ++ tailWord_5920956) baseStart_5920956 baseEnd_5920956 := by
    simpa [prefixWord, tailWord_5920956, baseEnd_5920956] using wordTrace_append hprefix tailTrace_5920956
  have hstable : (prefixWord ++ tailWord_5920956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920956).length < 2 ^ (prefixWord ++ tailWord_5920956).sum := by decide
  have hdescent : baseEnd_5920956 < baseStart_5920956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5920969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_5920969 : Nat := 118140960795 + 5920969 * 2 ^ 59
def prefixEnd_5920969 : Nat := 4983230072969 + 3 ^ 40 * 5920969 * 2
def baseEnd_5920969 : Nat := 3040303037371149915257465

theorem tailTrace_5920969 : CollatzResearch.WordTrace tailWord_5920969 prefixEnd_5920969 3040303037371149915257465 := by
  unfold tailWord_5920969
  simp only [CollatzResearch.WordTrace]
  refine ⟨215955480886348008842893961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143970320590898672561929307 215955480886348008842893961)
  ·
    refine ⟨161966610664761006632170471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215955480886348008842893961 161966610664761006632170471)
    ·
      refine ⟨242949915997141509948255707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161966610664761006632170471 242949915997141509948255707)
      ·
        refine ⟨364424873995712264922383561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242949915997141509948255707 364424873995712264922383561)
        ·
          refine ⟨273318655496784198691787671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364424873995712264922383561 273318655496784198691787671)
          ·
            refine ⟨409977983245176298037681507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273318655496784198691787671 409977983245176298037681507)
            ·
              refine ⟨614966974867764447056522261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409977983245176298037681507 614966974867764447056522261)
              ·
                refine ⟨28826576946926458455774481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 614966974867764447056522261 28826576946926458455774481)
                ·
                  refine ⟨21619932710194843841830861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28826576946926458455774481 21619932710194843841830861)
                  ·
                    refine ⟨8107474766323066440686573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21619932710194843841830861 8107474766323066440686573)
                    ·
                      refine ⟨3040303037371149915257465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107474766323066440686573 3040303037371149915257465)
                      ·
                        rfl

theorem cell23_5920969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_5920969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5920969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5920969 prefixEnd_5920969 := by exact prefixLift 5920969
  have htrace : WordTrace (prefixWord ++ tailWord_5920969) baseStart_5920969 baseEnd_5920969 := by
    simpa [prefixWord, tailWord_5920969, baseEnd_5920969] using wordTrace_append hprefix tailTrace_5920969
  have hstable : (prefixWord ++ tailWord_5920969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5920969).length < 2 ^ (prefixWord ++ tailWord_5920969).sum := by decide
  have hdescent : baseEnd_5920969 < baseStart_5920969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5920969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921009 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_5921009 : Nat := 118140960795 + 5921009 * 2 ^ 59
def prefixEnd_5921009 : Nat := 4983230072969 + 3 ^ 40 * 5921009 * 2
def baseEnd_5921009 : Nat := 3040323576597329758757281

theorem tailTrace_5921009 : CollatzResearch.WordTrace tailWord_5921009 prefixEnd_5921009 3040323576597329758757281 := by
  unfold tailWord_5921009
  simp only [CollatzResearch.WordTrace]
  refine ⟨215956939806203095674350081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143971293204135397116233387 215956939806203095674350081)
  ·
    refine ⟨161967704854652321755762561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215956939806203095674350081 161967704854652321755762561)
    ·
      refine ⟨121475778640989241316821921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161967704854652321755762561 121475778640989241316821921)
      ·
        refine ⟨91106833980741930987616441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121475778640989241316821921 91106833980741930987616441)
        ·
          refine ⟨68330125485556448240712331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91106833980741930987616441 68330125485556448240712331)
          ·
            refine ⟨102495188228334672361068497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68330125485556448240712331 102495188228334672361068497)
            ·
              refine ⟨76871391171251004270801373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102495188228334672361068497 76871391171251004270801373)
              ·
                refine ⟨28826771689219126601550515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76871391171251004270801373 28826771689219126601550515)
                ·
                  refine ⟨43240157533828689902325773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28826771689219126601550515 43240157533828689902325773)
                  ·
                    refine ⟨16215059075185758713372165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43240157533828689902325773 16215059075185758713372165)
                    ·
                      refine ⟨3040323576597329758757281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16215059075185758713372165 3040323576597329758757281)
                      ·
                        rfl

theorem cell23_5921009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_5921009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921009 prefixEnd_5921009 := by exact prefixLift 5921009
  have htrace : WordTrace (prefixWord ++ tailWord_5921009) baseStart_5921009 baseEnd_5921009 := by
    simpa [prefixWord, tailWord_5921009, baseEnd_5921009] using wordTrace_append hprefix tailTrace_5921009
  have hstable : (prefixWord ++ tailWord_5921009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921009).length < 2 ^ (prefixWord ++ tailWord_5921009).sum := by decide
  have hdescent : baseEnd_5921009 < baseStart_5921009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921036 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_5921036 : Nat := 118140960795 + 5921036 * 2 ^ 59
def prefixEnd_5921036 : Nat := 4983230072969 + 3 ^ 40 * 5921036 * 2
def baseEnd_5921036 : Nat := 1013445813525000384373219

theorem tailTrace_5921036 : CollatzResearch.WordTrace tailWord_5921036 prefixEnd_5921036 1013445813525000384373219 := by
  unfold tailWord_5921036
  simp only [CollatzResearch.WordTrace]
  refine ⟨107978962288552639642791481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143971949718070186190388641 107978962288552639642791481)
  ·
    refine ⟨80984221716414479732093611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107978962288552639642791481 80984221716414479732093611)
    ·
      refine ⟨121476332574621719598140417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80984221716414479732093611 121476332574621719598140417)
      ·
        refine ⟨91107249430966289698605313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121476332574621719598140417 91107249430966289698605313)
        ·
          refine ⟨68330437073224717273953985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91107249430966289698605313 68330437073224717273953985)
          ·
            refine ⟨51247827804918537955465489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68330437073224717273953985 51247827804918537955465489)
            ·
              refine ⟨38435870853688903466599117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51247827804918537955465489 38435870853688903466599117)
              ·
                refine ⟨14413451570133338799974669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38435870853688903466599117 14413451570133338799974669)
                ·
                  refine ⟨5405044338800002049990501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14413451570133338799974669 5405044338800002049990501)
                  ·
                    refine ⟨1013445813525000384373219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5405044338800002049990501 1013445813525000384373219)
                    ·
                      rfl

theorem cell23_5921036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_5921036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921036 prefixEnd_5921036 := by exact prefixLift 5921036
  have htrace : WordTrace (prefixWord ++ tailWord_5921036) baseStart_5921036 baseEnd_5921036 := by
    simpa [prefixWord, tailWord_5921036, baseEnd_5921036] using wordTrace_append hprefix tailTrace_5921036
  have hstable : (prefixWord ++ tailWord_5921036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921036).length < 2 ^ (prefixWord ++ tailWord_5921036).sum := by decide
  have hdescent : baseEnd_5921036 < baseStart_5921036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921086 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5921086 : Nat := 118140960795 + 5921086 * 2 ^ 59
def prefixEnd_5921086 : Nat := 4983230072969 + 3 ^ 40 * 5921086 * 2
def baseEnd_5921086 : Nat := 3040363114607725957494427

theorem tailTrace_5921086 : CollatzResearch.WordTrace tailWord_5921086 prefixEnd_5921086 3040363114607725957494427 := by
  unfold tailWord_5921086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26994968528365517228112889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143973165484616091883268741 26994968528365517228112889)
  ·
    refine ⟨20246226396274137921084667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26994968528365517228112889 20246226396274137921084667)
    ·
      refine ⟨30369339594411206881627001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20246226396274137921084667 30369339594411206881627001)
      ·
        refine ⟨22777004695808405161220251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30369339594411206881627001 22777004695808405161220251)
        ·
          refine ⟨34165507043712607741830377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22777004695808405161220251 34165507043712607741830377)
          ·
            refine ⟨25624130282784455806372783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34165507043712607741830377 25624130282784455806372783)
            ·
              refine ⟨38436195424176683709559175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25624130282784455806372783 38436195424176683709559175)
              ·
                refine ⟨57654293136265025564338763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38436195424176683709559175 57654293136265025564338763)
                ·
                  refine ⟨86481439704397538346508145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57654293136265025564338763 86481439704397538346508145)
                  ·
                    refine ⟨64861079778298153759881109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86481439704397538346508145 64861079778298153759881109)
                    ·
                      refine ⟨3040363114607725957494427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64861079778298153759881109 3040363114607725957494427)
                      ·
                        rfl

theorem cell23_5921086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5921086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921086 prefixEnd_5921086 := by exact prefixLift 5921086
  have htrace : WordTrace (prefixWord ++ tailWord_5921086) baseStart_5921086 baseEnd_5921086 := by
    simpa [prefixWord, tailWord_5921086, baseEnd_5921086] using wordTrace_append hprefix tailTrace_5921086
  have hstable : (prefixWord ++ tailWord_5921086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921086).length < 2 ^ (prefixWord ++ tailWord_5921086).sum := by decide
  have hdescent : baseEnd_5921086 < baseStart_5921086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921099 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_5921099 : Nat := 118140960795 + 5921099 * 2 ^ 59
def prefixEnd_5921099 : Nat := 4983230072969 + 3 ^ 40 * 5921099 * 2
def baseEnd_5921099 : Nat := 3040369789856234406631867

theorem tailTrace_5921099 : CollatzResearch.WordTrace tailWord_5921099 prefixEnd_5921099 3040369789856234406631867 := by
  unfold tailWord_5921099
  simp only [CollatzResearch.WordTrace]
  refine ⟨215960222375877041045126351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143973481583918027363417567 215960222375877041045126351)
  ·
    refine ⟨323940333563815561567689527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215960222375877041045126351 323940333563815561567689527)
    ·
      refine ⟨485910500345723342351534291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323940333563815561567689527 485910500345723342351534291)
      ·
        refine ⟨728865750518585013527301437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485910500345723342351534291 728865750518585013527301437)
        ·
          refine ⟨273324656444469380072738039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728865750518585013527301437 273324656444469380072738039)
          ·
            refine ⟨409986984666704070109107059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273324656444469380072738039 409986984666704070109107059)
            ·
              refine ⟨614980477000056105163660589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409986984666704070109107059 614980477000056105163660589)
              ·
                refine ⟨230617678875021039436372721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 614980477000056105163660589 230617678875021039436372721)
                ·
                  refine ⟨172963259156265779577279541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230617678875021039436372721 172963259156265779577279541)
                  ·
                    refine ⟨16215305545899916835369957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172963259156265779577279541 16215305545899916835369957)
                    ·
                      refine ⟨3040369789856234406631867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16215305545899916835369957 3040369789856234406631867)
                      ·
                        rfl

theorem cell23_5921099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_5921099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921099 prefixEnd_5921099 := by exact prefixLift 5921099
  have htrace : WordTrace (prefixWord ++ tailWord_5921099) baseStart_5921099 baseEnd_5921099 := by
    simpa [prefixWord, tailWord_5921099, baseEnd_5921099] using wordTrace_append hprefix tailTrace_5921099
  have hstable : (prefixWord ++ tailWord_5921099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921099).length < 2 ^ (prefixWord ++ tailWord_5921099).sum := by decide
  have hdescent : baseEnd_5921099 < baseStart_5921099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921127 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_5921127 : Nat := 118140960795 + 5921127 * 2 ^ 59
def prefixEnd_5921127 : Nat := 4983230072969 + 3 ^ 40 * 5921127 * 2
def baseEnd_5921127 : Nat := 3040384167314560297081739

theorem tailTrace_5921127 : CollatzResearch.WordTrace tailWord_5921127 prefixEnd_5921127 3040384167314560297081739 := by
  unfold tailWord_5921127
  simp only [CollatzResearch.WordTrace]
  refine ⟨215961243619775601827145635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143974162413183734551430423 215961243619775601827145635)
  ·
    refine ⟨323941865429663402740718453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215961243619775601827145635 323941865429663402740718453)
    ·
      refine ⟨30369549884030944006942355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323941865429663402740718453 30369549884030944006942355)
      ·
        refine ⟨45554324826046416010413533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30369549884030944006942355 45554324826046416010413533)
        ·
          refine ⟨17082871809767406003905075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45554324826046416010413533 17082871809767406003905075)
          ·
            refine ⟨25624307714651109005857613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17082871809767406003905075 25624307714651109005857613)
            ·
              refine ⟨9609115392994165877196605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25624307714651109005857613 9609115392994165877196605)
              ·
                refine ⟨3603418272372812203948727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9609115392994165877196605 3603418272372812203948727)
                ·
                  refine ⟨5405127408559218305923091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603418272372812203948727 5405127408559218305923091)
                  ·
                    refine ⟨8107691112838827458884637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5405127408559218305923091 8107691112838827458884637)
                    ·
                      refine ⟨3040384167314560297081739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107691112838827458884637 3040384167314560297081739)
                      ·
                        rfl

theorem cell23_5921127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_5921127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921127 prefixEnd_5921127 := by exact prefixLift 5921127
  have htrace : WordTrace (prefixWord ++ tailWord_5921127) baseStart_5921127 baseEnd_5921127 := by
    simpa [prefixWord, tailWord_5921127, baseEnd_5921127] using wordTrace_append hprefix tailTrace_5921127
  have hstable : (prefixWord ++ tailWord_5921127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921127).length < 2 ^ (prefixWord ++ tailWord_5921127).sum := by decide
  have hdescent : baseEnd_5921127 < baseStart_5921127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921133 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_5921133 : Nat := 118140960795 + 5921133 * 2 ^ 59
def prefixEnd_5921133 : Nat := 4983230072969 + 3 ^ 40 * 5921133 * 2
def baseEnd_5921133 : Nat := 3040387248198487273606711

theorem tailTrace_5921133 : CollatzResearch.WordTrace tailWord_5921133 prefixEnd_5921133 3040387248198487273606711 := by
  unfold tailWord_5921133
  simp only [CollatzResearch.WordTrace]
  refine ⟨215961462457753864851864053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143974308305169243234576035 215961462457753864851864053)
  ·
    refine ⟨20246387105414424829862255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215961462457753864851864053 20246387105414424829862255)
    ·
      refine ⟨30369580658121637244793383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20246387105414424829862255 30369580658121637244793383)
      ·
        refine ⟨45554370987182455867190075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30369580658121637244793383 45554370987182455867190075)
        ·
          refine ⟨68331556480773683800785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45554370987182455867190075 68331556480773683800785113)
          ·
            refine ⟨51248667360580262850588835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68331556480773683800785113 51248667360580262850588835)
            ·
              refine ⟨76873001040870394275883253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51248667360580262850588835 76873001040870394275883253)
              ·
                refine ⟨7206843847581599463364055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76873001040870394275883253 7206843847581599463364055)
                ·
                  refine ⟨10810265771372399195046083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7206843847581599463364055 10810265771372399195046083)
                  ·
                    refine ⟨16215398657058598792569125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10810265771372399195046083 16215398657058598792569125)
                    ·
                      refine ⟨3040387248198487273606711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16215398657058598792569125 3040387248198487273606711)
                      ·
                        rfl

theorem cell23_5921133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_5921133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921133 prefixEnd_5921133 := by exact prefixLift 5921133
  have htrace : WordTrace (prefixWord ++ tailWord_5921133) baseStart_5921133 baseEnd_5921133 := by
    simpa [prefixWord, tailWord_5921133, baseEnd_5921133] using wordTrace_append hprefix tailTrace_5921133
  have hstable : (prefixWord ++ tailWord_5921133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921133).length < 2 ^ (prefixWord ++ tailWord_5921133).sum := by decide
  have hdescent : baseEnd_5921133 < baseStart_5921133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921136 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_5921136 : Nat := 118140960795 + 5921136 * 2 ^ 59
def prefixEnd_5921136 : Nat := 4983230072969 + 3 ^ 40 * 5921136 * 2
def baseEnd_5921136 : Nat := 3040388788640450761869197

theorem tailTrace_5921136 : CollatzResearch.WordTrace tailWord_5921136 prefixEnd_5921136 3040388788640450761869197 := by
  unfold tailWord_5921136
  simp only [CollatzResearch.WordTrace]
  refine ⟨107980785938371498182111631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143974381251161997576148841 107980785938371498182111631)
  ·
    refine ⟨161971178907557247273167447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107980785938371498182111631 161971178907557247273167447)
    ·
      refine ⟨242956768361335870909751171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161971178907557247273167447 242956768361335870909751171)
      ·
        refine ⟨364435152542003806364626757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242956768361335870909751171 364435152542003806364626757)
        ·
          refine ⟨68331591101625713693367517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364435152542003806364626757 68331591101625713693367517)
          ·
            refine ⟨25624346663109642635012819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68331591101625713693367517 25624346663109642635012819)
            ·
              refine ⟨38436519994664463952519229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25624346663109642635012819 38436519994664463952519229)
              ·
                refine ⟨14413694997999173982194711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38436519994664463952519229 14413694997999173982194711)
                ·
                  refine ⟨21620542496998760973292067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14413694997999173982194711 21620542496998760973292067)
                  ·
                    refine ⟨32430813745498141459938101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21620542496998760973292067 32430813745498141459938101)
                    ·
                      refine ⟨3040388788640450761869197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32430813745498141459938101 3040388788640450761869197)
                      ·
                        rfl

theorem cell23_5921136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_5921136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921136 prefixEnd_5921136 := by exact prefixLift 5921136
  have htrace : WordTrace (prefixWord ++ tailWord_5921136) baseStart_5921136 baseEnd_5921136 := by
    simpa [prefixWord, tailWord_5921136, baseEnd_5921136] using wordTrace_append hprefix tailTrace_5921136
  have hstable : (prefixWord ++ tailWord_5921136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921136).length < 2 ^ (prefixWord ++ tailWord_5921136).sum := by decide
  have hdescent : baseEnd_5921136 < baseStart_5921136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921153 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5921153 : Nat := 118140960795 + 5921153 * 2 ^ 59
def prefixEnd_5921153 : Nat := 4983230072969 + 3 ^ 40 * 5921153 * 2
def baseEnd_5921153 : Nat := 3040397517811577195356619

theorem tailTrace_5921153 : CollatzResearch.WordTrace tailWord_5921153 prefixEnd_5921153 3040397517811577195356619 := by
  unfold tailWord_5921153
  simp only [CollatzResearch.WordTrace]
  refine ⟨215962191917681408267592113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143974794611787605511728075 215962191917681408267592113)
  ·
    refine ⟨161971643938261056200694085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215962191917681408267592113 161971643938261056200694085)
    ·
      refine ⟨30369683238423948037630141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161971643938261056200694085 30369683238423948037630141)
      ·
        refine ⟨11388631214408980514111303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30369683238423948037630141 11388631214408980514111303)
        ·
          refine ⟨17082946821613470771166955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388631214408980514111303 17082946821613470771166955)
          ·
            refine ⟨25624420232420206156750433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17082946821613470771166955 25624420232420206156750433)
            ·
              refine ⟨19218315174315154617562825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25624420232420206156750433 19218315174315154617562825)
              ·
                refine ⟨14413736380736365963172119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19218315174315154617562825 14413736380736365963172119)
                ·
                  refine ⟨21620604571104548944758179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14413736380736365963172119 21620604571104548944758179)
                  ·
                    refine ⟨32430906856656823417137269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21620604571104548944758179 32430906856656823417137269)
                    ·
                      refine ⟨3040397517811577195356619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32430906856656823417137269 3040397517811577195356619)
                      ·
                        rfl

theorem cell23_5921153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5921153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921153 prefixEnd_5921153 := by exact prefixLift 5921153
  have htrace : WordTrace (prefixWord ++ tailWord_5921153) baseStart_5921153 baseEnd_5921153 := by
    simpa [prefixWord, tailWord_5921153, baseEnd_5921153] using wordTrace_append hprefix tailTrace_5921153
  have hstable : (prefixWord ++ tailWord_5921153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921153).length < 2 ^ (prefixWord ++ tailWord_5921153).sum := by decide
  have hdescent : baseEnd_5921153 < baseStart_5921153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921156 : List Nat := [2, 3, 2, 1, 1, 2, 4, 8]
def baseStart_5921156 : Nat := 118140960795 + 5921156 * 2 ^ 59
def prefixEnd_5921156 : Nat := 4983230072969 + 3 ^ 40 * 5921156 * 2
def baseEnd_5921156 : Nat := 112607372527908914208115

theorem tailTrace_5921156 : CollatzResearch.WordTrace tailWord_5921156 prefixEnd_5921156 112607372527908914208115 := by
  unfold tailWord_5921156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107981150668335269889975661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143974867557780359853300881 107981150668335269889975661)
  ·
    refine ⟨40492931500625726208740873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107981150668335269889975661 40492931500625726208740873)
    ·
      refine ⟨30369698625469294656555655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40492931500625726208740873 30369698625469294656555655)
      ·
        refine ⟨45554547938203941984833483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30369698625469294656555655 45554547938203941984833483)
        ·
          refine ⟨68331821907305912977250225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45554547938203941984833483 68331821907305912977250225)
          ·
            refine ⟨51248866430479434732937669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68331821907305912977250225 51248866430479434732937669)
            ·
              refine ⟨9609162455714894012425813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51248866430479434732937669 9609162455714894012425813)
              ·
                refine ⟨112607372527908914208115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9609162455714894012425813 112607372527908914208115)
                ·
                  rfl

theorem cell23_5921156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 8].length) (baseStart_5921156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921156 prefixEnd_5921156 := by exact prefixLift 5921156
  have htrace : WordTrace (prefixWord ++ tailWord_5921156) baseStart_5921156 baseEnd_5921156 := by
    simpa [prefixWord, tailWord_5921156, baseEnd_5921156] using wordTrace_append hprefix tailTrace_5921156
  have hstable : (prefixWord ++ tailWord_5921156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921156).length < 2 ^ (prefixWord ++ tailWord_5921156).sum := by decide
  have hdescent : baseEnd_5921156 < baseStart_5921156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921183 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_5921183 : Nat := 118140960795 + 5921183 * 2 ^ 59
def prefixEnd_5921183 : Nat := 4983230072969 + 3 ^ 40 * 5921183 * 2
def baseEnd_5921183 : Nat := 3040412922231212077981481

theorem tailTrace_5921183 : CollatzResearch.WordTrace tailWord_5921183 prefixEnd_5921183 3040412922231212077981481 := by
  unfold tailWord_5921183
  simp only [CollatzResearch.WordTrace]
  refine ⟨215963286107572723391184203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143975524071715148927456135 215963286107572723391184203)
  ·
    refine ⟨323944929161359085086776305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215963286107572723391184203 323944929161359085086776305)
    ·
      refine ⟨242958696871019313815082229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323944929161359085086776305 242958696871019313815082229)
      ·
        refine ⟨22777377831658060670163959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242958696871019313815082229 22777377831658060670163959)
        ·
          refine ⟨34166066747487091005245939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22777377831658060670163959 34166066747487091005245939)
          ·
            refine ⟨51249100121230636507868909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34166066747487091005245939 51249100121230636507868909)
            ·
              refine ⟨19218412545461488690450841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51249100121230636507868909 19218412545461488690450841)
              ·
                refine ⟨14413809409096116517838131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19218412545461488690450841 14413809409096116517838131)
                ·
                  refine ⟨21620714113644174776757197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14413809409096116517838131 21620714113644174776757197)
                  ·
                    refine ⟨8107767792616565541283949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21620714113644174776757197 8107767792616565541283949)
                    ·
                      refine ⟨3040412922231212077981481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107767792616565541283949 3040412922231212077981481)
                      ·
                        rfl

theorem cell23_5921183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_5921183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921183 prefixEnd_5921183 := by exact prefixLift 5921183
  have htrace : WordTrace (prefixWord ++ tailWord_5921183) baseStart_5921183 baseEnd_5921183 := by
    simpa [prefixWord, tailWord_5921183, baseEnd_5921183] using wordTrace_append hprefix tailTrace_5921183
  have hstable : (prefixWord ++ tailWord_5921183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921183).length < 2 ^ (prefixWord ++ tailWord_5921183).sum := by decide
  have hdescent : baseEnd_5921183 < baseStart_5921183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921201 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5921201 : Nat := 118140960795 + 5921201 * 2 ^ 59
def prefixEnd_5921201 : Nat := 4983230072969 + 3 ^ 40 * 5921201 * 2
def baseEnd_5921201 : Nat := 3040422164882993007556399

theorem tailTrace_5921201 : CollatzResearch.WordTrace tailWord_5921201 prefixEnd_5921201 3040422164882993007556399 := by
  unfold tailWord_5921201
  simp only [CollatzResearch.WordTrace]
  refine ⟨215963942621507512465339457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143975961747671674976892971 215963942621507512465339457)
  ·
    refine ⟨161972956966130634349004593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215963942621507512465339457 161972956966130634349004593)
    ·
      refine ⟨121479717724597975761753445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161972956966130634349004593 121479717724597975761753445)
      ·
        refine ⟨22777447073362120455328771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121479717724597975761753445 22777447073362120455328771)
        ·
          refine ⟨34166170610043180682993157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22777447073362120455328771 34166170610043180682993157)
          ·
            refine ⟨6406156989383096378061217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34166170610043180682993157 6406156989383096378061217)
            ·
              refine ⟨4804617742037322283545913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406156989383096378061217 4804617742037322283545913)
              ·
                refine ⟨3603463306527991712659435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804617742037322283545913 3603463306527991712659435)
                ·
                  refine ⟨5405194959791987568989153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603463306527991712659435 5405194959791987568989153)
                  ·
                    refine ⟨4053896219843990676741865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405194959791987568989153 4053896219843990676741865)
                    ·
                      refine ⟨3040422164882993007556399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053896219843990676741865 3040422164882993007556399)
                      ·
                        rfl

theorem cell23_5921201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5921201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921201 prefixEnd_5921201 := by exact prefixLift 5921201
  have htrace : WordTrace (prefixWord ++ tailWord_5921201) baseStart_5921201 baseEnd_5921201 := by
    simpa [prefixWord, tailWord_5921201, baseEnd_5921201] using wordTrace_append hprefix tailTrace_5921201
  have hstable : (prefixWord ++ tailWord_5921201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921201).length < 2 ^ (prefixWord ++ tailWord_5921201).sum := by decide
  have hdescent : baseEnd_5921201 < baseStart_5921201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921240 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_5921240 : Nat := 118140960795 + 5921240 * 2 ^ 59
def prefixEnd_5921240 : Nat := 4983230072969 + 3 ^ 40 * 5921240 * 2
def baseEnd_5921240 : Nat := 3040442190628518354968719

theorem tailTrace_5921240 : CollatzResearch.WordTrace tailWord_5921240 prefixEnd_5921240 3040442190628518354968719 := by
  unfold tailWord_5921240
  simp only [CollatzResearch.WordTrace]
  refine ⟨107982682534183111063004587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143976910045577481417339449 107982682534183111063004587)
  ·
    refine ⟨161974023801274666594506881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107982682534183111063004587 161974023801274666594506881)
    ·
      refine ⟨121480517850955999945880161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161974023801274666594506881 121480517850955999945880161)
      ·
        refine ⟨91110388388216999959410121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121480517850955999945880161 91110388388216999959410121)
        ·
          refine ⟨68332791291162749969557591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91110388388216999959410121 68332791291162749969557591)
          ·
            refine ⟨102499186936744124954336387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68332791291162749969557591 102499186936744124954336387)
            ·
              refine ⟨153748780405116187431504581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102499186936744124954336387 153748780405116187431504581)
              ·
                refine ⟨28827896325959285143407109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153748780405116187431504581 28827896325959285143407109)
                ·
                  refine ⟨5405230561117365964388833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28827896325959285143407109 5405230561117365964388833)
                  ·
                    refine ⟨4053922920838024473291625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405230561117365964388833 4053922920838024473291625)
                    ·
                      refine ⟨3040442190628518354968719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053922920838024473291625 3040442190628518354968719)
                      ·
                        rfl

theorem cell23_5921240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_5921240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921240 prefixEnd_5921240 := by exact prefixLift 5921240
  have htrace : WordTrace (prefixWord ++ tailWord_5921240) baseStart_5921240 baseEnd_5921240 := by
    simpa [prefixWord, tailWord_5921240, baseEnd_5921240] using wordTrace_append hprefix tailTrace_5921240
  have hstable : (prefixWord ++ tailWord_5921240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921240).length < 2 ^ (prefixWord ++ tailWord_5921240).sum := by decide
  have hdescent : baseEnd_5921240 < baseStart_5921240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921273 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_5921273 : Nat := 118140960795 + 5921273 * 2 ^ 59
def prefixEnd_5921273 : Nat := 4983230072969 + 3 ^ 40 * 5921273 * 2
def baseEnd_5921273 : Nat := 3040459135490116725856067

theorem tailTrace_5921273 : CollatzResearch.WordTrace tailWord_5921273 prefixEnd_5921273 3040459135490116725856067 := by
  unfold tailWord_5921273
  simp only [CollatzResearch.WordTrace]
  refine ⟨215966568677246668761960473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143977712451497779174640315 215966568677246668761960473)
  ·
    refine ⟨161974926507935001571470355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215966568677246668761960473 161974926507935001571470355)
    ·
      refine ⟨242962389761902502357205533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161974926507935001571470355 242962389761902502357205533)
      ·
        refine ⟨91110896160713438383952075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242962389761902502357205533 91110896160713438383952075)
        ·
          refine ⟨136666344241070157575928113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91110896160713438383952075 136666344241070157575928113)
          ·
            refine ⟨102499758180802618181946085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136666344241070157575928113 102499758180802618181946085)
            ·
              refine ⟨19218704658900490909114891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102499758180802618181946085 19218704658900490909114891)
              ·
                refine ⟨28828056988350736363672337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19218704658900490909114891 28828056988350736363672337)
                ·
                  refine ⟨21621042741263052272754253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28828056988350736363672337 21621042741263052272754253)
                  ·
                    refine ⟨8107891027973644602282845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21621042741263052272754253 8107891027973644602282845)
                    ·
                      refine ⟨3040459135490116725856067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8107891027973644602282845 3040459135490116725856067)
                      ·
                        rfl

theorem cell23_5921273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_5921273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921273 prefixEnd_5921273 := by exact prefixLift 5921273
  have htrace : WordTrace (prefixWord ++ tailWord_5921273) baseStart_5921273 baseEnd_5921273 := by
    simpa [prefixWord, tailWord_5921273, baseEnd_5921273] using wordTrace_append hprefix tailTrace_5921273
  have hstable : (prefixWord ++ tailWord_5921273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921273).length < 2 ^ (prefixWord ++ tailWord_5921273).sum := by decide
  have hdescent : baseEnd_5921273 < baseStart_5921273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921320 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5921320 : Nat := 118140960795 + 5921320 * 2 ^ 59
def prefixEnd_5921320 : Nat := 4983230072969 + 3 ^ 40 * 5921320 * 2
def baseEnd_5921320 : Nat := 3040483269080878041968351

theorem tailTrace_5921320 : CollatzResearch.WordTrace tailWord_5921320 prefixEnd_5921320 3040483269080878041968351 := by
  unfold tailWord_5921320
  simp only [CollatzResearch.WordTrace]
  refine ⟨107984141454038197894460707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143978855272050930525947609 107984141454038197894460707)
  ·
    refine ⟨161976212181057296841691061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107984141454038197894460707 161976212181057296841691061)
    ·
      refine ⟨15185269891974121578908537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161976212181057296841691061 15185269891974121578908537)
      ·
        refine ⟨11388952418980591184181403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15185269891974121578908537 11388952418980591184181403)
        ·
          refine ⟨17083428628470886776272105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388952418980591184181403 17083428628470886776272105)
          ·
            refine ⟨12812571471353165082204079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17083428628470886776272105 12812571471353165082204079)
            ·
              refine ⟨19218857207029747623306119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812571471353165082204079 19218857207029747623306119)
              ·
                refine ⟨28828285810544621434959179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19218857207029747623306119 28828285810544621434959179)
                ·
                  refine ⟨43242428715816932152438769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28828285810544621434959179 43242428715816932152438769)
                  ·
                    refine ⟨32431821536862699114329077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43242428715816932152438769 32431821536862699114329077)
                    ·
                      refine ⟨3040483269080878041968351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32431821536862699114329077 3040483269080878041968351)
                      ·
                        rfl

theorem cell23_5921320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5921320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921320 prefixEnd_5921320 := by exact prefixLift 5921320
  have htrace : WordTrace (prefixWord ++ tailWord_5921320) baseStart_5921320 baseEnd_5921320 := by
    simpa [prefixWord, tailWord_5921320, baseEnd_5921320] using wordTrace_append hprefix tailTrace_5921320
  have hstable : (prefixWord ++ tailWord_5921320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921320).length < 2 ^ (prefixWord ++ tailWord_5921320).sum := by decide
  have hdescent : baseEnd_5921320 < baseStart_5921320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921330 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_5921330 : Nat := 118140960795 + 5921330 * 2 ^ 59
def prefixEnd_5921330 : Nat := 4983230072969 + 3 ^ 40 * 5921330 * 2
def baseEnd_5921330 : Nat := 3040488403887423002843305

theorem tailTrace_5921330 : CollatzResearch.WordTrace tailWord_5921330 prefixEnd_5921330 3040488403887423002843305 := by
  unfold tailWord_5921330
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992161909510041874196361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143979098425360111664523629 53992161909510041874196361)
  ·
    refine ⟨40494121432132531405647271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53992161909510041874196361 40494121432132531405647271)
    ·
      refine ⟨60741182148198797108470907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40494121432132531405647271 60741182148198797108470907)
      ·
        refine ⟨91111773222298195662706361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60741182148198797108470907 91111773222298195662706361)
        ·
          refine ⟨68333829916723646747029771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91111773222298195662706361 68333829916723646747029771)
          ·
            refine ⟨102500744875085470120544657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68333829916723646747029771 102500744875085470120544657)
            ·
              refine ⟨76875558656314102590408493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102500744875085470120544657 76875558656314102590408493)
              ·
                refine ⟨28828334496117788471403185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76875558656314102590408493 28828334496117788471403185)
                ·
                  refine ⟨21621250872088341353552389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28828334496117788471403185 21621250872088341353552389)
                  ·
                    refine ⟨4053984538516564003791073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21621250872088341353552389 4053984538516564003791073)
                    ·
                      refine ⟨3040488403887423002843305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4053984538516564003791073 3040488403887423002843305)
                      ·
                        rfl

theorem cell23_5921330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_5921330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921330 prefixEnd_5921330 := by exact prefixLift 5921330
  have htrace : WordTrace (prefixWord ++ tailWord_5921330) baseStart_5921330 baseEnd_5921330 := by
    simpa [prefixWord, tailWord_5921330, baseEnd_5921330] using wordTrace_append hprefix tailTrace_5921330
  have hstable : (prefixWord ++ tailWord_5921330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921330).length < 2 ^ (prefixWord ++ tailWord_5921330).sum := by decide
  have hdescent : baseEnd_5921330 < baseStart_5921330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921433 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_5921433 : Nat := 118140960795 + 5921433 * 2 ^ 59
def prefixEnd_5921433 : Nat := 4983230072969 + 3 ^ 40 * 5921433 * 2
def baseEnd_5921433 : Nat := 3040541292394836099855331

theorem tailTrace_5921433 : CollatzResearch.WordTrace tailWord_5921433 prefixEnd_5921433 3040541292394836099855331 := by
  unfold tailWord_5921433
  simp only [CollatzResearch.WordTrace]
  refine ⟨215972404356667016087784953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143981602904444677391856635 215972404356667016087784953)
  ·
    refine ⟨161979303267500262065838715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215972404356667016087784953 161979303267500262065838715)
    ·
      refine ⟨242968954901250393098758073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161979303267500262065838715 242968954901250393098758073)
      ·
        refine ⟨182226716175937794824068555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242968954901250393098758073 182226716175937794824068555)
        ·
          refine ⟨273340074263906692236102833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182226716175937794824068555 273340074263906692236102833)
          ·
            refine ⟨205005055697930019177077125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273340074263906692236102833 205005055697930019177077125)
            ·
              refine ⟨38438447943361878595701961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205005055697930019177077125 38438447943361878595701961)
              ·
                refine ⟨28828835957521408946776471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38438447943361878595701961 28828835957521408946776471)
                ·
                  refine ⟨43243253936282113420164707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28828835957521408946776471 43243253936282113420164707)
                  ·
                    refine ⟨64864880904423170130247061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43243253936282113420164707 64864880904423170130247061)
                    ·
                      refine ⟨3040541292394836099855331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64864880904423170130247061 3040541292394836099855331)
                      ·
                        rfl

theorem cell23_5921433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_5921433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921433 prefixEnd_5921433 := by exact prefixLift 5921433
  have htrace : WordTrace (prefixWord ++ tailWord_5921433) baseStart_5921433 baseEnd_5921433 := by
    simpa [prefixWord, tailWord_5921433, baseEnd_5921433] using wordTrace_append hprefix tailTrace_5921433
  have hstable : (prefixWord ++ tailWord_5921433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921433).length < 2 ^ (prefixWord ++ tailWord_5921433).sum := by decide
  have hdescent : baseEnd_5921433 < baseStart_5921433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921454 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5921454 : Nat := 118140960795 + 5921454 * 2 ^ 59
def prefixEnd_5921454 : Nat := 4983230072969 + 3 ^ 40 * 5921454 * 2
def baseEnd_5921454 : Nat := 3040552075488580517692735

theorem tailTrace_5921454 : CollatzResearch.WordTrace tailWord_5921454 prefixEnd_5921454 3040552075488580517692735 := by
  unfold tailWord_5921454
  simp only [CollatzResearch.WordTrace]
  refine ⟨26996646286198867084287427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143982113526393957782866277 26996646286198867084287427)
  ·
    refine ⟨40494969429298300626431141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26996646286198867084287427 40494969429298300626431141)
    ·
      refine ⟨7592806767993431367455839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40494969429298300626431141 7592806767993431367455839)
      ·
        refine ⟨11389210151990147051183759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7592806767993431367455839 11389210151990147051183759)
        ·
          refine ⟨17083815227985220576775639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11389210151990147051183759 17083815227985220576775639)
          ·
            refine ⟨25625722841977830865163459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17083815227985220576775639 25625722841977830865163459)
            ·
              refine ⟨38438584262966746297745189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25625722841977830865163459 38438584262966746297745189)
              ·
                refine ⟨7207234549306264930827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38438584262966746297745189 7207234549306264930827223)
                ·
                  refine ⟨10810851823959397396240835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207234549306264930827223 10810851823959397396240835)
                  ·
                    refine ⟨16216277735939096094361253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10810851823959397396240835 16216277735939096094361253)
                    ·
                      refine ⟨3040552075488580517692735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16216277735939096094361253 3040552075488580517692735)
                      ·
                        rfl

theorem cell23_5921454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5921454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921454 prefixEnd_5921454 := by exact prefixLift 5921454
  have htrace : WordTrace (prefixWord ++ tailWord_5921454) baseStart_5921454 baseEnd_5921454 := by
    simpa [prefixWord, tailWord_5921454, baseEnd_5921454] using wordTrace_append hprefix tailTrace_5921454
  have hstable : (prefixWord ++ tailWord_5921454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921454).length < 2 ^ (prefixWord ++ tailWord_5921454).sum := by decide
  have hdescent : baseEnd_5921454 < baseStart_5921454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921471 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 1, 2, 2]
def baseStart_5921471 : Nat := 118140960795 + 5921471 * 2 ^ 59
def prefixEnd_5921471 : Nat := 4983230072969 + 3 ^ 40 * 5921471 * 2
def baseEnd_5921471 : Nat := 3040560804659706951180157

theorem tailTrace_5921471 : CollatzResearch.WordTrace tailWord_5921471 prefixEnd_5921471 3040560804659706951180157 := by
  unfold tailWord_5921471
  simp only [CollatzResearch.WordTrace]
  refine ⟨215973790330529348577668267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143982526887019565718445511 215973790330529348577668267)
  ·
    refine ⟨323960685495794022866502401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215973790330529348577668267 323960685495794022866502401)
    ·
      refine ⟨242970514121845517149876801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323960685495794022866502401 242970514121845517149876801)
      ·
        refine ⟨182227885591384137862407601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242970514121845517149876801 182227885591384137862407601)
        ·
          refine ⟨136670914193538103396805701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182227885591384137862407601 136670914193538103396805701)
          ·
            refine ⟨25625796411288394386901069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136670914193538103396805701 25625796411288394386901069)
            ·
              refine ⟨9609673654233147895087901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25625796411288394386901069 9609673654233147895087901)
              ·
                refine ⟨3603627620337430460657963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9609673654233147895087901 3603627620337430460657963)
                ·
                  refine ⟨5405441430506145690986945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603627620337430460657963 5405441430506145690986945)
                  ·
                    refine ⟨4054081072879609268240209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405441430506145690986945 4054081072879609268240209)
                    ·
                      refine ⟨3040560804659706951180157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054081072879609268240209 3040560804659706951180157)
                      ·
                        rfl

theorem cell23_5921471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_5921471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921471 prefixEnd_5921471 := by exact prefixLift 5921471
  have htrace : WordTrace (prefixWord ++ tailWord_5921471) baseStart_5921471 baseEnd_5921471 := by
    simpa [prefixWord, tailWord_5921471, baseEnd_5921471] using wordTrace_append hprefix tailTrace_5921471
  have hstable : (prefixWord ++ tailWord_5921471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921471).length < 2 ^ (prefixWord ++ tailWord_5921471).sum := by decide
  have hdescent : baseEnd_5921471 < baseStart_5921471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921497 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 3, 3, 2]
def baseStart_5921497 : Nat := 118140960795 + 5921497 * 2 ^ 59
def prefixEnd_5921497 : Nat := 4983230072969 + 3 ^ 40 * 5921497 * 2
def baseEnd_5921497 : Nat := 3040574155156723849455037

theorem tailTrace_5921497 : CollatzResearch.WordTrace tailWord_5921497 prefixEnd_5921497 3040574155156723849455037 := by
  unfold tailWord_5921497
  simp only [CollatzResearch.WordTrace]
  refine ⟨215974738628435155018114745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143983159085623436678743163 215974738628435155018114745)
  ·
    refine ⟨161981053971326366263586059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215974738628435155018114745 161981053971326366263586059)
    ·
      refine ⟨242971580956989549395379089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161981053971326366263586059 242971580956989549395379089)
      ·
        refine ⟨182228685717742162046534317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242971580956989549395379089 182228685717742162046534317)
        ·
          refine ⟨68335757144153310767450369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182228685717742162046534317 68335757144153310767450369)
          ·
            refine ⟨51251817858114983075587777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68335757144153310767450369 51251817858114983075587777)
            ·
              refine ⟨38438863393586237306690833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51251817858114983075587777 38438863393586237306690833)
              ·
                refine ⟨28829147545189677980018125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38438863393586237306690833 28829147545189677980018125)
                ·
                  refine ⟨10810930329446129242506797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28829147545189677980018125 10810930329446129242506797)
                  ·
                    refine ⟨4054098873542298465940049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10810930329446129242506797 4054098873542298465940049)
                    ·
                      refine ⟨3040574155156723849455037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4054098873542298465940049 3040574155156723849455037)
                      ·
                        rfl

theorem cell23_5921497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_5921497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921497 prefixEnd_5921497 := by exact prefixLift 5921497
  have htrace : WordTrace (prefixWord ++ tailWord_5921497) baseStart_5921497 baseEnd_5921497 := by
    simpa [prefixWord, tailWord_5921497, baseEnd_5921497] using wordTrace_append hprefix tailTrace_5921497
  have hstable : (prefixWord ++ tailWord_5921497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921497).length < 2 ^ (prefixWord ++ tailWord_5921497).sum := by decide
  have hdescent : baseEnd_5921497 < baseStart_5921497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921525 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5921525 : Nat := 118140960795 + 5921525 * 2 ^ 59
def prefixEnd_5921525 : Nat := 4983230072969 + 3 ^ 40 * 5921525 * 2
def baseEnd_5921525 : Nat := 3040588532615049739904909

theorem tailTrace_5921525 : CollatzResearch.WordTrace tailWord_5921525 prefixEnd_5921525 3040588532615049739904909 := by
  unfold tailWord_5921525
  simp only [CollatzResearch.WordTrace]
  refine ⟨215975759872333715800134029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143983839914889143866756019 215975759872333715800134029)
  ·
    refine ⟨80990909952125143425050261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215975759872333715800134029 80990909952125143425050261)
    ·
      refine ⟨3796448904005866098049231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80990909952125143425050261 3796448904005866098049231)
      ·
        refine ⟨5694673356008799147073847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796448904005866098049231 5694673356008799147073847)
        ·
          refine ⟨8542010034013198720610771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694673356008799147073847 8542010034013198720610771)
          ·
            refine ⟨12813015051019798080916157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542010034013198720610771 12813015051019798080916157)
            ·
              refine ⟨4804880644132424280343559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12813015051019798080916157 4804880644132424280343559)
              ·
                refine ⟨7207320966198636420515339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804880644132424280343559 7207320966198636420515339)
                ·
                  refine ⟨10810981449297954630773009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207320966198636420515339 10810981449297954630773009)
                  ·
                    refine ⟨8108236086973465973079757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10810981449297954630773009 8108236086973465973079757)
                    ·
                      refine ⟨3040588532615049739904909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8108236086973465973079757 3040588532615049739904909)
                      ·
                        rfl

theorem cell23_5921525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5921525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921525 prefixEnd_5921525 := by exact prefixLift 5921525
  have htrace : WordTrace (prefixWord ++ tailWord_5921525) baseStart_5921525 baseEnd_5921525 := by
    simpa [prefixWord, tailWord_5921525, baseEnd_5921525] using wordTrace_append hprefix tailTrace_5921525
  have hstable : (prefixWord ++ tailWord_5921525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921525).length < 2 ^ (prefixWord ++ tailWord_5921525).sum := by decide
  have hdescent : baseEnd_5921525 < baseStart_5921525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921530 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_5921530 : Nat := 118140960795 + 5921530 * 2 ^ 59
def prefixEnd_5921530 : Nat := 4983230072969 + 3 ^ 40 * 5921530 * 2
def baseEnd_5921530 : Nat := 3040591100018322220342385

theorem tailTrace_5921530 : CollatzResearch.WordTrace tailWord_5921530 prefixEnd_5921530 3040591100018322220342385 := by
  unfold tailWord_5921530
  simp only [CollatzResearch.WordTrace]
  refine ⟨53993985559328900413516511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143983961491543734436044029 53993985559328900413516511)
  ·
    refine ⟨80990978338993350620274767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53993985559328900413516511 80990978338993350620274767)
    ·
      refine ⟨121486467508490025930412151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80990978338993350620274767 121486467508490025930412151)
      ·
        refine ⟨182229701262735038895618227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121486467508490025930412151 182229701262735038895618227)
        ·
          refine ⟨273344551894102558343427341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182229701262735038895618227 273344551894102558343427341)
          ·
            refine ⟨102504206960288459378785253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273344551894102558343427341 102504206960288459378785253)
            ·
              refine ⟨19219538805054086133522235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102504206960288459378785253 19219538805054086133522235)
              ·
                refine ⟨28829308207581129200283353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19219538805054086133522235 28829308207581129200283353)
                ·
                  refine ⟨21621981155685846900212515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28829308207581129200283353 21621981155685846900212515)
                  ·
                    refine ⟨32432971733528770350318773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21621981155685846900212515 32432971733528770350318773)
                    ·
                      refine ⟨3040591100018322220342385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32432971733528770350318773 3040591100018322220342385)
                      ·
                        rfl

theorem cell23_5921530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_5921530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921530 prefixEnd_5921530 := by exact prefixLift 5921530
  have htrace : WordTrace (prefixWord ++ tailWord_5921530) baseStart_5921530 baseEnd_5921530 := by
    simpa [prefixWord, tailWord_5921530, baseEnd_5921530] using wordTrace_append hprefix tailTrace_5921530
  have hstable : (prefixWord ++ tailWord_5921530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921530).length < 2 ^ (prefixWord ++ tailWord_5921530).sum := by decide
  have hdescent : baseEnd_5921530 < baseStart_5921530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921550 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_5921550 : Nat := 118140960795 + 5921550 * 2 ^ 59
def prefixEnd_5921550 : Nat := 4983230072969 + 3 ^ 40 * 5921550 * 2
def baseEnd_5921550 : Nat := 337844596625712460232477

theorem tailTrace_5921550 : CollatzResearch.WordTrace tailWord_5921550 prefixEnd_5921550 337844596625712460232477 := by
  unfold tailWord_5921550
  simp only [CollatzResearch.WordTrace]
  refine ⟨26997083962155393133724263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143984447798162096713196069 26997083962155393133724263)
  ·
    refine ⟨40495625943233089700586395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26997083962155393133724263 40495625943233089700586395)
    ·
      refine ⟨60743438914849634550879593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40495625943233089700586395 60743438914849634550879593)
      ·
        refine ⟨45557579186137225913159695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60743438914849634550879593 45557579186137225913159695)
        ·
          refine ⟨68336368779205838869739543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45557579186137225913159695 68336368779205838869739543)
          ·
            refine ⟨102504553168808758304609315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68336368779205838869739543 102504553168808758304609315)
            ·
              refine ⟨153756829753213137456913973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102504553168808758304609315 153756829753213137456913973)
              ·
                refine ⟨14414702789363731636585685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153756829753213137456913973 14414702789363731636585685)
                ·
                  refine ⟨337844596625712460232477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14414702789363731636585685 337844596625712460232477)
                  ·
                    rfl

theorem cell23_5921550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_5921550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921550 prefixEnd_5921550 := by exact prefixLift 5921550
  have htrace : WordTrace (prefixWord ++ tailWord_5921550) baseStart_5921550 baseEnd_5921550 := by
    simpa [prefixWord, tailWord_5921550, baseEnd_5921550] using wordTrace_append hprefix tailTrace_5921550
  have hstable : (prefixWord ++ tailWord_5921550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921550).length < 2 ^ (prefixWord ++ tailWord_5921550).sum := by decide
  have hdescent : baseEnd_5921550 < baseStart_5921550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921554 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5921554 : Nat := 118140960795 + 5921554 * 2 ^ 59
def prefixEnd_5921554 : Nat := 4983230072969 + 3 ^ 40 * 5921554 * 2
def baseEnd_5921554 : Nat := 1013534474518010042147425

theorem tailTrace_5921554 : CollatzResearch.WordTrace tailWord_5921554 prefixEnd_5921554 1013534474518010042147425 := by
  unfold tailWord_5921554
  simp only [CollatzResearch.WordTrace]
  refine ⟨53994204397307163438234929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143984545059485769168626477 53994204397307163438234929)
  ·
    refine ⟨40495653297980372578676197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53994204397307163438234929 40495653297980372578676197)
    ·
      refine ⟨7592934993371319858501787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40495653297980372578676197 7592934993371319858501787)
      ·
        refine ⟨11389402490056979787752681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7592934993371319858501787 11389402490056979787752681)
        ·
          refine ⟨8542051867542734840814511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11389402490056979787752681 8542051867542734840814511)
          ·
            refine ⟨12813077801314102261221767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542051867542734840814511 12813077801314102261221767)
            ·
              refine ⟨19219616701971153391832651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12813077801314102261221767 19219616701971153391832651)
              ·
                refine ⟨28829425052956730087748977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19219616701971153391832651 28829425052956730087748977)
                ·
                  refine ⟨21622068789717547565811733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28829425052956730087748977 21622068789717547565811733)
                  ·
                    refine ⟨1013534474518010042147425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21622068789717547565811733 1013534474518010042147425)
                    ·
                      rfl

theorem cell23_5921554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5921554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921554 prefixEnd_5921554 := by exact prefixLift 5921554
  have htrace : WordTrace (prefixWord ++ tailWord_5921554) baseStart_5921554 baseEnd_5921554 := by
    simpa [prefixWord, tailWord_5921554, baseEnd_5921554] using wordTrace_append hprefix tailTrace_5921554
  have hstable : (prefixWord ++ tailWord_5921554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921554).length < 2 ^ (prefixWord ++ tailWord_5921554).sum := by decide
  have hdescent : baseEnd_5921554 < baseStart_5921554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921580 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_5921580 : Nat := 118140960795 + 5921580 * 2 ^ 59
def prefixEnd_5921580 : Nat := 4983230072969 + 3 ^ 40 * 5921580 * 2
def baseEnd_5921580 : Nat := 1013538924683682341572385

theorem tailTrace_5921580 : CollatzResearch.WordTrace tailWord_5921580 prefixEnd_5921580 1013538924683682341572385 := by
  unfold tailWord_5921580
  simp only [CollatzResearch.WordTrace]
  refine ⟨107988882943567230096693097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143985177258089640128924129 107988882943567230096693097)
  ·
    refine ⟨80991662207675422572519823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107988882943567230096693097 80991662207675422572519823)
    ·
      refine ⟨121487493311513133858779735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80991662207675422572519823 121487493311513133858779735)
      ·
        refine ⟨182231239967269700788169603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121487493311513133858779735 182231239967269700788169603)
        ·
          refine ⟨273346859950904551182254405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182231239967269700788169603 273346859950904551182254405)
          ·
            refine ⟨51252536240794603346672701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273346859950904551182254405 51252536240794603346672701)
            ·
              refine ⟨19219701090297976255002263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51252536240794603346672701 19219701090297976255002263)
              ·
                refine ⟨28829551635446964382503395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19219701090297976255002263 28829551635446964382503395)
                ·
                  refine ⟨43244327453170446573755093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28829551635446964382503395 43244327453170446573755093)
                  ·
                    refine ⟨1013538924683682341572385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43244327453170446573755093 1013538924683682341572385)
                    ·
                      rfl

theorem cell23_5921580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_5921580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921580 prefixEnd_5921580 := by exact prefixLift 5921580
  have htrace : WordTrace (prefixWord ++ tailWord_5921580) baseStart_5921580 baseEnd_5921580 := by
    simpa [prefixWord, tailWord_5921580, baseEnd_5921580] using wordTrace_append hprefix tailTrace_5921580
  have hstable : (prefixWord ++ tailWord_5921580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921580).length < 2 ^ (prefixWord ++ tailWord_5921580).sum := by decide
  have hdescent : baseEnd_5921580 < baseStart_5921580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921637 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_5921637 : Nat := 118140960795 + 5921637 * 2 ^ 59
def prefixEnd_5921637 : Nat := 4983230072969 + 3 ^ 40 * 5921637 * 2
def baseEnd_5921637 : Nat := 3040646042448353301704393

theorem tailTrace_5921637 : CollatzResearch.WordTrace tailWord_5921637 prefixEnd_5921637 3040646042448353301704393 := by
  unfold tailWord_5921637
  simp only [CollatzResearch.WordTrace]
  refine ⟨215979844847927958928211165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143986563231951972618807443 215979844847927958928211165)
  ·
    refine ⟨80992441817972984598079187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215979844847927958928211165 80992441817972984598079187)
    ·
      refine ⟨121488662726959476897118781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80992441817972984598079187 121488662726959476897118781)
      ·
        refine ⟨45558248522609803836419543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121488662726959476897118781 45558248522609803836419543)
        ·
          refine ⟨68337372783914705754629315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45558248522609803836419543 68337372783914705754629315)
          ·
            refine ⟨102506059175872058631943973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68337372783914705754629315 102506059175872058631943973)
            ·
              refine ⟨19219886095476010993489495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102506059175872058631943973 19219886095476010993489495)
              ·
                refine ⟨28829829143214016490234243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19219886095476010993489495 28829829143214016490234243)
                ·
                  refine ⟨43244743714821024735351365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28829829143214016490234243 43244743714821024735351365)
                  ·
                    refine ⟨8108389446528942137878381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43244743714821024735351365 8108389446528942137878381)
                    ·
                      refine ⟨3040646042448353301704393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8108389446528942137878381 3040646042448353301704393)
                      ·
                        rfl

theorem cell23_5921637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_5921637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921637 prefixEnd_5921637 := by exact prefixLift 5921637
  have htrace : WordTrace (prefixWord ++ tailWord_5921637) baseStart_5921637 baseEnd_5921637 := by
    simpa [prefixWord, tailWord_5921637, baseEnd_5921637] using wordTrace_append hprefix tailTrace_5921637
  have hstable : (prefixWord ++ tailWord_5921637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921637).length < 2 ^ (prefixWord ++ tailWord_5921637).sum := by decide
  have hdescent : baseEnd_5921637 < baseStart_5921637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5921660 : Nat := 118140960795 + 5921660 * 2 ^ 59
def prefixEnd_5921660 : Nat := 4983230072969 + 3 ^ 40 * 5921660 * 2
def baseEnd_5921660 : Nat := 3040657852503406711716787

theorem tailTrace_5921660 : CollatzResearch.WordTrace tailWord_5921660 prefixEnd_5921660 3040657852503406711716787 := by
  unfold tailWord_5921660
  simp only [CollatzResearch.WordTrace]
  refine ⟨107990341863422316928149217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143987122484563089237532289 107990341863422316928149217)
  ·
    refine ⟨80992756397566737696111913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107990341863422316928149217 80992756397566737696111913)
    ·
      refine ⟨60744567298175053272083935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80992756397566737696111913 60744567298175053272083935)
      ·
        refine ⟨91116850947262579908125903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60744567298175053272083935 91116850947262579908125903)
        ·
          refine ⟨136675276420893869862188855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91116850947262579908125903 136675276420893869862188855)
          ·
            refine ⟨205012914631340804793283283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136675276420893869862188855 205012914631340804793283283)
            ·
              refine ⟨307519371947011207189924925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205012914631340804793283283 307519371947011207189924925)
              ·
                refine ⟨115319764480129202696221847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307519371947011207189924925 115319764480129202696221847)
                ·
                  refine ⟨172979646720193804044332771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115319764480129202696221847 172979646720193804044332771)
                  ·
                    refine ⟨259469470080290706066499157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172979646720193804044332771 259469470080290706066499157)
                    ·
                      refine ⟨3040657852503406711716787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 259469470080290706066499157 3040657852503406711716787)
                      ·
                        rfl

theorem cell23_5921660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5921660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921660 prefixEnd_5921660 := by exact prefixLift 5921660
  have htrace : WordTrace (prefixWord ++ tailWord_5921660) baseStart_5921660 baseEnd_5921660 := by
    simpa [prefixWord, tailWord_5921660, baseEnd_5921660] using wordTrace_append hprefix tailTrace_5921660
  have hstable : (prefixWord ++ tailWord_5921660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921660).length < 2 ^ (prefixWord ++ tailWord_5921660).sum := by decide
  have hdescent : baseEnd_5921660 < baseStart_5921660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921674 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_5921674 : Nat := 118140960795 + 5921674 * 2 ^ 59
def prefixEnd_5921674 : Nat := 4983230072969 + 3 ^ 40 * 5921674 * 2
def baseEnd_5921674 : Nat := 337851671248063295215747

theorem tailTrace_5921674 : CollatzResearch.WordTrace tailWord_5921674 prefixEnd_5921674 337851671248063295215747 := by
  unfold tailWord_5921674
  simp only [CollatzResearch.WordTrace]
  refine ⟨53995298587198478561827019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143987462899195942831538717 53995298587198478561827019)
  ·
    refine ⟨80992947880797717842740529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53995298587198478561827019 80992947880797717842740529)
    ·
      refine ⟨60744710910598288382055397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80992947880797717842740529 60744710910598288382055397)
      ·
        refine ⟨11389633295737179071635387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60744710910598288382055397 11389633295737179071635387)
        ·
          refine ⟨17084449943605768607453081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11389633295737179071635387 17084449943605768607453081)
          ·
            refine ⟨12813337457704326455589811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17084449943605768607453081 12813337457704326455589811)
            ·
              refine ⟨19220006186556489683384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12813337457704326455589811 19220006186556489683384717)
              ·
                refine ⟨7207502319958683631269269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19220006186556489683384717 7207502319958683631269269)
                ·
                  refine ⟨337851671248063295215747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7207502319958683631269269 337851671248063295215747)
                  ·
                    rfl

theorem cell23_5921674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_5921674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921674 prefixEnd_5921674 := by exact prefixLift 5921674
  have htrace : WordTrace (prefixWord ++ tailWord_5921674) baseStart_5921674 baseEnd_5921674 := by
    simpa [prefixWord, tailWord_5921674, baseEnd_5921674] using wordTrace_append hprefix tailTrace_5921674
  have hstable : (prefixWord ++ tailWord_5921674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921674).length < 2 ^ (prefixWord ++ tailWord_5921674).sum := by decide
  have hdescent : baseEnd_5921674 < baseStart_5921674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921680 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_5921680 : Nat := 118140960795 + 5921680 * 2 ^ 59
def prefixEnd_5921680 : Nat := 4983230072969 + 3 ^ 40 * 5921680 * 2
def baseEnd_5921680 : Nat := 3040668122116496633466695

theorem tailTrace_5921680 : CollatzResearch.WordTrace tailWord_5921680 prefixEnd_5921680 3040668122116496633466695 := by
  unfold tailWord_5921680
  simp only [CollatzResearch.WordTrace]
  refine ⟨107990706593386088636013247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143987608791181451514684329 107990706593386088636013247)
  ·
    refine ⟨161986059890079132954019871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107990706593386088636013247 161986059890079132954019871)
    ·
      refine ⟨242979089835118699431029807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161986059890079132954019871 242979089835118699431029807)
      ·
        refine ⟨364468634752678049146544711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242979089835118699431029807 364468634752678049146544711)
        ·
          refine ⟨546702952129017073719817067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364468634752678049146544711 546702952129017073719817067)
          ·
            refine ⟨820054428193525610579725601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546702952129017073719817067 820054428193525610579725601)
            ·
              refine ⟨615040821145144207934794201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820054428193525610579725601 615040821145144207934794201)
              ·
                refine ⟨461280615858858155951095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615040821145144207934794201 461280615858858155951095651)
                ·
                  refine ⟨691920923788287233926643477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461280615858858155951095651 691920923788287233926643477)
                  ·
                    refine ⟨32433793302575964090311413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 691920923788287233926643477 32433793302575964090311413)
                    ·
                      refine ⟨3040668122116496633466695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32433793302575964090311413 3040668122116496633466695)
                      ·
                        rfl

theorem cell23_5921680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_5921680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921680 prefixEnd_5921680 := by exact prefixLift 5921680
  have htrace : WordTrace (prefixWord ++ tailWord_5921680) baseStart_5921680 baseEnd_5921680 := by
    simpa [prefixWord, tailWord_5921680, baseEnd_5921680] using wordTrace_append hprefix tailTrace_5921680
  have hstable : (prefixWord ++ tailWord_5921680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921680).length < 2 ^ (prefixWord ++ tailWord_5921680).sum := by decide
  have hdescent : baseEnd_5921680 < baseStart_5921680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921687 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 3, 5]
def baseStart_5921687 : Nat := 118140960795 + 5921687 * 2 ^ 59
def prefixEnd_5921687 : Nat := 4983230072969 + 3 ^ 40 * 5921687 * 2
def baseEnd_5921687 : Nat := 1013557238827026035359721

theorem tailTrace_5921687 : CollatzResearch.WordTrace tailWord_5921687 prefixEnd_5921687 1013557238827026035359721 := by
  unfold tailWord_5921687
  simp only [CollatzResearch.WordTrace]
  refine ⟨215981668497746817467531315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143987778998497878311687543 215981668497746817467531315)
  ·
    refine ⟨323972502746620226201296973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215981668497746817467531315 323972502746620226201296973)
    ·
      refine ⟨121489688529982584825486365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323972502746620226201296973 121489688529982584825486365)
      ·
        refine ⟨45558633198743469309557387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121489688529982584825486365 45558633198743469309557387)
        ·
          refine ⟨68337949798115203964336081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45558633198743469309557387 68337949798115203964336081)
          ·
            refine ⟨51253462348586402973252061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68337949798115203964336081 51253462348586402973252061)
            ·
              refine ⟨19220048380719901114969523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51253462348586402973252061 19220048380719901114969523)
              ·
                refine ⟨28830072571079851672454285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19220048380719901114969523 28830072571079851672454285)
                ·
                  refine ⟨10811277214154944377170357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28830072571079851672454285 10811277214154944377170357)
                  ·
                    refine ⟨1013557238827026035359721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10811277214154944377170357 1013557238827026035359721)
                    ·
                      rfl

theorem cell23_5921687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_5921687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921687 prefixEnd_5921687 := by exact prefixLift 5921687
  have htrace : WordTrace (prefixWord ++ tailWord_5921687) baseStart_5921687 baseEnd_5921687 := by
    simpa [prefixWord, tailWord_5921687, baseEnd_5921687] using wordTrace_append hprefix tailTrace_5921687
  have hstable : (prefixWord ++ tailWord_5921687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921687).length < 2 ^ (prefixWord ++ tailWord_5921687).sum := by decide
  have hdescent : baseEnd_5921687 < baseStart_5921687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5921717 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_5921717 : Nat := 118140960795 + 5921717 * 2 ^ 59
def prefixEnd_5921717 : Nat := 4983230072969 + 3 ^ 40 * 5921717 * 2
def baseEnd_5921717 : Nat := 1013562373633570996234675

theorem tailTrace_5921717 : CollatzResearch.WordTrace tailWord_5921717 prefixEnd_5921717 1013562373633570996234675 := by
  unfold tailWord_5921717
  simp only [CollatzResearch.WordTrace]
  refine ⟨215982762687638132591123405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143988508458425421727415603 215982762687638132591123405)
  ·
    refine ⟨80993536007864299721671277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215982762687638132591123405 80993536007864299721671277)
    ·
      refine ⟨30372576002949112395626729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80993536007864299721671277 30372576002949112395626729)
      ·
        refine ⟨22779432002211834296720047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30372576002949112395626729 22779432002211834296720047)
        ·
          refine ⟨34169148003317751445080071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22779432002211834296720047 34169148003317751445080071)
          ·
            refine ⟨51253722004976627167620107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34169148003317751445080071 51253722004976627167620107)
            ·
              refine ⟨76880583007464940751430161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51253722004976627167620107 76880583007464940751430161)
              ·
                refine ⟨57660437255598705563572621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76880583007464940751430161 57660437255598705563572621)
                ·
                  refine ⟨21622663970849514586339733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57660437255598705563572621 21622663970849514586339733)
                  ·
                    refine ⟨1013562373633570996234675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21622663970849514586339733 1013562373633570996234675)
                    ·
                      rfl

theorem cell23_5921717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_5921717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5921717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5921717 prefixEnd_5921717 := by exact prefixLift 5921717
  have htrace : WordTrace (prefixWord ++ tailWord_5921717) baseStart_5921717 baseEnd_5921717 := by
    simpa [prefixWord, tailWord_5921717, baseEnd_5921717] using wordTrace_append hprefix tailTrace_5921717
  have hstable : (prefixWord ++ tailWord_5921717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5921717).length < 2 ^ (prefixWord ++ tailWord_5921717).sum := by decide
  have hdescent : baseEnd_5921717 < baseStart_5921717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5921717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
