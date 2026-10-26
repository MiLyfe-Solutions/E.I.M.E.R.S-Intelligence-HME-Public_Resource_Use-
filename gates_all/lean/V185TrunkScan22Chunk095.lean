import V185TrunkScan22Chunk094

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_852233 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 6]
def baseStart_852233 : Nat := 118140960795 + 852233 * 2 ^ 59
def prefixEnd_852233 : Nat := 4983230072969 + 3 ^ 40 * 852233 * 2
def baseEnd_852233 : Nat := 97245590805170970704035

theorem tailTrace_852233 : CollatzResearch.WordTrace tailWord_852233 prefixEnd_852233 97245590805170970704035 := by
  unfold tailWord_852233
  simp only [CollatzResearch.WordTrace]
  refine ⟨31083491121512865653697353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722327414341910435798235 31083491121512865653697353)
  ·
    refine ⟨23312618341134649240273015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31083491121512865653697353 23312618341134649240273015)
    ·
      refine ⟨34968927511701973860409523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23312618341134649240273015 34968927511701973860409523)
      ·
        refine ⟨52453391267552960790614285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968927511701973860409523 52453391267552960790614285)
        ·
          refine ⟨19670021725332360296480357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52453391267552960790614285 19670021725332360296480357)
          ·
            refine ⟨3688129073499817555590067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19670021725332360296480357 3688129073499817555590067)
            ·
              refine ⟨5532193610249726333385101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688129073499817555590067 5532193610249726333385101)
              ·
                refine ⟨2074572603843647375019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532193610249726333385101 2074572603843647375019413)
                ·
                  refine ⟨97245590805170970704035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2074572603843647375019413 97245590805170970704035)
                  ·
                    rfl

theorem cell22_852233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_852233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852233 prefixEnd_852233 := by exact prefixLift 852233
  have htrace : WordTrace (prefixWord ++ tailWord_852233) baseStart_852233 baseEnd_852233 := by
    simpa [prefixWord, tailWord_852233, baseEnd_852233] using wordTrace_append hprefix tailTrace_852233
  have hstable : (prefixWord ++ tailWord_852233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852233).length < 2 ^ (prefixWord ++ tailWord_852233).sum := by decide
  have hdescent : baseEnd_852233 < baseStart_852233 := by decide
  rcases family_descends (prefixWord ++ tailWord_852233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852387 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 1, 4]
def baseStart_852387 : Nat := 118140960795 + 852387 * 2 ^ 59
def prefixEnd_852387 : Nat := 4983230072969 + 3 ^ 40 * 852387 * 2
def baseEnd_852387 : Nat := 291789489762707843761633

theorem tailTrace_852387 : CollatzResearch.WordTrace tailWord_852387 prefixEnd_852387 291789489762707843761633 := by
  unfold tailWord_852387
  simp only [CollatzResearch.WordTrace]
  refine ⟨31089107962954949954803415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20726071975303299969868943 31089107962954949954803415)
  ·
    refine ⟨46633661944432424932205123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31089107962954949954803415 46633661944432424932205123)
    ·
      refine ⟨69950492916648637398307685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46633661944432424932205123 69950492916648637398307685)
      ·
        refine ⟨13115717421871619512182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69950492916648637398307685 13115717421871619512182691)
        ·
          refine ⟨19673576132807429268274037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115717421871619512182691 19673576132807429268274037)
          ·
            refine ⟨1844397762450696493900691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19673576132807429268274037 1844397762450696493900691)
            ·
              refine ⟨2766596643676044740851037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844397762450696493900691 2766596643676044740851037)
              ·
                refine ⟨1037473741378516777819139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2766596643676044740851037 1037473741378516777819139)
                ·
                  refine ⟨1556210612067775166728709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037473741378516777819139 1556210612067775166728709)
                  ·
                    refine ⟨291789489762707843761633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556210612067775166728709 291789489762707843761633)
                    ·
                      rfl

theorem cell22_852387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_852387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852387 prefixEnd_852387 := by exact prefixLift 852387
  have htrace : WordTrace (prefixWord ++ tailWord_852387) baseStart_852387 baseEnd_852387 := by
    simpa [prefixWord, tailWord_852387, baseEnd_852387] using wordTrace_append hprefix tailTrace_852387
  have hstable : (prefixWord ++ tailWord_852387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852387).length < 2 ^ (prefixWord ++ tailWord_852387).sum := by decide
  have hdescent : baseEnd_852387 < baseStart_852387 := by decide
  rcases family_descends (prefixWord ++ tailWord_852387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852402 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_852402 : Nat := 118140960795 + 852402 * 2 ^ 59
def prefixEnd_852402 : Nat := 4983230072969 + 3 ^ 40 * 852402 * 2
def baseEnd_852402 : Nat := 97264874856417601545529

theorem tailTrace_852402 : CollatzResearch.WordTrace tailWord_852402 prefixEnd_852402 97264874856417601545529 := by
  unfold tailWord_852402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772413764475151879149865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20726436705267071677732973 7772413764475151879149865)
  ·
    refine ⟨5829310323356363909362399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7772413764475151879149865 5829310323356363909362399)
    ·
      refine ⟨8743965485034545864043599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829310323356363909362399 8743965485034545864043599)
      ·
        refine ⟨13115948227551818796065399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743965485034545864043599 13115948227551818796065399)
        ·
          refine ⟨19673922341327728194098099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115948227551818796065399 19673922341327728194098099)
          ·
            refine ⟨29510883511991592291147149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19673922341327728194098099 29510883511991592291147149)
            ·
              refine ⟨11066581316996847109180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29510883511991592291147149 11066581316996847109180181)
              ·
                refine ⟨518745999234227208242821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11066581316996847109180181 518745999234227208242821)
                ·
                  refine ⟨97264874856417601545529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518745999234227208242821 97264874856417601545529)
                  ·
                    rfl

theorem cell22_852402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_852402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852402 prefixEnd_852402 := by exact prefixLift 852402
  have htrace : WordTrace (prefixWord ++ tailWord_852402) baseStart_852402 baseEnd_852402 := by
    simpa [prefixWord, tailWord_852402, baseEnd_852402] using wordTrace_append hprefix tailTrace_852402
  have hstable : (prefixWord ++ tailWord_852402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852402).length < 2 ^ (prefixWord ++ tailWord_852402).sum := by decide
  have hdescent : baseEnd_852402 < baseStart_852402 := by decide
  rcases family_descends (prefixWord ++ tailWord_852402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852436 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 4]
def baseStart_852436 : Nat := 118140960795 + 852436 * 2 ^ 59
def prefixEnd_852436 : Nat := 4983230072969 + 3 ^ 40 * 852436 * 2
def baseEnd_852436 : Nat := 97268754488029349762161

theorem tailTrace_852436 : CollatzResearch.WordTrace tailWord_852436 prefixEnd_852436 97268754488029349762161 := by
  unfold tailWord_852436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545447569888715661668581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20727263426518287548891441 15545447569888715661668581)
  ·
    refine ⟨2914771419354134186562859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15545447569888715661668581 2914771419354134186562859)
    ·
      refine ⟨4372157129031201279844289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914771419354134186562859 4372157129031201279844289)
      ·
        refine ⟨3279117846773400959883217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372157129031201279844289 3279117846773400959883217)
        ·
          refine ⟨2459338385080050719912413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279117846773400959883217 2459338385080050719912413)
          ·
            refine ⟨922251894405019019967155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2459338385080050719912413 922251894405019019967155)
            ·
              refine ⟨1383377841607528529950733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922251894405019019967155 1383377841607528529950733)
              ·
                refine ⟨518766690602823198731525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1383377841607528529950733 518766690602823198731525)
                ·
                  refine ⟨97268754488029349762161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518766690602823198731525 97268754488029349762161)
                  ·
                    rfl

theorem cell22_852436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_852436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852436 prefixEnd_852436 := by exact prefixLift 852436
  have htrace : WordTrace (prefixWord ++ tailWord_852436) baseStart_852436 baseEnd_852436 := by
    simpa [prefixWord, tailWord_852436, baseEnd_852436] using wordTrace_append hprefix tailTrace_852436
  have hstable : (prefixWord ++ tailWord_852436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852436).length < 2 ^ (prefixWord ++ tailWord_852436).sum := by decide
  have hdescent : baseEnd_852436 < baseStart_852436 := by decide
  rcases family_descends (prefixWord ++ tailWord_852436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852460 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_852460 : Nat := 118140960795 + 852460 * 2 ^ 59
def prefixEnd_852460 : Nat := 4983230072969 + 3 ^ 40 * 852460 * 2
def baseEnd_852460 : Nat := 291814479154559986686409

theorem tailTrace_852460 : CollatzResearch.WordTrace tailWord_852460 prefixEnd_852460 291814479154559986686409 := by
  unfold tailWord_852460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545885245845241711105417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20727846994460322281473889 15545885245845241711105417)
  ·
    refine ⟨11659413934383931283329063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15545885245845241711105417 11659413934383931283329063)
    ·
      refine ⟨17489120901575896924993595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659413934383931283329063 17489120901575896924993595)
      ·
        refine ⟨26233681352363845387490393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489120901575896924993595 26233681352363845387490393)
        ·
          refine ⟨19675261014272884040617795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26233681352363845387490393 19675261014272884040617795)
          ·
            refine ⟨29512891521409326060926693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19675261014272884040617795 29512891521409326060926693)
            ·
              refine ⟨5533667160264248636423755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29512891521409326060926693 5533667160264248636423755)
              ·
                refine ⟨8300500740396372954635633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533667160264248636423755 8300500740396372954635633)
                ·
                  refine ⟨6225375555297279715976725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300500740396372954635633 6225375555297279715976725)
                  ·
                    refine ⟨291814479154559986686409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6225375555297279715976725 291814479154559986686409)
                    ·
                      rfl

theorem cell22_852460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_852460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852460 prefixEnd_852460 := by exact prefixLift 852460
  have htrace : WordTrace (prefixWord ++ tailWord_852460) baseStart_852460 baseEnd_852460 := by
    simpa [prefixWord, tailWord_852460, baseEnd_852460] using wordTrace_append hprefix tailTrace_852460
  have hstable : (prefixWord ++ tailWord_852460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852460).length < 2 ^ (prefixWord ++ tailWord_852460).sum := by decide
  have hdescent : baseEnd_852460 < baseStart_852460 := by decide
  rcases family_descends (prefixWord ++ tailWord_852460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852509 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 5]
def baseStart_852509 : Nat := 118140960795 + 852509 * 2 ^ 59
def prefixEnd_852509 : Nat := 4983230072969 + 3 ^ 40 * 852509 * 2
def baseEnd_852509 : Nat := 97277084285313397403753

theorem tailTrace_852509 : CollatzResearch.WordTrace tailWord_852509 prefixEnd_852509 97277084285313397403753 := by
  unfold tailWord_852509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093557668512964790744581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20729038445675309860496387 31093557668512964790744581)
  ·
    refine ⟨5830042062846180898264609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31093557668512964790744581 5830042062846180898264609)
    ·
      refine ⟨4372531547134635673698457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5830042062846180898264609 4372531547134635673698457)
      ·
        refine ⟨3279398660350976755273843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372531547134635673698457 3279398660350976755273843)
        ·
          refine ⟨4919097990526465132910765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279398660350976755273843 4919097990526465132910765)
          ·
            refine ⟨1844661746447424424841537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4919097990526465132910765 1844661746447424424841537)
            ·
              refine ⟨1383496309835568318631153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844661746447424424841537 1383496309835568318631153)
              ·
                refine ⟨1037622232376676238973365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383496309835568318631153 1037622232376676238973365)
                ·
                  refine ⟨97277084285313397403753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037622232376676238973365 97277084285313397403753)
                  ·
                    rfl

theorem cell22_852509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_852509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852509 prefixEnd_852509 := by exact prefixLift 852509
  have htrace : WordTrace (prefixWord ++ tailWord_852509) baseStart_852509 baseEnd_852509 := by
    simpa [prefixWord, tailWord_852509, baseEnd_852509] using wordTrace_append hprefix tailTrace_852509
  have hstable : (prefixWord ++ tailWord_852509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852509).length < 2 ^ (prefixWord ++ tailWord_852509).sum := by decide
  have hdescent : baseEnd_852509 < baseStart_852509 := by decide
  rcases family_descends (prefixWord ++ tailWord_852509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852537 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 6]
def baseStart_852537 : Nat := 118140960795 + 852537 * 2 ^ 59
def prefixEnd_852537 : Nat := 4983230072969 + 3 ^ 40 * 852537 * 2
def baseEnd_852537 : Nat := 97280279276052484170391

theorem tailTrace_852537 : CollatzResearch.WordTrace tailWord_852537 prefixEnd_852537 97280279276052484170391 := by
  unfold tailWord_852537
  simp only [CollatzResearch.WordTrace]
  refine ⟨31094578912411525572763865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20729719274941017048509243 31094578912411525572763865)
  ·
    refine ⟨23320934184308644179572899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31094578912411525572763865 23320934184308644179572899)
    ·
      refine ⟨34981401276462966269359349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320934184308644179572899 34981401276462966269359349)
      ·
        refine ⟨3279506369668403087752439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34981401276462966269359349 3279506369668403087752439)
        ·
          refine ⟨4919259554502604631628659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279506369668403087752439 4919259554502604631628659)
          ·
            refine ⟨7378889331753906947442989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919259554502604631628659 7378889331753906947442989)
            ·
              refine ⟨2767083499407715105291121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7378889331753906947442989 2767083499407715105291121)
              ·
                refine ⟨2075312624555786328968341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767083499407715105291121 2075312624555786328968341)
                ·
                  refine ⟨97280279276052484170391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2075312624555786328968341 97280279276052484170391)
                  ·
                    rfl

theorem cell22_852537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_852537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852537 prefixEnd_852537 := by exact prefixLift 852537
  have htrace : WordTrace (prefixWord ++ tailWord_852537) baseStart_852537 baseEnd_852537 := by
    simpa [prefixWord, tailWord_852537, baseEnd_852537] using wordTrace_append hprefix tailTrace_852537
  have hstable : (prefixWord ++ tailWord_852537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852537).length < 2 ^ (prefixWord ++ tailWord_852537).sum := by decide
  have hdescent : baseEnd_852537 < baseStart_852537 := by decide
  rcases family_descends (prefixWord ++ tailWord_852537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852554 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_852554 : Nat := 118140960795 + 852554 * 2 ^ 59
def prefixEnd_852554 : Nat := 4983230072969 + 3 ^ 40 * 852554 * 2
def baseEnd_852554 : Nat := 97282219091858358278707

theorem tailTrace_852554 : CollatzResearch.WordTrace tailWord_852554 prefixEnd_852554 97282219091858358278707 := by
  unfold tailWord_852554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773799738337484369033179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20730132635566624984088477 7773799738337484369033179)
  ·
    refine ⟨11660699607506226553549769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773799738337484369033179 11660699607506226553549769)
    ·
      refine ⟨8745524705629669915162327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11660699607506226553549769 8745524705629669915162327)
      ·
        refine ⟨13118287058444504872743491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745524705629669915162327 13118287058444504872743491)
        ·
          refine ⟨19677430587666757309115237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13118287058444504872743491 19677430587666757309115237)
          ·
            refine ⟨3689518235187516995459107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19677430587666757309115237 3689518235187516995459107)
            ·
              refine ⟨5534277352781275493188661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689518235187516995459107 5534277352781275493188661)
              ·
                refine ⟨518838501823244577486437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5534277352781275493188661 518838501823244577486437)
                ·
                  refine ⟨97282219091858358278707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518838501823244577486437 97282219091858358278707)
                  ·
                    rfl

theorem cell22_852554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_852554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852554 prefixEnd_852554 := by exact prefixLift 852554
  have htrace : WordTrace (prefixWord ++ tailWord_852554) baseStart_852554 baseEnd_852554 := by
    simpa [prefixWord, tailWord_852554, baseEnd_852554] using wordTrace_append hprefix tailTrace_852554
  have hstable : (prefixWord ++ tailWord_852554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852554).length < 2 ^ (prefixWord ++ tailWord_852554).sum := by decide
  have hdescent : baseEnd_852554 < baseStart_852554 := by decide
  rcases family_descends (prefixWord ++ tailWord_852554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852567 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_852567 : Nat := 118140960795 + 852567 * 2 ^ 59
def prefixEnd_852567 : Nat := 4983230072969 + 3 ^ 40 * 852567 * 2
def baseEnd_852567 : Nat := 291851107441247374261081

theorem tailTrace_852567 : CollatzResearch.WordTrace tailWord_852567 prefixEnd_852567 291851107441247374261081 := by
  unfold tailWord_852567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31095673102302840696355955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20730448734868560464237303 31095673102302840696355955)
  ·
    refine ⟨46643509653454261044533933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31095673102302840696355955 46643509653454261044533933)
    ·
      refine ⟨17491316120045347891700225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46643509653454261044533933 17491316120045347891700225)
      ·
        refine ⟨13118487090034010918775169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17491316120045347891700225 13118487090034010918775169)
        ·
          refine ⟨9838865317525508189081377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13118487090034010918775169 9838865317525508189081377)
          ·
            refine ⟨7379148988144131141811033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9838865317525508189081377 7379148988144131141811033)
            ·
              refine ⟨5534361741108098356358275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379148988144131141811033 5534361741108098356358275)
              ·
                refine ⟨8301542611662147534537413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534361741108098356358275 8301542611662147534537413)
                ·
                  refine ⟨1556539239686652662725765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8301542611662147534537413 1556539239686652662725765)
                  ·
                    refine ⟨291851107441247374261081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556539239686652662725765 291851107441247374261081)
                    ·
                      rfl

theorem cell22_852567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_852567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852567 prefixEnd_852567 := by exact prefixLift 852567
  have htrace : WordTrace (prefixWord ++ tailWord_852567) baseStart_852567 baseEnd_852567 := by
    simpa [prefixWord, tailWord_852567, baseEnd_852567] using wordTrace_append hprefix tailTrace_852567
  have hstable : (prefixWord ++ tailWord_852567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852567).length < 2 ^ (prefixWord ++ tailWord_852567).sum := by decide
  have hdescent : baseEnd_852567 < baseStart_852567 := by decide
  rcases family_descends (prefixWord ++ tailWord_852567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852644 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_852644 : Nat := 118140960795 + 852644 * 2 ^ 59
def prefixEnd_852644 : Nat := 4983230072969 + 3 ^ 40 * 852644 * 2
def baseEnd_852644 : Nat := 97292488704948280028615

theorem tailTrace_852644 : CollatzResearch.WordTrace tailWord_852644 prefixEnd_852644 97292488704948280028615 := by
  unfold tailWord_852644
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549240761511941423454493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20732321015349255231272657 15549240761511941423454493)
  ·
    refine ⟨5830965285566978033795435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15549240761511941423454493 5830965285566978033795435)
    ·
      refine ⟨8746447928350467050693153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830965285566978033795435 8746447928350467050693153)
      ·
        refine ⟨6559835946262850288019865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8746447928350467050693153 6559835946262850288019865)
        ·
          refine ⟨4919876959697137716014899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6559835946262850288019865 4919876959697137716014899)
          ·
            refine ⟨7379815439545706574022349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919876959697137716014899 7379815439545706574022349)
            ·
              refine ⟨2767430789829639965258381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7379815439545706574022349 2767430789829639965258381)
              ·
                refine ⟨1037786546186114986971893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2767430789829639965258381 1037786546186114986971893)
                ·
                  refine ⟨97292488704948280028615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037786546186114986971893 97292488704948280028615)
                  ·
                    rfl

theorem cell22_852644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_852644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852644 prefixEnd_852644 := by exact prefixLift 852644
  have htrace : WordTrace (prefixWord ++ tailWord_852644) baseStart_852644 baseEnd_852644 := by
    simpa [prefixWord, tailWord_852644, baseEnd_852644] using wordTrace_append hprefix tailTrace_852644
  have hstable : (prefixWord ++ tailWord_852644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852644).length < 2 ^ (prefixWord ++ tailWord_852644).sum := by decide
  have hdescent : baseEnd_852644 < baseStart_852644 := by decide
  rcases family_descends (prefixWord ++ tailWord_852644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852704 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_852704 : Nat := 118140960795 + 852704 * 2 ^ 59
def prefixEnd_852704 : Nat := 4983230072969 + 3 ^ 40 * 852704 * 2
def baseEnd_852704 : Nat := 291898005341024683585661

theorem tailTrace_852704 : CollatzResearch.WordTrace tailWord_852704 prefixEnd_852704 291898005341024683585661 := by
  unfold tailWord_852704
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550334951403256547046583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20733779935204342062728777 15550334951403256547046583)
  ·
    refine ⟨23325502427104884820569875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15550334951403256547046583 23325502427104884820569875)
    ·
      refine ⟨34988253640657327230854813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23325502427104884820569875 34988253640657327230854813)
      ·
        refine ⟨13120595115246497711570555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34988253640657327230854813 13120595115246497711570555)
        ·
          refine ⟨19680892672869746567355833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13120595115246497711570555 19680892672869746567355833)
          ·
            refine ⟨14760669504652309925516875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19680892672869746567355833 14760669504652309925516875)
            ·
              refine ⟨22141004256978464888275313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14760669504652309925516875 22141004256978464888275313)
              ·
                refine ⟨16605753192733848666206485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22141004256978464888275313 16605753192733848666206485)
                ·
                  refine ⟨778394680909399156228429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16605753192733848666206485 778394680909399156228429)
                  ·
                    refine ⟨291898005341024683585661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778394680909399156228429 291898005341024683585661)
                    ·
                      rfl

theorem cell22_852704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_852704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852704 prefixEnd_852704 := by exact prefixLift 852704
  have htrace : WordTrace (prefixWord ++ tailWord_852704) baseStart_852704 baseEnd_852704 := by
    simpa [prefixWord, tailWord_852704, baseEnd_852704] using wordTrace_append hprefix tailTrace_852704
  have hstable : (prefixWord ++ tailWord_852704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852704).length < 2 ^ (prefixWord ++ tailWord_852704).sum := by decide
  have hdescent : baseEnd_852704 < baseStart_852704 := by decide
  rcases family_descends (prefixWord ++ tailWord_852704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852719 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_852719 : Nat := 118140960795 + 852719 * 2 ^ 59
def prefixEnd_852719 : Nat := 4983230072969 + 3 ^ 40 * 852719 * 2
def baseEnd_852719 : Nat := 291903140147569644460615

theorem tailTrace_852719 : CollatzResearch.WordTrace tailWord_852719 prefixEnd_852719 291903140147569644460615 := by
  unfold tailWord_852719
  simp only [CollatzResearch.WordTrace]
  refine ⟨31101216997752170655889211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20734144665168113770592807 31101216997752170655889211)
  ·
    refine ⟨46651825496628255983833817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31101216997752170655889211 46651825496628255983833817)
    ·
      refine ⟨34988869122471191987875363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46651825496628255983833817 34988869122471191987875363)
      ·
        refine ⟨52483303683706787981813045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34988869122471191987875363 52483303683706787981813045)
        ·
          refine ⟨4920309720347511373294973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52483303683706787981813045 4920309720347511373294973)
          ·
            refine ⟨1845116145130316764985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4920309720347511373294973 1845116145130316764985615)
            ·
              refine ⟨2767674217695475147478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845116145130316764985615 2767674217695475147478423)
              ·
                refine ⟨4151511326543212721217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767674217695475147478423 4151511326543212721217635)
                ·
                  refine ⟨6227266989814819081826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151511326543212721217635 6227266989814819081826453)
                  ·
                    refine ⟨291903140147569644460615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6227266989814819081826453 291903140147569644460615)
                    ·
                      rfl

theorem cell22_852719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_852719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852719 prefixEnd_852719 := by exact prefixLift 852719
  have htrace : WordTrace (prefixWord ++ tailWord_852719) baseStart_852719 baseEnd_852719 := by
    simpa [prefixWord, tailWord_852719, baseEnd_852719] using wordTrace_append hprefix tailTrace_852719
  have hstable : (prefixWord ++ tailWord_852719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852719).length < 2 ^ (prefixWord ++ tailWord_852719).sum := by decide
  have hdescent : baseEnd_852719 < baseStart_852719 := by decide
  rcases family_descends (prefixWord ++ tailWord_852719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852738 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_852738 : Nat := 118140960795 + 852738 * 2 ^ 59
def prefixEnd_852738 : Nat := 4983230072969 + 3 ^ 40 * 852738 * 2
def baseEnd_852738 : Nat := 291909644235859928235557

theorem tailTrace_852738 : CollatzResearch.WordTrace tailWord_852738 prefixEnd_852738 291909644235859928235557 := by
  unfold tailWord_852738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775477496170834225207717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20734606656455557933887245 7775477496170834225207717)
  ·
    refine ⟨1457902030532031417226447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7775477496170834225207717 1457902030532031417226447)
    ·
      refine ⟨2186853045798047125839671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457902030532031417226447 2186853045798047125839671)
      ·
        refine ⟨3280279568697070688759507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186853045798047125839671 3280279568697070688759507)
        ·
          refine ⟨4920419353045606033139261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280279568697070688759507 4920419353045606033139261)
          ·
            refine ⟨1845157257392102262427223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4920419353045606033139261 1845157257392102262427223)
            ·
              refine ⟨2767735886088153393640835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845157257392102262427223 2767735886088153393640835)
              ·
                refine ⟨4151603829132230090461253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767735886088153393640835 4151603829132230090461253)
                ·
                  refine ⟨778425717962293141961485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4151603829132230090461253 778425717962293141961485)
                  ·
                    refine ⟨291909644235859928235557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778425717962293141961485 291909644235859928235557)
                    ·
                      rfl

theorem cell22_852738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_852738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852738 prefixEnd_852738 := by exact prefixLift 852738
  have htrace : WordTrace (prefixWord ++ tailWord_852738) baseStart_852738 baseEnd_852738 := by
    simpa [prefixWord, tailWord_852738, baseEnd_852738] using wordTrace_append hprefix tailTrace_852738
  have hstable : (prefixWord ++ tailWord_852738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852738).length < 2 ^ (prefixWord ++ tailWord_852738).sum := by decide
  have hdescent : baseEnd_852738 < baseStart_852738 := by decide
  rcases family_descends (prefixWord ++ tailWord_852738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852806 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_852806 : Nat := 118140960795 + 852806 * 2 ^ 59
def prefixEnd_852806 : Nat := 4983230072969 + 3 ^ 40 * 852806 * 2
def baseEnd_852806 : Nat := 291932922025530417535349

theorem tailTrace_852806 : CollatzResearch.WordTrace tailWord_852806 prefixEnd_852806 291932922025530417535349 := by
  unfold tailWord_852806
  simp only [CollatzResearch.WordTrace]
  refine ⟨972012192138655766072071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20736260098957989676204181 972012192138655766072071)
  ·
    refine ⟨1458018288207983649108107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972012192138655766072071 1458018288207983649108107)
    ·
      refine ⟨2187027432311975473662161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458018288207983649108107 2187027432311975473662161)
      ·
        refine ⟨1640270574233981605246621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187027432311975473662161 1640270574233981605246621)
        ·
          refine ⟨615101465337743101967483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1640270574233981605246621 615101465337743101967483)
          ·
            refine ⟨922652198006614652951225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615101465337743101967483 922652198006614652951225)
            ·
              refine ⟨691989148504960989713419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922652198006614652951225 691989148504960989713419)
              ·
                refine ⟨1037983722757441484570129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691989148504960989713419 1037983722757441484570129)
                ·
                  refine ⟨778487792068081113427597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037983722757441484570129 778487792068081113427597)
                  ·
                    refine ⟨291932922025530417535349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778487792068081113427597 291932922025530417535349)
                    ·
                      rfl

theorem cell22_852806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_852806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852806 prefixEnd_852806 := by exact prefixLift 852806
  have htrace : WordTrace (prefixWord ++ tailWord_852806) baseStart_852806 baseEnd_852806 := by
    simpa [prefixWord, tailWord_852806, baseEnd_852806] using wordTrace_append hprefix tailTrace_852806
  have hstable : (prefixWord ++ tailWord_852806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852806).length < 2 ^ (prefixWord ++ tailWord_852806).sum := by decide
  have hdescent : baseEnd_852806 < baseStart_852806 := by decide
  rcases family_descends (prefixWord ++ tailWord_852806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852824 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_852824 : Nat := 118140960795 + 852824 * 2 ^ 59
def prefixEnd_852824 : Nat := 4983230072969 + 3 ^ 40 * 852824 * 2
def baseEnd_852824 : Nat := 97313027931128123528431

theorem tailTrace_852824 : CollatzResearch.WordTrace tailWord_852824 prefixEnd_852824 97313027931128123528431 := by
  unfold tailWord_852824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15552523331185886794230763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20736697774914515725641017 15552523331185886794230763)
  ·
    refine ⟨23328784996778830191346145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15552523331185886794230763 23328784996778830191346145)
    ·
      refine ⟨17496588747584122643509609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23328784996778830191346145 17496588747584122643509609)
      ·
        refine ⟨13122441560688091982632207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17496588747584122643509609 13122441560688091982632207)
        ·
          refine ⟨19683662341032137973948311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122441560688091982632207 19683662341032137973948311)
          ·
            refine ⟨29525493511548206960922467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19683662341032137973948311 29525493511548206960922467)
            ·
              refine ⟨44288240267322310441383701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29525493511548206960922467 44288240267322310441383701)
              ·
                refine ⟨2076011262530733301939861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44288240267322310441383701 2076011262530733301939861)
                ·
                  refine ⟨97313027931128123528431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2076011262530733301939861 97313027931128123528431)
                  ·
                    rfl

theorem cell22_852824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_852824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852824 prefixEnd_852824 := by exact prefixLift 852824
  have htrace : WordTrace (prefixWord ++ tailWord_852824) baseStart_852824 baseEnd_852824 := by
    simpa [prefixWord, tailWord_852824, baseEnd_852824] using wordTrace_append hprefix tailTrace_852824
  have hstable : (prefixWord ++ tailWord_852824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852824).length < 2 ^ (prefixWord ++ tailWord_852824).sum := by decide
  have hdescent : baseEnd_852824 < baseStart_852824 := by decide
  rcases family_descends (prefixWord ++ tailWord_852824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852826 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_852826 : Nat := 118140960795 + 852826 * 2 ^ 59
def prefixEnd_852826 : Nat := 4983230072969 + 3 ^ 40 * 852826 * 2
def baseEnd_852826 : Nat := 291939768434257032035287

theorem tailTrace_852826 : CollatzResearch.WordTrace tailWord_852826 prefixEnd_852826 291939768434257032035287 := by
  unfold tailWord_852826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776279902091131982508583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20736746405576351953356221 7776279902091131982508583)
  ·
    refine ⟨11664419853136697973762875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776279902091131982508583 11664419853136697973762875)
    ·
      refine ⟨17496629779705046960644313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664419853136697973762875 17496629779705046960644313)
      ·
        refine ⟨13122472334778785220483235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17496629779705046960644313 13122472334778785220483235)
        ·
          refine ⟨19683708502168177830724853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122472334778785220483235 19683708502168177830724853)
          ·
            refine ⟨1845347672078266671630455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19683708502168177830724853 1845347672078266671630455)
            ·
              refine ⟨2768021508117400007445683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845347672078266671630455 2768021508117400007445683)
              ·
                refine ⟨4152032262176100011168525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768021508117400007445683 4152032262176100011168525)
                ·
                  refine ⟨1557012098316037504188197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4152032262176100011168525 1557012098316037504188197)
                  ·
                    refine ⟨291939768434257032035287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557012098316037504188197 291939768434257032035287)
                    ·
                      rfl

theorem cell22_852826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_852826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852826 prefixEnd_852826 := by exact prefixLift 852826
  have htrace : WordTrace (prefixWord ++ tailWord_852826) baseStart_852826 baseEnd_852826 := by
    simpa [prefixWord, tailWord_852826, baseEnd_852826] using wordTrace_append hprefix tailTrace_852826
  have hstable : (prefixWord ++ tailWord_852826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852826).length < 2 ^ (prefixWord ++ tailWord_852826).sum := by decide
  have hdescent : baseEnd_852826 < baseStart_852826 := by decide
  rcases family_descends (prefixWord ++ tailWord_852826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852873 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_852873 : Nat := 118140960795 + 852873 * 2 ^ 59
def prefixEnd_852873 : Nat := 4983230072969 + 3 ^ 40 * 852873 * 2
def baseEnd_852873 : Nat := 291955857494764576110143

theorem tailTrace_852873 : CollatzResearch.WordTrace tailWord_852873 prefixEnd_852873 291955857494764576110143 := by
  unfold tailWord_852873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31106833839194254956995273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20737889226129503304663515 31106833839194254956995273)
  ·
    refine ⟨23330125379395691217746455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31106833839194254956995273 23330125379395691217746455)
    ·
      refine ⟨34995188069093536826619683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23330125379395691217746455 34995188069093536826619683)
      ·
        refine ⟨52492782103640305239929525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34995188069093536826619683 52492782103640305239929525)
        ·
          refine ⟨4921198322216278616243393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52492782103640305239929525 4921198322216278616243393)
          ·
            refine ⟨3690898741662208962182545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4921198322216278616243393 3690898741662208962182545)
            ·
              refine ⟨2768174056246656721636909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690898741662208962182545 2768174056246656721636909)
              ·
                refine ⟨1038065271092496270613841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768174056246656721636909 1038065271092496270613841)
                ·
                  refine ⟨778548953319372202960381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1038065271092496270613841 778548953319372202960381)
                  ·
                    refine ⟨291955857494764576110143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778548953319372202960381 291955857494764576110143)
                    ·
                      rfl

theorem cell22_852873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_852873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852873 prefixEnd_852873 := by exact prefixLift 852873
  have htrace : WordTrace (prefixWord ++ tailWord_852873) baseStart_852873 baseEnd_852873 := by
    simpa [prefixWord, tailWord_852873, baseEnd_852873] using wordTrace_append hprefix tailTrace_852873
  have hstable : (prefixWord ++ tailWord_852873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852873).length < 2 ^ (prefixWord ++ tailWord_852873).sum := by decide
  have hdescent : baseEnd_852873 < baseStart_852873 := by decide
  rcases family_descends (prefixWord ++ tailWord_852873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852952 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 1, 3]
def baseStart_852952 : Nat := 118140960795 + 852952 * 2 ^ 59
def prefixEnd_852952 : Nat := 4983230072969 + 3 ^ 40 * 852952 * 2
def baseEnd_852952 : Nat := 291982900809234703384901

theorem tailTrace_852952 : CollatzResearch.WordTrace tailWord_852952 prefixEnd_852952 291982900809234703384901 := by
  unfold tailWord_852952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15554857602954025724560555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20739810137272034299414073 15554857602954025724560555)
  ·
    refine ⟨23332286404431038586840833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15554857602954025724560555 23332286404431038586840833)
    ·
      refine ⟨17499214803323278940130625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23332286404431038586840833 17499214803323278940130625)
      ·
        refine ⟨13124411102492459205097969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17499214803323278940130625 13124411102492459205097969)
        ·
          refine ⟨9843308326869344403823477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124411102492459205097969 9843308326869344403823477)
          ·
            refine ⟨922810155644001037858451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9843308326869344403823477 922810155644001037858451)
            ·
              refine ⟨1384215233466001556787677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922810155644001037858451 1384215233466001556787677)
              ·
                refine ⟨519080712549750583795379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384215233466001556787677 519080712549750583795379)
                ·
                  refine ⟨778621068824625875693069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519080712549750583795379 778621068824625875693069)
                  ·
                    refine ⟨291982900809234703384901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778621068824625875693069 291982900809234703384901)
                    ·
                      rfl

theorem cell22_852952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_852952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852952 prefixEnd_852952 := by exact prefixLift 852952
  have htrace : WordTrace (prefixWord ++ tailWord_852952) baseStart_852952 baseEnd_852952 := by
    simpa [prefixWord, tailWord_852952, baseEnd_852952] using wordTrace_append hprefix tailTrace_852952
  have hstable : (prefixWord ++ tailWord_852952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852952).length < 2 ^ (prefixWord ++ tailWord_852952).sum := by decide
  have hdescent : baseEnd_852952 < baseStart_852952 := by decide
  rcases family_descends (prefixWord ++ tailWord_852952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852961 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_852961 : Nat := 118140960795 + 852961 * 2 ^ 59
def prefixEnd_852961 : Nat := 4983230072969 + 3 ^ 40 * 852961 * 2
def baseEnd_852961 : Nat := 291985981693161679909873

theorem tailTrace_852961 : CollatzResearch.WordTrace tailWord_852961 prefixEnd_852961 291985981693161679909873 := by
  unfold tailWord_852961
  simp only [CollatzResearch.WordTrace]
  refine ⟨31110043462875445986198737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20740028975250297324132491 31110043462875445986198737)
  ·
    refine ⟨23332532597156584489649053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31110043462875445986198737 23332532597156584489649053)
    ·
      refine ⟨8749699723933719183618395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23332532597156584489649053 8749699723933719183618395)
      ·
        refine ⟨13124549585900578775427593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8749699723933719183618395 13124549585900578775427593)
        ·
          refine ⟨9843412189425434081570695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124549585900578775427593 9843412189425434081570695)
          ·
            refine ⟨14765118284138151122356043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843412189425434081570695 14765118284138151122356043)
            ·
              refine ⟨22147677426207226683534065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14765118284138151122356043 22147677426207226683534065)
              ·
                refine ⟨16610758069655420012650549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22147677426207226683534065 16610758069655420012650549)
                ·
                  refine ⟨1557258569030195626185989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16610758069655420012650549 1557258569030195626185989)
                  ·
                    refine ⟨291985981693161679909873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557258569030195626185989 291985981693161679909873)
                    ·
                      rfl

theorem cell22_852961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_852961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852961 prefixEnd_852961 := by exact prefixLift 852961
  have htrace : WordTrace (prefixWord ++ tailWord_852961) baseStart_852961 baseEnd_852961 := by
    simpa [prefixWord, tailWord_852961, baseEnd_852961] using wordTrace_append hprefix tailTrace_852961
  have hstable : (prefixWord ++ tailWord_852961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852961).length < 2 ^ (prefixWord ++ tailWord_852961).sum := by decide
  have hdescent : baseEnd_852961 < baseStart_852961 := by decide
  rcases family_descends (prefixWord ++ tailWord_852961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852982 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_852982 : Nat := 118140960795 + 852982 * 2 ^ 59
def prefixEnd_852982 : Nat := 4983230072969 + 3 ^ 40 * 852982 * 2
def baseEnd_852982 : Nat := 97331056807441541711603

theorem tailTrace_852982 : CollatzResearch.WordTrace tailWord_852982 prefixEnd_852982 97331056807441541711603 := by
  unfold tailWord_852982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944425587237460410794575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20740539597199577715142133 1944425587237460410794575)
  ·
    refine ⟨2916638380856190616191863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1944425587237460410794575 2916638380856190616191863)
    ·
      refine ⟨4374957571284285924287795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2916638380856190616191863 4374957571284285924287795)
      ·
        refine ⟨6562436356926428886431693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374957571284285924287795 6562436356926428886431693)
        ·
          refine ⟨2460913633847410832411885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6562436356926428886431693 2460913633847410832411885)
          ·
            refine ⟨922842612692779062154457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2460913633847410832411885 922842612692779062154457)
            ·
              refine ⟨692131959519584296615843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922842612692779062154457 692131959519584296615843)
              ·
                refine ⟨1038197939279376444923765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692131959519584296615843 1038197939279376444923765)
                ·
                  refine ⟨97331056807441541711603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038197939279376444923765 97331056807441541711603)
                  ·
                    rfl

theorem cell22_852982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_852982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_852982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_852982 prefixEnd_852982 := by exact prefixLift 852982
  have htrace : WordTrace (prefixWord ++ tailWord_852982) baseStart_852982 baseEnd_852982 := by
    simpa [prefixWord, tailWord_852982, baseEnd_852982] using wordTrace_append hprefix tailTrace_852982
  have hstable : (prefixWord ++ tailWord_852982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852982).length < 2 ^ (prefixWord ++ tailWord_852982).sum := by decide
  have hdescent : baseEnd_852982 < baseStart_852982 := by decide
  rcases family_descends (prefixWord ++ tailWord_852982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853021 : List Nat := [1, 4, 2, 2, 13]
def baseStart_853021 : Nat := 118140960795 + 853021 * 2 ^ 59
def prefixEnd_853021 : Nat := 4983230072969 + 3 ^ 40 * 853021 * 2
def baseEnd_853021 : Nat := 1201672925593998038723

theorem tailTrace_853021 : CollatzResearch.WordTrace tailWord_853021 prefixEnd_853021 1201672925593998038723 := by
  unfold tailWord_853021
  simp only [CollatzResearch.WordTrace]
  refine ⟨31112231842658076233382917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741487895105384155588611 31112231842658076233382917)
  ·
    refine ⟨5833543470498389293759297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31112231842658076233382917 5833543470498389293759297)
    ·
      refine ⟨4375157602873791970319473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5833543470498389293759297 4375157602873791970319473)
      ·
        refine ⟨3281368202155343977739605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375157602873791970319473 3281368202155343977739605)
        ·
          refine ⟨1201672925593998038723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3281368202155343977739605 1201672925593998038723)
          ·
            rfl

theorem cell22_853021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 13].length) (baseStart_853021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853021 prefixEnd_853021 := by exact prefixLift 853021
  have htrace : WordTrace (prefixWord ++ tailWord_853021) baseStart_853021 baseEnd_853021 := by
    simpa [prefixWord, tailWord_853021, baseEnd_853021] using wordTrace_append hprefix tailTrace_853021
  have hstable : (prefixWord ++ tailWord_853021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853021).length < 2 ^ (prefixWord ++ tailWord_853021).sum := by decide
  have hdescent : baseEnd_853021 < baseStart_853021 := by decide
  rcases family_descends (prefixWord ++ tailWord_853021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853023 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_853023 : Nat := 118140960795 + 853023 * 2 ^ 59
def prefixEnd_853023 : Nat := 4983230072969 + 3 ^ 40 * 853023 * 2
def baseEnd_853023 : Nat := 292007205560214184859683

theorem tailTrace_853023 : CollatzResearch.WordTrace tailWord_853023 prefixEnd_853023 292007205560214184859683 := by
  unfold tailWord_853023
  simp only [CollatzResearch.WordTrace]
  refine ⟨31112304788650830574955723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741536525767220383303815 31112304788650830574955723)
  ·
    refine ⟨46668457182976245862433585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31112304788650830574955723 46668457182976245862433585)
    ·
      refine ⟨35001342887232184396825189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46668457182976245862433585 35001342887232184396825189)
      ·
        refine ⟨6562751791356034574404723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35001342887232184396825189 6562751791356034574404723)
        ·
          refine ⟨9844127687034051861607085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562751791356034574404723 9844127687034051861607085)
          ·
            refine ⟨3691547882637769448102657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9844127687034051861607085 3691547882637769448102657)
            ·
              refine ⟨2768660911978327086076993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691547882637769448102657 2768660911978327086076993)
              ·
                refine ⟨2076495683983745314557745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768660911978327086076993 2076495683983745314557745)
                ·
                  refine ⟨1557371762987808985918309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076495683983745314557745 1557371762987808985918309)
                  ·
                    refine ⟨292007205560214184859683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557371762987808985918309 292007205560214184859683)
                    ·
                      rfl

theorem cell22_853023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_853023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853023 prefixEnd_853023 := by exact prefixLift 853023
  have htrace : WordTrace (prefixWord ++ tailWord_853023) baseStart_853023 baseEnd_853023 := by
    simpa [prefixWord, tailWord_853023, baseEnd_853023] using wordTrace_append hprefix tailTrace_853023
  have hstable : (prefixWord ++ tailWord_853023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853023).length < 2 ^ (prefixWord ++ tailWord_853023).sum := by decide
  have hdescent : baseEnd_853023 < baseStart_853023 := by decide
  rcases family_descends (prefixWord ++ tailWord_853023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853025 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_853025 : Nat := 118140960795 + 853025 * 2 ^ 59
def prefixEnd_853025 : Nat := 4983230072969 + 3 ^ 40 * 853025 * 2
def baseEnd_853025 : Nat := 292007890201086846309677

theorem tailTrace_853025 : CollatzResearch.WordTrace tailWord_853025 prefixEnd_853025 292007890201086846309677 := by
  unfold tailWord_853025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31112377734643584916528529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741585156429056611019019 31112377734643584916528529)
  ·
    refine ⟨23334283300982688687396397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31112377734643584916528529 23334283300982688687396397)
    ·
      refine ⟨8750356237868508257773649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23334283300982688687396397 8750356237868508257773649)
      ·
        refine ⟨6562767178401381193330237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8750356237868508257773649 6562767178401381193330237)
        ·
          refine ⟨2461037691900517947498839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6562767178401381193330237 2461037691900517947498839)
          ·
            refine ⟨3691556537850776921248259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461037691900517947498839 3691556537850776921248259)
            ·
              refine ⟨5537334806776165381872389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691556537850776921248259 5537334806776165381872389)
              ·
                refine ⟨1038250276270531009101073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5537334806776165381872389 1038250276270531009101073)
                ·
                  refine ⟨778687707202898256825805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1038250276270531009101073 778687707202898256825805)
                  ·
                    refine ⟨292007890201086846309677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778687707202898256825805 292007890201086846309677)
                    ·
                      rfl

theorem cell22_853025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_853025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853025 prefixEnd_853025 := by exact prefixLift 853025
  have htrace : WordTrace (prefixWord ++ tailWord_853025) baseStart_853025 baseEnd_853025 := by
    simpa [prefixWord, tailWord_853025, baseEnd_853025] using wordTrace_append hprefix tailTrace_853025
  have hstable : (prefixWord ++ tailWord_853025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853025).length < 2 ^ (prefixWord ++ tailWord_853025).sum := by decide
  have hdescent : baseEnd_853025 < baseStart_853025 := by decide
  rcases family_descends (prefixWord ++ tailWord_853025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853027 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 4]
def baseStart_853027 : Nat := 118140960795 + 853027 * 2 ^ 59
def prefixEnd_853027 : Nat := 4983230072969 + 3 ^ 40 * 853027 * 2
def baseEnd_853027 : Nat := 97336191613986502586557

theorem tailTrace_853027 : CollatzResearch.WordTrace tailWord_853027 prefixEnd_853027 97336191613986502586557 := by
  unfold tailWord_853027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31112450680636339258101335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741633787090892838734223 31112450680636339258101335)
  ·
    refine ⟨46668676020954508887152003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31112450680636339258101335 46668676020954508887152003)
    ·
      refine ⟨70003014031431763330728005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46668676020954508887152003 70003014031431763330728005)
      ·
        refine ⟨13125565130893455624511501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70003014031431763330728005 13125565130893455624511501)
        ·
          refine ⟨4922086924085045859191813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13125565130893455624511501 4922086924085045859191813)
          ·
            refine ⟨922891298265946098598465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4922086924085045859191813 922891298265946098598465)
            ·
              refine ⟨692168473699459573948849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922891298265946098598465 692168473699459573948849)
              ·
                refine ⟨519126355274594680461637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692168473699459573948849 519126355274594680461637)
                ·
                  refine ⟨97336191613986502586557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519126355274594680461637 97336191613986502586557)
                  ·
                    rfl

theorem cell22_853027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 4].length) (baseStart_853027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853027 prefixEnd_853027 := by exact prefixLift 853027
  have htrace : WordTrace (prefixWord ++ tailWord_853027) baseStart_853027 baseEnd_853027 := by
    simpa [prefixWord, tailWord_853027, baseEnd_853027] using wordTrace_append hprefix tailTrace_853027
  have hstable : (prefixWord ++ tailWord_853027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853027).length < 2 ^ (prefixWord ++ tailWord_853027).sum := by decide
  have hdescent : baseEnd_853027 < baseStart_853027 := by decide
  rcases family_descends (prefixWord ++ tailWord_853027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853057 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_853057 : Nat := 118140960795 + 853057 * 2 ^ 59
def prefixEnd_853057 : Nat := 4983230072969 + 3 ^ 40 * 853057 * 2
def baseEnd_853057 : Nat := 292018844455049429509579

theorem tailTrace_853057 : CollatzResearch.WordTrace tailWord_853057 prefixEnd_853057 292018844455049429509579 := by
  unfold tailWord_853057
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113544870527654381693425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20742363247018436254462283 31113544870527654381693425)
  ·
    refine ⟨23335158652895740786270069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31113544870527654381693425 23335158652895740786270069)
    ·
      refine ⟨2187671123708975698712819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23335158652895740786270069 2187671123708975698712819)
      ·
        refine ⟨3281506685563463548069229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187671123708975698712819 3281506685563463548069229)
        ·
          refine ⟨1230565007086298830525961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3281506685563463548069229 1230565007086298830525961)
          ·
            refine ⟨922923755314724122894471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230565007086298830525961 922923755314724122894471)
            ·
              refine ⟨1384385632972086184341707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922923755314724122894471 1384385632972086184341707)
              ·
                refine ⟨2076578449458129276512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384385632972086184341707 2076578449458129276512561)
                ·
                  refine ⟨1557433837093596957384421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076578449458129276512561 1557433837093596957384421)
                  ·
                    refine ⟨292018844455049429509579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557433837093596957384421 292018844455049429509579)
                    ·
                      rfl

theorem cell22_853057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_853057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853057 prefixEnd_853057 := by exact prefixLift 853057
  have htrace : WordTrace (prefixWord ++ tailWord_853057) baseStart_853057 baseEnd_853057 := by
    simpa [prefixWord, tailWord_853057, baseEnd_853057] using wordTrace_append hprefix tailTrace_853057
  have hstable : (prefixWord ++ tailWord_853057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853057).length < 2 ^ (prefixWord ++ tailWord_853057).sum := by decide
  have hdescent : baseEnd_853057 < baseStart_853057 := by decide
  rcases family_descends (prefixWord ++ tailWord_853057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853100 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_853100 : Nat := 118140960795 + 853100 * 2 ^ 59
def prefixEnd_853100 : Nat := 4983230072969 + 3 ^ 40 * 853100 * 2
def baseEnd_853100 : Nat := 97344521411270550228149

theorem tailTrace_853100 : CollatzResearch.WordTrace tailWord_853100 prefixEnd_853100 97344521411270550228149 := by
  unfold tailWord_853100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557556604685936362754377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743408806247915150339169 15557556604685936362754377)
  ·
    refine ⟨11668167453514452272065783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557556604685936362754377 11668167453514452272065783)
    ·
      refine ⟨17502251180271678408098675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668167453514452272065783 17502251180271678408098675)
      ·
        refine ⟨26253376770407517612148013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502251180271678408098675 26253376770407517612148013)
        ·
          refine ⟨9845016288902819104555505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26253376770407517612148013 9845016288902819104555505)
          ·
            refine ⟨7383762216677114328416629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845016288902819104555505 7383762216677114328416629)
            ·
              refine ⟨692227707813479468289059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7383762216677114328416629 692227707813479468289059)
              ·
                refine ⟨1038341561720219202433589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692227707813479468289059 1038341561720219202433589)
                ·
                  refine ⟨97344521411270550228149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038341561720219202433589 97344521411270550228149)
                  ·
                    rfl

theorem cell22_853100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_853100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853100 prefixEnd_853100 := by exact prefixLift 853100
  have htrace : WordTrace (prefixWord ++ tailWord_853100) baseStart_853100 baseEnd_853100 := by
    simpa [prefixWord, tailWord_853100, baseEnd_853100] using wordTrace_append hprefix tailTrace_853100
  have hstable : (prefixWord ++ tailWord_853100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853100).length < 2 ^ (prefixWord ++ tailWord_853100).sum := by decide
  have hdescent : baseEnd_853100 < baseStart_853100 := by decide
  rcases family_descends (prefixWord ++ tailWord_853100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853130 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_853130 : Nat := 118140960795 + 853130 * 2 ^ 59
def prefixEnd_853130 : Nat := 4983230072969 + 3 ^ 40 * 853130 * 2
def baseEnd_853130 : Nat := 292043833846901572434355

theorem tailTrace_853130 : CollatzResearch.WordTrace tailWord_853130 prefixEnd_853130 292043833846901572434355 := by
  unfold tailWord_853130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779051849815796962275211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20744138266175458566067229 7779051849815796962275211)
  ·
    refine ⟨11668577774723695443412817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779051849815796962275211 11668577774723695443412817)
    ·
      refine ⟨8751433331042771582559613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11668577774723695443412817 8751433331042771582559613)
      ·
        refine ⟨3281787499141039343459855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8751433331042771582559613 3281787499141039343459855)
        ·
          refine ⟨4922681248711559015189783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3281787499141039343459855 4922681248711559015189783)
          ·
            refine ⟨7384021873067338522784675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922681248711559015189783 7384021873067338522784675)
            ·
              refine ⟨11076032809601007784177013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384021873067338522784675 11076032809601007784177013)
              ·
                refine ⟨1038378075900094479766595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11076032809601007784177013 1038378075900094479766595)
                ·
                  refine ⟨1557567113850141719649893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038378075900094479766595 1557567113850141719649893)
                  ·
                    refine ⟨292043833846901572434355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557567113850141719649893 292043833846901572434355)
                    ·
                      rfl

theorem cell22_853130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_853130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853130 prefixEnd_853130 := by exact prefixLift 853130
  have htrace : WordTrace (prefixWord ++ tailWord_853130) baseStart_853130 baseEnd_853130 := by
    simpa [prefixWord, tailWord_853130, baseEnd_853130] using wordTrace_append hprefix tailTrace_853130
  have hstable : (prefixWord ++ tailWord_853130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853130).length < 2 ^ (prefixWord ++ tailWord_853130).sum := by decide
  have hdescent : baseEnd_853130 < baseStart_853130 := by decide
  rcases family_descends (prefixWord ++ tailWord_853130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853175 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_853175 : Nat := 118140960795 + 853175 * 2 ^ 59
def prefixEnd_853175 : Nat := 4983230072969 + 3 ^ 40 * 853175 * 2
def baseEnd_853175 : Nat := 292059238266536455059217

theorem tailTrace_853175 : CollatzResearch.WordTrace tailWord_853175 prefixEnd_853175 292059238266536455059217 := by
  unfold tailWord_853175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117848684100160534488979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20745232456066773689659319 31117848684100160534488979)
  ·
    refine ⟨46676773026150240801733469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31117848684100160534488979 46676773026150240801733469)
    ·
      refine ⟨17503789884806340300650051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46676773026150240801733469 17503789884806340300650051)
      ·
        refine ⟨26255684827209510450975077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503789884806340300650051 26255684827209510450975077)
        ·
          refine ⟨4922940905101783209557827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26255684827209510450975077 4922940905101783209557827)
          ·
            refine ⟨7384411357652674814336741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922940905101783209557827 7384411357652674814336741)
            ·
              refine ⟨1384577129559876527688139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7384411357652674814336741 1384577129559876527688139)
              ·
                refine ⟨2076865694339814791532209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384577129559876527688139 2076865694339814791532209)
                ·
                  refine ⟨1557649270754861093649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076865694339814791532209 1557649270754861093649157)
                  ·
                    refine ⟨292059238266536455059217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557649270754861093649157 292059238266536455059217)
                    ·
                      rfl

theorem cell22_853175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_853175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853175 prefixEnd_853175 := by exact prefixLift 853175
  have htrace : WordTrace (prefixWord ++ tailWord_853175) baseStart_853175 baseEnd_853175 := by
    simpa [prefixWord, tailWord_853175, baseEnd_853175] using wordTrace_append hprefix tailTrace_853175
  have hstable : (prefixWord ++ tailWord_853175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853175).length < 2 ^ (prefixWord ++ tailWord_853175).sum := by decide
  have hdescent : baseEnd_853175 < baseStart_853175 := by decide
  rcases family_descends (prefixWord ++ tailWord_853175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853233 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_853233 : Nat := 118140960795 + 853233 * 2 ^ 59
def prefixEnd_853233 : Nat := 4983230072969 + 3 ^ 40 * 853233 * 2
def baseEnd_853233 : Nat := 292079092851843637109039

theorem tailTrace_853233 : CollatzResearch.WordTrace tailWord_853233 prefixEnd_853233 292079092851843637109039 := by
  unfold tailWord_853233
  simp only [CollatzResearch.WordTrace]
  refine ⟨31119964117890036440100353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20746642745260024293400235 31119964117890036440100353)
  ·
    refine ⟨23339973088417527330075265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31119964117890036440100353 23339973088417527330075265)
    ·
      refine ⟨17504979816313145497556449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23339973088417527330075265 17504979816313145497556449)
      ·
        refine ⟨13128734862234859123167337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17504979816313145497556449 13128734862234859123167337)
        ·
          refine ⟨9846551146676144342375503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13128734862234859123167337 9846551146676144342375503)
          ·
            refine ⟨14769826720014216513563255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846551146676144342375503 14769826720014216513563255)
            ·
              refine ⟨22154740080021324770344883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769826720014216513563255 22154740080021324770344883)
              ·
                refine ⟨33232110120031987155517325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22154740080021324770344883 33232110120031987155517325)
                ·
                  refine ⟨12462041295011995183318997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33232110120031987155517325 12462041295011995183318997)
                  ·
                    refine ⟨292079092851843637109039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12462041295011995183318997 292079092851843637109039)
                    ·
                      rfl

theorem cell22_853233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_853233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853233 prefixEnd_853233 := by exact prefixLift 853233
  have htrace : WordTrace (prefixWord ++ tailWord_853233) baseStart_853233 baseEnd_853233 := by
    simpa [prefixWord, tailWord_853233, baseEnd_853233] using wordTrace_append hprefix tailTrace_853233
  have hstable : (prefixWord ++ tailWord_853233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853233).length < 2 ^ (prefixWord ++ tailWord_853233).sum := by decide
  have hdescent : baseEnd_853233 < baseStart_853233 := by decide
  rcases family_descends (prefixWord ++ tailWord_853233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853252 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_853252 : Nat := 118140960795 + 853252 * 2 ^ 59
def prefixEnd_853252 : Nat := 4983230072969 + 3 ^ 40 * 853252 * 2
def baseEnd_853252 : Nat := 97361865646711306961327

theorem tailTrace_853252 : CollatzResearch.WordTrace tailWord_853252 prefixEnd_853252 97361865646711306961327 := by
  unfold tailWord_853252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15560328552410601342521005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20747104736547468456694673 15560328552410601342521005)
  ·
    refine ⟨5835123207153975503445377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15560328552410601342521005 5835123207153975503445377)
    ·
      refine ⟨4376342405365481627584033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5835123207153975503445377 4376342405365481627584033)
      ·
        refine ⟨3282256804024111220688025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4376342405365481627584033 3282256804024111220688025)
        ·
          refine ⟨2461692603018083415516019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3282256804024111220688025 2461692603018083415516019)
          ·
            refine ⟨3692538904527125123274029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461692603018083415516019 3692538904527125123274029)
            ·
              refine ⟨1384702089197671921227761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3692538904527125123274029 1384702089197671921227761)
              ·
                refine ⟨1038526566898253940920821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384702089197671921227761 1038526566898253940920821)
                ·
                  refine ⟨97361865646711306961327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038526566898253940920821 97361865646711306961327)
                  ·
                    rfl

theorem cell22_853252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_853252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853252 prefixEnd_853252 := by exact prefixLift 853252
  have htrace : WordTrace (prefixWord ++ tailWord_853252) baseStart_853252 baseEnd_853252 := by
    simpa [prefixWord, tailWord_853252, baseEnd_853252] using wordTrace_append hprefix tailTrace_853252
  have hstable : (prefixWord ++ tailWord_853252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853252).length < 2 ^ (prefixWord ++ tailWord_853252).sum := by decide
  have hdescent : baseEnd_853252 < baseStart_853252 := by decide
  rcases family_descends (prefixWord ++ tailWord_853252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853312 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 2, 3]
def baseStart_853312 : Nat := 118140960795 + 853312 * 2 ^ 59
def prefixEnd_853312 : Nat := 4983230072969 + 3 ^ 40 * 853312 * 2
def baseEnd_853312 : Nat := 292106136166313764383797

theorem tailTrace_853312 : CollatzResearch.WordTrace tailWord_853312 prefixEnd_853312 292106136166313764383797 := by
  unfold tailWord_853312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15561422742301916466113095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20748563656402555288150793 15561422742301916466113095)
  ·
    refine ⟨23342134113452874699169643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15561422742301916466113095 23342134113452874699169643)
    ·
      refine ⟨35013201170179312048754465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23342134113452874699169643 35013201170179312048754465)
      ·
        refine ⟨26259900877634484036565849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35013201170179312048754465 26259900877634484036565849)
        ·
          refine ⟨19694925658225863027424387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26259900877634484036565849 19694925658225863027424387)
          ·
            refine ⟨29542388487338794541136581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694925658225863027424387 29542388487338794541136581)
            ·
              refine ⟨5539197841376023976463109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29542388487338794541136581 5539197841376023976463109)
              ·
                refine ⟨1038599595258004495586833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5539197841376023976463109 1038599595258004495586833)
                ·
                  refine ⟨778949696443503371690125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1038599595258004495586833 778949696443503371690125)
                  ·
                    refine ⟨292106136166313764383797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 778949696443503371690125 292106136166313764383797)
                    ·
                      rfl

theorem cell22_853312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 3].length) (baseStart_853312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853312 prefixEnd_853312 := by exact prefixLift 853312
  have htrace : WordTrace (prefixWord ++ tailWord_853312) baseStart_853312 baseEnd_853312 := by
    simpa [prefixWord, tailWord_853312, baseEnd_853312] using wordTrace_append hprefix tailTrace_853312
  have hstable : (prefixWord ++ tailWord_853312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853312).length < 2 ^ (prefixWord ++ tailWord_853312).sum := by decide
  have hdescent : baseEnd_853312 < baseStart_853312 := by decide
  rcases family_descends (prefixWord ++ tailWord_853312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853421 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 5]
def baseStart_853421 : Nat := 118140960795 + 853421 * 2 ^ 59
def prefixEnd_853421 : Nat := 4983230072969 + 3 ^ 40 * 853421 * 2
def baseEnd_853421 : Nat := 97381149697957937802821

theorem tailTrace_853421 : CollatzResearch.WordTrace tailWord_853421 prefixEnd_853421 97381149697957937802821 := by
  unfold tailWord_853421
  simp only [CollatzResearch.WordTrace]
  refine ⟨31126821041208944547944117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20751214027472629698629411 31126821041208944547944117)
  ·
    refine ⟨2918139472613338551369761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31126821041208944547944117 2918139472613338551369761)
    ·
      refine ⟨2188604604460003913527321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2918139472613338551369761 2188604604460003913527321)
      ·
        refine ⟨1641453453345002935145491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2188604604460003913527321 1641453453345002935145491)
        ·
          refine ⟨2462180180017504402718237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641453453345002935145491 2462180180017504402718237)
          ·
            refine ⟨923317567506564151019339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2462180180017504402718237 923317567506564151019339)
            ·
              refine ⟨1384976351259846226529009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923317567506564151019339 1384976351259846226529009)
              ·
                refine ⟨1038732263444884669896757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384976351259846226529009 1038732263444884669896757)
                ·
                  refine ⟨97381149697957937802821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038732263444884669896757 97381149697957937802821)
                  ·
                    rfl

theorem cell22_853421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_853421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853421 prefixEnd_853421 := by exact prefixLift 853421
  have htrace : WordTrace (prefixWord ++ tailWord_853421) baseStart_853421 baseEnd_853421 := by
    simpa [prefixWord, tailWord_853421, baseEnd_853421] using wordTrace_append hprefix tailTrace_853421
  have hstable : (prefixWord ++ tailWord_853421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853421).length < 2 ^ (prefixWord ++ tailWord_853421).sum := by decide
  have hdescent : baseEnd_853421 < baseStart_853421 := by decide
  rcases family_descends (prefixWord ++ tailWord_853421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853466 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_853466 : Nat := 118140960795 + 853466 * 2 ^ 59
def prefixEnd_853466 : Nat := 4983230072969 + 3 ^ 40 * 853466 * 2
def baseEnd_853466 : Nat := 97386284504502898677775

theorem tailTrace_853466 : CollatzResearch.WordTrace tailWord_853466 prefixEnd_853466 97386284504502898677775 := by
  unfold tailWord_853466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7782115581511479308333063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20752308217363944822221501 7782115581511479308333063)
  ·
    refine ⟨11673173372267218962499595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7782115581511479308333063 11673173372267218962499595)
    ·
      refine ⟨17509760058400828443749393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11673173372267218962499595 17509760058400828443749393)
      ·
        refine ⟨13132320043800621332812045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17509760058400828443749393 13132320043800621332812045)
        ·
          refine ⟨4924620016425232999804517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13132320043800621332812045 4924620016425232999804517)
          ·
            refine ⟨923366253079731187463347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4924620016425232999804517 923366253079731187463347)
            ·
              refine ⟨1385049379619596781195021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923366253079731187463347 1385049379619596781195021)
              ·
                refine ⟨519393517357348792948133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385049379619596781195021 519393517357348792948133)
                ·
                  refine ⟨97386284504502898677775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519393517357348792948133 97386284504502898677775)
                  ·
                    rfl

theorem cell22_853466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_853466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853466 prefixEnd_853466 := by exact prefixLift 853466
  have htrace : WordTrace (prefixWord ++ tailWord_853466) baseStart_853466 baseEnd_853466 := by
    simpa [prefixWord, tailWord_853466, baseEnd_853466] using wordTrace_append hprefix tailTrace_853466
  have hstable : (prefixWord ++ tailWord_853466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853466).length < 2 ^ (prefixWord ++ tailWord_853466).sum := by decide
  have hdescent : baseEnd_853466 < baseStart_853466 := by decide
  rcases family_descends (prefixWord ++ tailWord_853466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853477 : List Nat := [1, 3, 1, 5, 1, 1, 10]
def baseStart_853477 : Nat := 118140960795 + 853477 * 2 ^ 59
def prefixEnd_853477 : Nat := 4983230072969 + 3 ^ 40 * 853477 * 2
def baseEnd_853477 : Nat := 10820837742159567926233

theorem tailTrace_853477 : CollatzResearch.WordTrace tailWord_853477 prefixEnd_853477 10820837742159567926233 := by
  unfold tailWord_853477
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128863529006066111982685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752575686004044074655123 31128863529006066111982685)
  ·
    refine ⟨11673323823377274791993507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31128863529006066111982685 11673323823377274791993507)
    ·
      refine ⟨17509985735065912187990261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11673323823377274791993507 17509985735065912187990261)
      ·
        refine ⟨1641561162662429267624087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17509985735065912187990261 1641561162662429267624087)
        ·
          refine ⟨2462341743993643901436131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641561162662429267624087 2462341743993643901436131)
          ·
            refine ⟨3693512615990465852154197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462341743993643901436131 3693512615990465852154197)
            ·
              refine ⟨10820837742159567926233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3693512615990465852154197 10820837742159567926233)
              ·
                rfl

theorem cell22_853477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 10].length) (baseStart_853477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853477 prefixEnd_853477 := by exact prefixLift 853477
  have htrace : WordTrace (prefixWord ++ tailWord_853477) baseStart_853477 baseEnd_853477 := by
    simpa [prefixWord, tailWord_853477, baseEnd_853477] using wordTrace_append hprefix tailTrace_853477
  have hstable : (prefixWord ++ tailWord_853477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853477).length < 2 ^ (prefixWord ++ tailWord_853477).sum := by decide
  have hdescent : baseEnd_853477 < baseStart_853477 := by decide
  rcases family_descends (prefixWord ++ tailWord_853477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853479 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_853479 : Nat := 118140960795 + 853479 * 2 ^ 59
def prefixEnd_853479 : Nat := 4983230072969 + 3 ^ 40 * 853479 * 2
def baseEnd_853479 : Nat := 292163303679180995458285

theorem tailTrace_853479 : CollatzResearch.WordTrace tailWord_853479 prefixEnd_853479 292163303679180995458285 := by
  unfold tailWord_853479
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128936474998820453555491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752624316665880302370327 31128936474998820453555491)
  ·
    refine ⟨46693404712498230680333237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31128936474998820453555491 46693404712498230680333237)
    ·
      refine ⟨4377506691796709126281241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46693404712498230680333237 4377506691796709126281241)
      ·
        refine ⟨3283130018847531844710931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377506691796709126281241 3283130018847531844710931)
        ·
          refine ⟨4924695028271297767066397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283130018847531844710931 4924695028271297767066397)
          ·
            refine ⟨1846760635601736662649899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924695028271297767066397 1846760635601736662649899)
            ·
              refine ⟨2770140953402604993974849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846760635601736662649899 2770140953402604993974849)
              ·
                refine ⟨2077605715051953745481137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770140953402604993974849 2077605715051953745481137)
                ·
                  refine ⟨1558204286288965309110853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077605715051953745481137 1558204286288965309110853)
                  ·
                    refine ⟨292163303679180995458285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558204286288965309110853 292163303679180995458285)
                    ·
                      rfl

theorem cell22_853479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_853479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853479 prefixEnd_853479 := by exact prefixLift 853479
  have htrace : WordTrace (prefixWord ++ tailWord_853479) baseStart_853479 baseEnd_853479 := by
    simpa [prefixWord, tailWord_853479, baseEnd_853479] using wordTrace_append hprefix tailTrace_853479
  have hstable : (prefixWord ++ tailWord_853479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853479).length < 2 ^ (prefixWord ++ tailWord_853479).sum := by decide
  have hdescent : baseEnd_853479 < baseStart_853479 := by decide
  rcases family_descends (prefixWord ++ tailWord_853479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853494 : List Nat := [5, 1, 1, 1, 2, 3, 2, 7]
def baseStart_853494 : Nat := 118140960795 + 853494 * 2 ^ 59
def prefixEnd_853494 : Nat := 4983230072969 + 3 ^ 40 * 853494 * 2
def baseEnd_853494 : Nat := 32463159831747328481471

theorem tailTrace_853494 : CollatzResearch.WordTrace tailWord_853494 prefixEnd_853494 32463159831747328481471 := by
  unfold tailWord_853494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945592723121529875959471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20752989046629652010234357 1945592723121529875959471)
  ·
    refine ⟨2918389084682294813939207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945592723121529875959471 2918389084682294813939207)
    ·
      refine ⟨4377583627023442220908811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918389084682294813939207 4377583627023442220908811)
      ·
        refine ⟨6566375440535163331363217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377583627023442220908811 6566375440535163331363217)
        ·
          refine ⟨4924781580401372498522413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6566375440535163331363217 4924781580401372498522413)
          ·
            refine ⟨1846793092650514686945905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924781580401372498522413 1846793092650514686945905)
            ·
              refine ⟨1385094819487886015209429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846793092650514686945905 1385094819487886015209429)
              ·
                refine ⟨32463159831747328481471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1385094819487886015209429 32463159831747328481471)
                ·
                  rfl

theorem cell22_853494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_853494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853494 prefixEnd_853494 := by exact prefixLift 853494
  have htrace : WordTrace (prefixWord ++ tailWord_853494) baseStart_853494 baseEnd_853494 := by
    simpa [prefixWord, tailWord_853494, baseEnd_853494] using wordTrace_append hprefix tailTrace_853494
  have hstable : (prefixWord ++ tailWord_853494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853494).length < 2 ^ (prefixWord ++ tailWord_853494).sum := by decide
  have hdescent : baseEnd_853494 < baseStart_853494 := by decide
  rcases family_descends (prefixWord ++ tailWord_853494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853534 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_853534 : Nat := 118140960795 + 853534 * 2 ^ 59
def prefixEnd_853534 : Nat := 4983230072969 + 3 ^ 40 * 853534 * 2
def baseEnd_853534 : Nat := 97394043767726395111039

theorem tailTrace_853534 : CollatzResearch.WordTrace tailWord_853534 prefixEnd_853534 97394043767726395111039 := by
  unfold tailWord_853534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891367811224945605850957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20753961659866376564538437 3891367811224945605850957)
  ·
    refine ⟨1459262929209354602194109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3891367811224945605850957 1459262929209354602194109)
    ·
      refine ⟨547223598453507975822791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1459262929209354602194109 547223598453507975822791)
      ·
        refine ⟨820835397680261963734187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547223598453507975822791 820835397680261963734187)
        ·
          refine ⟨1231253096520392945601281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820835397680261963734187 1231253096520392945601281)
          ·
            refine ⟨923439822390294709200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231253096520392945601281 923439822390294709200961)
            ·
              refine ⟨692579866792721031900721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923439822390294709200961 692579866792721031900721)
              ·
                refine ⟨519434900094540773925541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692579866792721031900721 519434900094540773925541)
                ·
                  refine ⟨97394043767726395111039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519434900094540773925541 97394043767726395111039)
                  ·
                    rfl

theorem cell22_853534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_853534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853534 prefixEnd_853534 := by exact prefixLift 853534
  have htrace : WordTrace (prefixWord ++ tailWord_853534) baseStart_853534 baseEnd_853534 := by
    simpa [prefixWord, tailWord_853534, baseEnd_853534] using wordTrace_append hprefix tailTrace_853534
  have hstable : (prefixWord ++ tailWord_853534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853534).length < 2 ^ (prefixWord ++ tailWord_853534).sum := by decide
  have hdescent : baseEnd_853534 < baseStart_853534 := by decide
  rcases family_descends (prefixWord ++ tailWord_853534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853567 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 8]
def baseStart_853567 : Nat := 118140960795 + 853567 * 2 ^ 59
def prefixEnd_853567 : Nat := 4983230072969 + 3 ^ 40 * 853567 * 2
def baseEnd_853567 : Nat := 97397809292526033086005

theorem tailTrace_853567 : CollatzResearch.WordTrace tailWord_853567 prefixEnd_853567 97397809292526033086005 := by
  unfold tailWord_853567
  simp only [CollatzResearch.WordTrace]
  refine ⟨31132146098680011482758955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20754764065786674321839303 31132146098680011482758955)
  ·
    refine ⟨46698219148020017224138433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31132146098680011482758955 46698219148020017224138433)
    ·
      refine ⟨35023664361015012918103825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46698219148020017224138433 35023664361015012918103825)
      ·
        refine ⟨26267748270761259688577869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35023664361015012918103825 26267748270761259688577869)
        ·
          refine ⟨9850405601535472383216701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26267748270761259688577869 9850405601535472383216701)
          ·
            refine ⟨3693902100575802143706263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9850405601535472383216701 3693902100575802143706263)
            ·
              refine ⟨5540853150863703215559395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693902100575802143706263 5540853150863703215559395)
              ·
                refine ⟨8311279726295554823339093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5540853150863703215559395 8311279726295554823339093)
                ·
                  refine ⟨97397809292526033086005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8311279726295554823339093 97397809292526033086005)
                  ·
                    rfl

theorem cell22_853567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_853567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853567 prefixEnd_853567 := by exact prefixLift 853567
  have htrace : WordTrace (prefixWord ++ tailWord_853567) baseStart_853567 baseEnd_853567 := by
    simpa [prefixWord, tailWord_853567, baseEnd_853567] using wordTrace_append hprefix tailTrace_853567
  have hstable : (prefixWord ++ tailWord_853567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853567).length < 2 ^ (prefixWord ++ tailWord_853567).sum := by decide
  have hdescent : baseEnd_853567 < baseStart_853567 := by decide
  rcases family_descends (prefixWord ++ tailWord_853567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853569 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_853569 : Nat := 118140960795 + 853569 * 2 ^ 59
def prefixEnd_853569 : Nat := 4983230072969 + 3 ^ 40 * 853569 * 2
def baseEnd_853569 : Nat := 292194112518450760708009

theorem tailTrace_853569 : CollatzResearch.WordTrace tailWord_853569 prefixEnd_853569 292194112518450760708009 := by
  unfold tailWord_853569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31132219044672765824331761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20754812696448510549554507 31132219044672765824331761)
  ·
    refine ⟨23349164283504574368248821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31132219044672765824331761 23349164283504574368248821)
    ·
      refine ⟨2188984151578553847023327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23349164283504574368248821 2188984151578553847023327)
      ·
        refine ⟨3283476227367830770534991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188984151578553847023327 3283476227367830770534991)
        ·
          refine ⟨4925214341051746155802487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283476227367830770534991 4925214341051746155802487)
          ·
            refine ⟨7387821511577619233703731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925214341051746155802487 7387821511577619233703731)
            ·
              refine ⟨11081732267366428850555597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387821511577619233703731 11081732267366428850555597)
              ·
                refine ⟨4155649600262410818958349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11081732267366428850555597 4155649600262410818958349)
                ·
                  refine ⟨1558368600098404057109381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4155649600262410818958349 1558368600098404057109381)
                  ·
                    refine ⟨292194112518450760708009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558368600098404057109381 292194112518450760708009)
                    ·
                      rfl

theorem cell22_853569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_853569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853569 prefixEnd_853569 := by exact prefixLift 853569
  have htrace : WordTrace (prefixWord ++ tailWord_853569) baseStart_853569 baseEnd_853569 := by
    simpa [prefixWord, tailWord_853569, baseEnd_853569] using wordTrace_append hprefix tailTrace_853569
  have hstable : (prefixWord ++ tailWord_853569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853569).length < 2 ^ (prefixWord ++ tailWord_853569).sum := by decide
  have hdescent : baseEnd_853569 < baseStart_853569 := by decide
  rcases family_descends (prefixWord ++ tailWord_853569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853586 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_853586 : Nat := 118140960795 + 853586 * 2 ^ 59
def prefixEnd_853586 : Nat := 4983230072969 + 3 ^ 40 * 853586 * 2
def baseEnd_853586 : Nat := 292199931965868383032957

theorem tailTrace_853586 : CollatzResearch.WordTrace tailWord_853586 prefixEnd_853586 292199931965868383032957 := by
  unfold tailWord_853586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783209771402794431925153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20755226057074118485133741 7783209771402794431925153)
  ·
    refine ⟨5837407328552095823943865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7783209771402794431925153 5837407328552095823943865)
    ·
      refine ⟨4378055496414071867957899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5837407328552095823943865 4378055496414071867957899)
      ·
        refine ⟨6567083244621107801936849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378055496414071867957899 6567083244621107801936849)
        ·
          refine ⟨4925312433465830851452637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6567083244621107801936849 4925312433465830851452637)
          ·
            refine ⟨1846992162549686569294739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4925312433465830851452637 1846992162549686569294739)
            ·
              refine ⟨2770488243824529853942109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846992162549686569294739 2770488243824529853942109)
              ·
                refine ⟨1038933091434198695228291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770488243824529853942109 1038933091434198695228291)
                ·
                  refine ⟨1558399637151298042842437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038933091434198695228291 1558399637151298042842437)
                  ·
                    refine ⟨292199931965868383032957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558399637151298042842437 292199931965868383032957)
                    ·
                      rfl

theorem cell22_853586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_853586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853586 prefixEnd_853586 := by exact prefixLift 853586
  have htrace : WordTrace (prefixWord ++ tailWord_853586) baseStart_853586 baseEnd_853586 := by
    simpa [prefixWord, tailWord_853586, baseEnd_853586] using wordTrace_append hprefix tailTrace_853586
  have hstable : (prefixWord ++ tailWord_853586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853586).length < 2 ^ (prefixWord ++ tailWord_853586).sum := by decide
  have hdescent : baseEnd_853586 < baseStart_853586 := by decide
  rcases family_descends (prefixWord ++ tailWord_853586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853612 : List Nat := [2, 2, 1, 1, 3, 1, 1, 11]
def baseStart_853612 : Nat := 118140960795 + 853612 * 2 ^ 59
def prefixEnd_853612 : Nat := 4983230072969 + 3 ^ 40 * 853612 * 2
def baseEnd_853612 : Nat := 32467648033023664653653

theorem tailTrace_853612 : CollatzResearch.WordTrace tailWord_853612 prefixEnd_853612 32467648033023664653653 := by
  unfold tailWord_853612
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566893691758492084073545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20755858255677989445431393 15566893691758492084073545)
  ·
    refine ⟨11675170268818869063055159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15566893691758492084073545 11675170268818869063055159)
    ·
      refine ⟨17512755403228303594582739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675170268818869063055159 17512755403228303594582739)
      ·
        refine ⟨26269133104842455391874109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17512755403228303594582739 26269133104842455391874109)
        ·
          refine ⟨9850924914315920771952791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26269133104842455391874109 9850924914315920771952791)
          ·
            refine ⟨14776387371473881157929187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850924914315920771952791 14776387371473881157929187)
            ·
              refine ⟨22164581057210821736893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14776387371473881157929187 22164581057210821736893781)
              ·
                refine ⟨32467648033023664653653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22164581057210821736893781 32467648033023664653653)
                ·
                  rfl

theorem cell22_853612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_853612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853612 prefixEnd_853612 := by exact prefixLift 853612
  have htrace : WordTrace (prefixWord ++ tailWord_853612) baseStart_853612 baseEnd_853612 := by
    simpa [prefixWord, tailWord_853612, baseEnd_853612] using wordTrace_append hprefix tailTrace_853612
  have hstable : (prefixWord ++ tailWord_853612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853612).length < 2 ^ (prefixWord ++ tailWord_853612).sum := by decide
  have hdescent : baseEnd_853612 < baseStart_853612 := by decide
  rcases family_descends (prefixWord ++ tailWord_853612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853616 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_853616 : Nat := 118140960795 + 853616 * 2 ^ 59
def prefixEnd_853616 : Nat := 4983230072969 + 3 ^ 40 * 853616 * 2
def baseEnd_853616 : Nat := 292210201578958304782865

theorem tailTrace_853616 : CollatzResearch.WordTrace tailWord_853616 prefixEnd_853616 292210201578958304782865 := by
  unfold tailWord_853616
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566966637751246425646351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20755955517001661900861801 15566966637751246425646351)
  ·
    refine ⟨23350449956626869638469527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15566966637751246425646351 23350449956626869638469527)
    ·
      refine ⟨35025674934940304457704291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23350449956626869638469527 35025674934940304457704291)
      ·
        refine ⟨52538512402410456686556437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35025674934940304457704291 52538512402410456686556437)
        ·
          refine ⟨2462742768862990157182333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52538512402410456686556437 2462742768862990157182333)
          ·
            refine ⟨923528538323621308943375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2462742768862990157182333 923528538323621308943375)
            ·
              refine ⟨1385292807485431963415063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923528538323621308943375 1385292807485431963415063)
              ·
                refine ⟨2077939211228147945122595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385292807485431963415063 2077939211228147945122595)
                ·
                  refine ⟨3116908816842221917683893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077939211228147945122595 3116908816842221917683893)
                  ·
                    refine ⟨292210201578958304782865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3116908816842221917683893 292210201578958304782865)
                    ·
                      rfl

theorem cell22_853616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_853616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853616 prefixEnd_853616 := by exact prefixLift 853616
  have htrace : WordTrace (prefixWord ++ tailWord_853616) baseStart_853616 baseEnd_853616 := by
    simpa [prefixWord, tailWord_853616, baseEnd_853616] using wordTrace_append hprefix tailTrace_853616
  have hstable : (prefixWord ++ tailWord_853616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853616).length < 2 ^ (prefixWord ++ tailWord_853616).sum := by decide
  have hdescent : baseEnd_853616 < baseStart_853616 := by decide
  rcases family_descends (prefixWord ++ tailWord_853616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853627 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_853627 : Nat := 118140960795 + 853627 * 2 ^ 59
def prefixEnd_853627 : Nat := 4983230072969 + 3 ^ 40 * 853627 * 2
def baseEnd_853627 : Nat := 292213967103757942757831

theorem tailTrace_853627 : CollatzResearch.WordTrace tailWord_853627 prefixEnd_853627 292213967103757942757831 := by
  unfold tailWord_853627
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134334478462641729943135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756222985641761153295423 31134334478462641729943135)
  ·
    refine ⟨46701501717693962594914703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31134334478462641729943135 46701501717693962594914703)
    ·
      refine ⟨70052252576540943892372055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46701501717693962594914703 70052252576540943892372055)
      ·
        refine ⟨105078378864811415838558083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70052252576540943892372055 105078378864811415838558083)
        ·
          refine ⟨157617568297217123757837125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105078378864811415838558083 157617568297217123757837125)
          ·
            refine ⟨29553294055728210704594461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157617568297217123757837125 29553294055728210704594461)
            ·
              refine ⟨11082485270898079014222923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29553294055728210704594461 11082485270898079014222923)
              ·
                refine ⟨16623727906347118521334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082485270898079014222923 16623727906347118521334385)
                ·
                  refine ⟨12467795929760338891000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16623727906347118521334385 12467795929760338891000789)
                  ·
                    refine ⟨292213967103757942757831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12467795929760338891000789 292213967103757942757831)
                    ·
                      rfl

theorem cell22_853627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_853627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853627 prefixEnd_853627 := by exact prefixLift 853627
  have htrace : WordTrace (prefixWord ++ tailWord_853627) baseStart_853627 baseEnd_853627 := by
    simpa [prefixWord, tailWord_853627, baseEnd_853627] using wordTrace_append hprefix tailTrace_853627
  have hstable : (prefixWord ++ tailWord_853627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853627).length < 2 ^ (prefixWord ++ tailWord_853627).sum := by decide
  have hdescent : baseEnd_853627 < baseStart_853627 := by decide
  rcases family_descends (prefixWord ++ tailWord_853627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853629 : List Nat := [1, 4, 1, 1, 4, 2, 1, 8]
def baseStart_853629 : Nat := 118140960795 + 853629 * 2 ^ 59
def prefixEnd_853629 : Nat := 4983230072969 + 3 ^ 40 * 853629 * 2
def baseEnd_853629 : Nat := 32468294638292289356425

theorem tailTrace_853629 : CollatzResearch.WordTrace tailWord_853629 prefixEnd_853629 32468294638292289356425 := by
  unfold tailWord_853629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134407424455396071515941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756271616303597381010627 31134407424455396071515941)
  ·
    refine ⟨5837701392085386763409239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31134407424455396071515941 5837701392085386763409239)
    ·
      refine ⟨8756552088128080145113859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837701392085386763409239 8756552088128080145113859)
      ·
        refine ⟨13134828132192120217670789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8756552088128080145113859 13134828132192120217670789)
        ·
          refine ⟨2462780274786022540813273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13134828132192120217670789 2462780274786022540813273)
          ·
            refine ⟨1847085206089516905609955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462780274786022540813273 1847085206089516905609955)
            ·
              refine ⟨2770627809134275358414933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847085206089516905609955 2770627809134275358414933)
              ·
                refine ⟨32468294638292289356425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2770627809134275358414933 32468294638292289356425)
                ·
                  rfl

theorem cell22_853629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 8].length) (baseStart_853629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853629 prefixEnd_853629 := by exact prefixLift 853629
  have htrace : WordTrace (prefixWord ++ tailWord_853629) baseStart_853629 baseEnd_853629 := by
    simpa [prefixWord, tailWord_853629, baseEnd_853629] using wordTrace_append hprefix tailTrace_853629
  have hstable : (prefixWord ++ tailWord_853629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853629).length < 2 ^ (prefixWord ++ tailWord_853629).sum := by decide
  have hdescent : baseEnd_853629 < baseStart_853629 := by decide
  rcases family_descends (prefixWord ++ tailWord_853629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853708 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_853708 : Nat := 118140960795 + 853708 * 2 ^ 59
def prefixEnd_853708 : Nat := 4983230072969 + 3 ^ 40 * 853708 * 2
def baseEnd_853708 : Nat := 97413898353033577160861

theorem tailTrace_853708 : CollatzResearch.WordTrace tailWord_853708 prefixEnd_853708 97413898353033577160861 := by
  unfold tailWord_853708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568644395584596281820889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20758192527446128375761185 15568644395584596281820889)
  ·
    refine ⟨11676483296688447211365667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15568644395584596281820889 11676483296688447211365667)
    ·
      refine ⟨17514724945032670817048501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676483296688447211365667 17514724945032670817048501)
      ·
        refine ⟨1642005463596812889098297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17514724945032670817048501 1642005463596812889098297)
        ·
          refine ⟨1231504097697609666823723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642005463596812889098297 1231504097697609666823723)
          ·
            refine ⟨1847256146546414500235585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231504097697609666823723 1847256146546414500235585)
            ·
              refine ⟨1385442109909810875176689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847256146546414500235585 1385442109909810875176689)
              ·
                refine ⟨1039081582432358156382517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385442109909810875176689 1039081582432358156382517)
                ·
                  refine ⟨97413898353033577160861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039081582432358156382517 97413898353033577160861)
                  ·
                    rfl

theorem cell22_853708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_853708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853708 prefixEnd_853708 := by exact prefixLift 853708
  have htrace : WordTrace (prefixWord ++ tailWord_853708) baseStart_853708 baseEnd_853708 := by
    simpa [prefixWord, tailWord_853708, baseEnd_853708] using wordTrace_append hprefix tailTrace_853708
  have hstable : (prefixWord ++ tailWord_853708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853708).length < 2 ^ (prefixWord ++ tailWord_853708).sum := by decide
  have hdescent : baseEnd_853708 < baseStart_853708 := by decide
  rcases family_descends (prefixWord ++ tailWord_853708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853719 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 6]
def baseStart_853719 : Nat := 118140960795 + 853719 * 2 ^ 59
def prefixEnd_853719 : Nat := 4983230072969 + 3 ^ 40 * 853719 * 2
def baseEnd_853719 : Nat := 97415153527966789819183

theorem tailTrace_853719 : CollatzResearch.WordTrace tailWord_853719 prefixEnd_853719 97415153527966789819183 := by
  unfold tailWord_853719
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137689994129341442292211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20758459996086227628194807 31137689994129341442292211)
  ·
    refine ⟨46706534991194012163438317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137689994129341442292211 46706534991194012163438317)
    ·
      refine ⟨17514950621697754561289369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46706534991194012163438317 17514950621697754561289369)
      ·
        refine ⟨13136212966273315920967027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17514950621697754561289369 13136212966273315920967027)
        ·
          refine ⟨19704319449409973881450541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13136212966273315920967027 19704319449409973881450541)
          ·
            refine ⟨7389119793528740205543953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19704319449409973881450541 7389119793528740205543953)
            ·
              refine ⟨5541839845146555154157965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389119793528740205543953 5541839845146555154157965)
              ·
                refine ⟨2078189941929958182809237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541839845146555154157965 2078189941929958182809237)
                ·
                  refine ⟨97415153527966789819183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2078189941929958182809237 97415153527966789819183)
                  ·
                    rfl

theorem cell22_853719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_853719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853719 prefixEnd_853719 := by exact prefixLift 853719
  have htrace : WordTrace (prefixWord ++ tailWord_853719) baseStart_853719 baseEnd_853719 := by
    simpa [prefixWord, tailWord_853719, baseEnd_853719] using wordTrace_append hprefix tailTrace_853719
  have hstable : (prefixWord ++ tailWord_853719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853719).length < 2 ^ (prefixWord ++ tailWord_853719).sum := by decide
  have hdescent : baseEnd_853719 < baseStart_853719 := by decide
  rcases family_descends (prefixWord ++ tailWord_853719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853736 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_853736 : Nat := 118140960795 + 853736 * 2 ^ 59
def prefixEnd_853736 : Nat := 4983230072969 + 3 ^ 40 * 853736 * 2
def baseEnd_853736 : Nat := 97417093343772663927499

theorem tailTrace_853736 : CollatzResearch.WordTrace tailWord_853736 prefixEnd_853736 97417093343772663927499 := by
  unfold tailWord_853736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569155017533876672830531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20758873356711835563774041 15569155017533876672830531)
  ·
    refine ⟨23353732526300815009245797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15569155017533876672830531 23353732526300815009245797)
    ·
      refine ⟨4378824848681402814233587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23353732526300815009245797 4378824848681402814233587)
      ·
        refine ⟨6568237273022104221350381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378824848681402814233587 6568237273022104221350381)
        ·
          refine ⟨2463088977383289083006393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6568237273022104221350381 2463088977383289083006393)
          ·
            refine ⟨1847316733037466812254795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463088977383289083006393 1847316733037466812254795)
            ·
              refine ⟨2770975099556200218382193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847316733037466812254795 2770975099556200218382193)
              ·
                refine ⟨2078231324667150163786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770975099556200218382193 2078231324667150163786645)
                ·
                  refine ⟨97417093343772663927499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2078231324667150163786645 97417093343772663927499)
                  ·
                    rfl

theorem cell22_853736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_853736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853736 prefixEnd_853736 := by exact prefixLift 853736
  have htrace : WordTrace (prefixWord ++ tailWord_853736) baseStart_853736 baseEnd_853736 := by
    simpa [prefixWord, tailWord_853736, baseEnd_853736] using wordTrace_append hprefix tailTrace_853736
  have hstable : (prefixWord ++ tailWord_853736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853736).length < 2 ^ (prefixWord ++ tailWord_853736).sum := by decide
  have hdescent : baseEnd_853736 < baseStart_853736 := by decide
  rcases family_descends (prefixWord ++ tailWord_853736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853888 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 4]
def baseStart_853888 : Nat := 118140960795 + 853888 * 2 ^ 59
def prefixEnd_853888 : Nat := 4983230072969 + 3 ^ 40 * 853888 * 2
def baseEnd_853888 : Nat := 97434437579213420660677

theorem tailTrace_853888 : CollatzResearch.WordTrace tailWord_853888 prefixEnd_853888 97434437579213420660677 := by
  unfold tailWord_853888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571926965258541652597159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20762569287011388870129545 15571926965258541652597159)
  ·
    refine ⟨23357890447887812478895739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15571926965258541652597159 23357890447887812478895739)
    ·
      refine ⟨35036835671831718718343609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23357890447887812478895739 35036835671831718718343609)
      ·
        refine ⟨26277626753873789038757707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35036835671831718718343609 26277626753873789038757707)
        ·
          refine ⟨39416440130810683558136561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26277626753873789038757707 39416440130810683558136561)
          ·
            refine ⟨29562330098108012668602421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39416440130810683558136561 29562330098108012668602421)
            ·
              refine ⟨2771468446697626187681477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29562330098108012668602421 2771468446697626187681477)
              ·
                refine ⟨519650333755804910190277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2771468446697626187681477 519650333755804910190277)
                ·
                  refine ⟨97434437579213420660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519650333755804910190277 97434437579213420660677)
                  ·
                    rfl

theorem cell22_853888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 4].length) (baseStart_853888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853888 prefixEnd_853888 := by exact prefixLift 853888
  have htrace : WordTrace (prefixWord ++ tailWord_853888) baseStart_853888 baseEnd_853888 := by
    simpa [prefixWord, tailWord_853888, baseEnd_853888] using wordTrace_append hprefix tailTrace_853888
  have hstable : (prefixWord ++ tailWord_853888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853888).length < 2 ^ (prefixWord ++ tailWord_853888).sum := by decide
  have hdescent : baseEnd_853888 < baseStart_853888 := by decide
  rcases family_descends (prefixWord ++ tailWord_853888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853922 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_853922 : Nat := 118140960795 + 853922 * 2 ^ 59
def prefixEnd_853922 : Nat := 4983230072969 + 3 ^ 40 * 853922 * 2
def baseEnd_853922 : Nat := 97438317210825168877309

theorem tailTrace_853922 : CollatzResearch.WordTrace tailWord_853922 prefixEnd_853922 97438317210825168877309 := by
  unfold tailWord_853922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786273503098476777983005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20763396008262604741288013 7786273503098476777983005)
  ·
    refine ⟨2919852563661928791743627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7786273503098476777983005 2919852563661928791743627)
    ·
      refine ⟨4379778845492893187615441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919852563661928791743627 4379778845492893187615441)
      ·
        refine ⟨3284834134119669890711581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4379778845492893187615441 3284834134119669890711581)
        ·
          refine ⟨1231812800294876209016843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3284834134119669890711581 1231812800294876209016843)
          ·
            refine ⟨1847719200442314313525265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231812800294876209016843 1847719200442314313525265)
            ·
              refine ⟨1385789400331735735143949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847719200442314313525265 1385789400331735735143949)
              ·
                refine ⟨519671025124400900678981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385789400331735735143949 519671025124400900678981)
                ·
                  refine ⟨97438317210825168877309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519671025124400900678981 97438317210825168877309)
                  ·
                    rfl

theorem cell22_853922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_853922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853922 prefixEnd_853922 := by exact prefixLift 853922
  have htrace : WordTrace (prefixWord ++ tailWord_853922) baseStart_853922 baseEnd_853922 := by
    simpa [prefixWord, tailWord_853922, baseEnd_853922] using wordTrace_append hprefix tailTrace_853922
  have hstable : (prefixWord ++ tailWord_853922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853922).length < 2 ^ (prefixWord ++ tailWord_853922).sum := by decide
  have hdescent : baseEnd_853922 < baseStart_853922 := by decide
  rcases family_descends (prefixWord ++ tailWord_853922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853937 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_853937 : Nat := 118140960795 + 853937 * 2 ^ 59
def prefixEnd_853937 : Nat := 4983230072969 + 3 ^ 40 * 853937 * 2
def baseEnd_853937 : Nat := 292320086439020467506881

theorem tailTrace_853937 : CollatzResearch.WordTrace tailWord_853937 prefixEnd_853937 292320086439020467506881 := by
  unfold tailWord_853937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31145641107339564673728065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20763760738226376449152043 31145641107339564673728065)
  ·
    refine ⟨23359230830504673505296049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31145641107339564673728065 23359230830504673505296049)
    ·
      refine ⟨17519423122878505128972037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23359230830504673505296049 17519423122878505128972037)
      ·
        refine ⟨3284891835539719711682257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17519423122878505128972037 3284891835539719711682257)
        ·
          refine ⟨2463668876654789783761693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284891835539719711682257 2463668876654789783761693)
          ·
            refine ⟨923875828745546168910635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463668876654789783761693 923875828745546168910635)
            ·
              refine ⟨1385813743118319253365953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923875828745546168910635 1385813743118319253365953)
              ·
                refine ⟨1039360307338739440024465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385813743118319253365953 1039360307338739440024465)
                ·
                  refine ⟨779520230504054580018349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039360307338739440024465 779520230504054580018349)
                  ·
                    refine ⟨292320086439020467506881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779520230504054580018349 292320086439020467506881)
                    ·
                      rfl

theorem cell22_853937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_853937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853937 prefixEnd_853937 := by exact prefixLift 853937
  have htrace : WordTrace (prefixWord ++ tailWord_853937) baseStart_853937 baseEnd_853937 := by
    simpa [prefixWord, tailWord_853937, baseEnd_853937] using wordTrace_append hprefix tailTrace_853937
  have hstable : (prefixWord ++ tailWord_853937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853937).length < 2 ^ (prefixWord ++ tailWord_853937).sum := by decide
  have hdescent : baseEnd_853937 < baseStart_853937 := by decide
  rcases family_descends (prefixWord ++ tailWord_853937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853946 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_853946 : Nat := 118140960795 + 853946 * 2 ^ 59
def prefixEnd_853946 : Nat := 4983230072969 + 3 ^ 40 * 853946 * 2
def baseEnd_853946 : Nat := 292323167322947444031853

theorem tailTrace_853946 : CollatzResearch.WordTrace tailWord_853946 prefixEnd_853946 292323167322947444031853 := by
  unfold tailWord_853946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786492341076739802701423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20763979576204639473870461 7786492341076739802701423)
  ·
    refine ⟨11679738511615109704052135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7786492341076739802701423 11679738511615109704052135)
    ·
      refine ⟨17519607767422664556078203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11679738511615109704052135 17519607767422664556078203)
      ·
        refine ⟨26279411651133996834117305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519607767422664556078203 26279411651133996834117305)
        ·
          refine ⟨19709558738350497625587979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26279411651133996834117305 19709558738350497625587979)
          ·
            refine ⟨29564338107525746438381969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19709558738350497625587979 29564338107525746438381969)
            ·
              refine ⟨22173253580644309828786477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29564338107525746438381969 22173253580644309828786477)
              ·
                refine ⟨8314970092741616185794929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22173253580644309828786477 8314970092741616185794929)
                ·
                  refine ⟨6236227569556212139346197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8314970092741616185794929 6236227569556212139346197)
                  ·
                    refine ⟨292323167322947444031853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6236227569556212139346197 292323167322947444031853)
                    ·
                      rfl

theorem cell22_853946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_853946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_853946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_853946 prefixEnd_853946 := by exact prefixLift 853946
  have htrace : WordTrace (prefixWord ++ tailWord_853946) baseStart_853946 baseEnd_853946 := by
    simpa [prefixWord, tailWord_853946, baseEnd_853946] using wordTrace_append hprefix tailTrace_853946
  have hstable : (prefixWord ++ tailWord_853946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853946).length < 2 ^ (prefixWord ++ tailWord_853946).sum := by decide
  have hdescent : baseEnd_853946 < baseStart_853946 := by decide
  rcases family_descends (prefixWord ++ tailWord_853946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854040 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_854040 : Nat := 118140960795 + 854040 * 2 ^ 59
def prefixEnd_854040 : Nat := 4983230072969 + 3 ^ 40 * 854040 * 2
def baseEnd_854040 : Nat := 97451781814654177393855

theorem tailTrace_854040 : CollatzResearch.WordTrace tailWord_854040 prefixEnd_854040 97451781814654177393855 := by
  unfold tailWord_854040
  simp only [CollatzResearch.WordTrace]
  refine ⟨15574698912983206632363787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20766265217310942176485049 15574698912983206632363787)
  ·
    refine ⟨23362048369474809948545681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15574698912983206632363787 23362048369474809948545681)
    ·
      refine ⟨17521536277106107461409261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23362048369474809948545681 17521536277106107461409261)
      ·
        refine ⟨6570576103914790298028473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17521536277106107461409261 6570576103914790298028473)
        ·
          refine ⟨4927932077936092723521355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6570576103914790298028473 4927932077936092723521355)
          ·
            refine ⟨7391898116904139085282033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927932077936092723521355 7391898116904139085282033)
            ·
              refine ⟨5543923587678104313961525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391898116904139085282033 5543923587678104313961525)
              ·
                refine ⟨519742836344822279433893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5543923587678104313961525 519742836344822279433893)
                ·
                  refine ⟨97451781814654177393855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519742836344822279433893 97451781814654177393855)
                  ·
                    rfl

theorem cell22_854040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_854040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854040 prefixEnd_854040 := by exact prefixLift 854040
  have htrace : WordTrace (prefixWord ++ tailWord_854040) baseStart_854040 baseEnd_854040 := by
    simpa [prefixWord, tailWord_854040, baseEnd_854040] using wordTrace_append hprefix tailTrace_854040
  have hstable : (prefixWord ++ tailWord_854040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854040).length < 2 ^ (prefixWord ++ tailWord_854040).sum := by decide
  have hdescent : baseEnd_854040 < baseStart_854040 := by decide
  rcases family_descends (prefixWord ++ tailWord_854040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854042 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_854042 : Nat := 118140960795 + 854042 * 2 ^ 59
def prefixEnd_854042 : Nat := 4983230072969 + 3 ^ 40 * 854042 * 2
def baseEnd_854042 : Nat := 292356030084835193631559

theorem tailTrace_854042 : CollatzResearch.WordTrace tailWord_854042 prefixEnd_854042 292356030084835193631559 := by
  unfold tailWord_854042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787367692989791901575095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20766313847972778404200253 7787367692989791901575095)
  ·
    refine ⟨11681051539484687852362643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7787367692989791901575095 11681051539484687852362643)
    ·
      refine ⟨17521577309227031778543965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681051539484687852362643 17521577309227031778543965)
      ·
        refine ⟨6570591490960136916953987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17521577309227031778543965 6570591490960136916953987)
        ·
          refine ⟨9855887236440205375430981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570591490960136916953987 9855887236440205375430981)
          ·
            refine ⟨1847978856832538507893309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9855887236440205375430981 1847978856832538507893309)
            ·
              refine ⟨692992071312201940459991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847978856832538507893309 692992071312201940459991)
              ·
                refine ⟨1039488106968302910689987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692992071312201940459991 1039488106968302910689987)
                ·
                  refine ⟨1559232160452454366034981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039488106968302910689987 1559232160452454366034981)
                  ·
                    refine ⟨292356030084835193631559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559232160452454366034981 292356030084835193631559)
                    ·
                      rfl

theorem cell22_854042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_854042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854042 prefixEnd_854042 := by exact prefixLift 854042
  have htrace : WordTrace (prefixWord ++ tailWord_854042) baseStart_854042 baseEnd_854042 := by
    simpa [prefixWord, tailWord_854042, baseEnd_854042] using wordTrace_append hprefix tailTrace_854042
  have hstable : (prefixWord ++ tailWord_854042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854042).length < 2 ^ (prefixWord ++ tailWord_854042).sum := by decide
  have hdescent : baseEnd_854042 < baseStart_854042 := by decide
  rcases family_descends (prefixWord ++ tailWord_854042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854070 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_854070 : Nat := 118140960795 + 854070 * 2 ^ 59
def prefixEnd_854070 : Nat := 4983230072969 + 3 ^ 40 * 854070 * 2
def baseEnd_854070 : Nat := 292365615057052453931473

theorem tailTrace_854070 : CollatzResearch.WordTrace tailWord_854070 prefixEnd_854070 292365615057052453931473 := by
  unfold tailWord_854070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946905750991108024269979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20766994677238485592213109 1946905750991108024269979)
  ·
    refine ⟨2920358626486662036404969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946905750991108024269979 2920358626486662036404969)
    ·
      refine ⟨2190268969864996527303727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2920358626486662036404969 2190268969864996527303727)
      ·
        refine ⟨3285403454797494790955591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190268969864996527303727 3285403454797494790955591)
        ·
          refine ⟨4928105182196242186433387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285403454797494790955591 4928105182196242186433387)
          ·
            refine ⟨7392157773294363279650081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928105182196242186433387 7392157773294363279650081)
            ·
              refine ⟨5544118329970772459737561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7392157773294363279650081 5544118329970772459737561)
              ·
                refine ⟨4158088747478079344803171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5544118329970772459737561 4158088747478079344803171)
                ·
                  refine ⟨6237133121217119017204757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158088747478079344803171 6237133121217119017204757)
                  ·
                    refine ⟨292365615057052453931473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6237133121217119017204757 292365615057052453931473)
                    ·
                      rfl

theorem cell22_854070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_854070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854070 prefixEnd_854070 := by exact prefixLift 854070
  have htrace : WordTrace (prefixWord ++ tailWord_854070) baseStart_854070 baseEnd_854070 := by
    simpa [prefixWord, tailWord_854070, baseEnd_854070] using wordTrace_append hprefix tailTrace_854070
  have hstable : (prefixWord ++ tailWord_854070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854070).length < 2 ^ (prefixWord ++ tailWord_854070).sum := by decide
  have hdescent : baseEnd_854070 < baseStart_854070 := by decide
  rcases family_descends (prefixWord ++ tailWord_854070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854100 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_854100 : Nat := 118140960795 + 854100 * 2 ^ 59
def prefixEnd_854100 : Nat := 4983230072969 + 3 ^ 40 * 854100 * 2
def baseEnd_854100 : Nat := 292375884670142375681381

theorem tailTrace_854100 : CollatzResearch.WordTrace tailWord_854100 prefixEnd_854100 292375884670142375681381 := by
  unfold tailWord_854100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575793102874521755955877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20767724137166029007941169 15575793102874521755955877)
  ·
    refine ⟨2920461206788972829241727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15575793102874521755955877 2920461206788972829241727)
    ·
      refine ⟨4380691810183459243862591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920461206788972829241727 4380691810183459243862591)
      ·
        refine ⟨6571037715275188865793887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380691810183459243862591 6571037715275188865793887)
        ·
          refine ⟨9856556572912783298690831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571037715275188865793887 9856556572912783298690831)
          ·
            refine ⟨14784834859369174948036247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856556572912783298690831 14784834859369174948036247)
            ·
              refine ⟨22177252289053762422054371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784834859369174948036247 22177252289053762422054371)
              ·
                refine ⟨33265878433580643633081557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22177252289053762422054371 33265878433580643633081557)
                ·
                  refine ⟨779669025787046335150349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 33265878433580643633081557 779669025787046335150349)
                  ·
                    refine ⟨292375884670142375681381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779669025787046335150349 292375884670142375681381)
                    ·
                      rfl

theorem cell22_854100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_854100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854100 prefixEnd_854100 := by exact prefixLift 854100
  have htrace : WordTrace (prefixWord ++ tailWord_854100) baseStart_854100 baseEnd_854100 := by
    simpa [prefixWord, tailWord_854100, baseEnd_854100] using wordTrace_append hprefix tailTrace_854100
  have hstable : (prefixWord ++ tailWord_854100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854100).length < 2 ^ (prefixWord ++ tailWord_854100).sum := by decide
  have hdescent : baseEnd_854100 < baseStart_854100 := by decide
  rcases family_descends (prefixWord ++ tailWord_854100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854102 : List Nat := [5, 2, 2, 1, 1, 2, 9]
def baseStart_854102 : Nat := 118140960795 + 854102 * 2 ^ 59
def prefixEnd_854102 : Nat := 4983230072969 + 3 ^ 40 * 854102 * 2
def baseEnd_854102 : Nat := 10828761826333890264125

theorem tailTrace_854102 : CollatzResearch.WordTrace tailWord_854102 prefixEnd_854102 10828761826333890264125 := by
  unfold tailWord_854102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946978696983862365842785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20767772767827865235656373 1946978696983862365842785)
  ·
    refine ⟨1460234022737896774382089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946978696983862365842785 1460234022737896774382089)
    ·
      refine ⟨1095175517053422580786567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460234022737896774382089 1095175517053422580786567)
      ·
        refine ⟨1642763275580133871179851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095175517053422580786567 1642763275580133871179851)
        ·
          refine ⟨2464144913370200806769777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642763275580133871179851 2464144913370200806769777)
          ·
            refine ⟨1848108685027650605077333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464144913370200806769777 1848108685027650605077333)
            ·
              refine ⟨10828761826333890264125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1848108685027650605077333 10828761826333890264125)
              ·
                rfl

theorem cell22_854102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 9].length) (baseStart_854102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854102 prefixEnd_854102 := by exact prefixLift 854102
  have htrace : WordTrace (prefixWord ++ tailWord_854102) baseStart_854102 baseEnd_854102 := by
    simpa [prefixWord, tailWord_854102, baseEnd_854102] using wordTrace_append hprefix tailTrace_854102
  have hstable : (prefixWord ++ tailWord_854102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854102).length < 2 ^ (prefixWord ++ tailWord_854102).sum := by decide
  have hdescent : baseEnd_854102 < baseStart_854102 := by decide
  rcases family_descends (prefixWord ++ tailWord_854102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854117 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_854117 : Nat := 118140960795 + 854117 * 2 ^ 59
def prefixEnd_854117 : Nat := 4983230072969 + 3 ^ 40 * 854117 * 2
def baseEnd_854117 : Nat := 292381704117559998006329

theorem tailTrace_854117 : CollatzResearch.WordTrace tailWord_854117 prefixEnd_854117 292381704117559998006329 := by
  unfold tailWord_854117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31152206246687455415280605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20768137497791636943520403 31152206246687455415280605)
  ·
    refine ⟨11682077342507795780730227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31152206246687455415280605 11682077342507795780730227)
    ·
      refine ⟨17523116013761693671095341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11682077342507795780730227 17523116013761693671095341)
      ·
        refine ⟨6571168505160635126660753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17523116013761693671095341 6571168505160635126660753)
        ·
          refine ⟨4928376378870476344995565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6571168505160635126660753 4928376378870476344995565)
          ·
            refine ⟨1848141142076428629373337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4928376378870476344995565 1848141142076428629373337)
            ·
              refine ⟨1386105856557321472030003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848141142076428629373337 1386105856557321472030003)
              ·
                refine ⟨2079158784835982208045005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386105856557321472030003 2079158784835982208045005)
                ·
                  refine ⟨779684544313493328016877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2079158784835982208045005 779684544313493328016877)
                  ·
                    refine ⟨292381704117559998006329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779684544313493328016877 292381704117559998006329)
                    ·
                      rfl

theorem cell22_854117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_854117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854117 prefixEnd_854117 := by exact prefixLift 854117
  have htrace : WordTrace (prefixWord ++ tailWord_854117) baseStart_854117 baseEnd_854117 := by
    simpa [prefixWord, tailWord_854117, baseEnd_854117] using wordTrace_append hprefix tailTrace_854117
  have hstable : (prefixWord ++ tailWord_854117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854117).length < 2 ^ (prefixWord ++ tailWord_854117).sum := by decide
  have hdescent : baseEnd_854117 < baseStart_854117 := by decide
  rcases family_descends (prefixWord ++ tailWord_854117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854160 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_854160 : Nat := 118140960795 + 854160 * 2 ^ 59
def prefixEnd_854160 : Nat := 4983230072969 + 3 ^ 40 * 854160 * 2
def baseEnd_854160 : Nat := 292396423896322219181197

theorem tailTrace_854160 : CollatzResearch.WordTrace tailWord_854160 prefixEnd_854160 292396423896322219181197 := by
  unfold tailWord_854160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576887292765836879547967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20769183057021115839397289 15576887292765836879547967)
  ·
    refine ⟨23365330939148755319321951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15576887292765836879547967 23365330939148755319321951)
    ·
      refine ⟨35047996408723132978982927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23365330939148755319321951 35047996408723132978982927)
      ·
        refine ⟨52571994613084699468474391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35047996408723132978982927 52571994613084699468474391)
        ·
          refine ⟨78857991919627049202711587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52571994613084699468474391 78857991919627049202711587)
          ·
            refine ⟨118286987879440573804067381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78857991919627049202711587 118286987879440573804067381)
            ·
              refine ⟨11089405113697553794131317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118286987879440573804067381 11089405113697553794131317)
              ·
                refine ⟨1039631729409145668199811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11089405113697553794131317 1039631729409145668199811)
                ·
                  refine ⟨1559447594113718502299717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039631729409145668199811 1559447594113718502299717)
                  ·
                    refine ⟨292396423896322219181197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559447594113718502299717 292396423896322219181197)
                    ·
                      rfl

theorem cell22_854160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_854160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854160 prefixEnd_854160 := by exact prefixLift 854160
  have htrace : WordTrace (prefixWord ++ tailWord_854160) baseStart_854160 baseEnd_854160 := by
    simpa [prefixWord, tailWord_854160, baseEnd_854160] using wordTrace_append hprefix tailTrace_854160
  have hstable : (prefixWord ++ tailWord_854160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854160).length < 2 ^ (prefixWord ++ tailWord_854160).sum := by decide
  have hdescent : baseEnd_854160 < baseStart_854160 := by decide
  rcases family_descends (prefixWord ++ tailWord_854160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854203 : List Nat := [1, 1, 1, 1, 1, 2, 5, 10]
def baseStart_854203 : Nat := 118140960795 + 854203 * 2 ^ 59
def prefixEnd_854203 : Nat := 4983230072969 + 3 ^ 40 * 854203 * 2
def baseEnd_854203 : Nat := 32490127075009382261785

theorem tailTrace_854203 : CollatzResearch.WordTrace tailWord_854203 prefixEnd_854203 32490127075009382261785 := by
  unfold tailWord_854203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31155342924375892102911263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20770228616250594735274175 31155342924375892102911263)
  ·
    refine ⟨46733014386563838154366895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31155342924375892102911263 46733014386563838154366895)
    ·
      refine ⟨70099521579845757231550343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46733014386563838154366895 70099521579845757231550343)
      ·
        refine ⟨105149282369768635847325515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70099521579845757231550343 105149282369768635847325515)
        ·
          refine ⟨157723923554652953770988273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105149282369768635847325515 157723923554652953770988273)
          ·
            refine ⟨118292942665989715328241205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157723923554652953770988273 118292942665989715328241205)
            ·
              refine ⟨11089963374936535812022613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118292942665989715328241205 11089963374936535812022613)
              ·
                refine ⟨32490127075009382261785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11089963374936535812022613 32490127075009382261785)
                ·
                  rfl

theorem cell22_854203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_854203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854203 prefixEnd_854203 := by exact prefixLift 854203
  have htrace : WordTrace (prefixWord ++ tailWord_854203) baseStart_854203 baseEnd_854203 := by
    simpa [prefixWord, tailWord_854203, baseEnd_854203] using wordTrace_append hprefix tailTrace_854203
  have hstable : (prefixWord ++ tailWord_854203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854203).length < 2 ^ (prefixWord ++ tailWord_854203).sum := by decide
  have hdescent : baseEnd_854203 < baseStart_854203 := by decide
  rcases family_descends (prefixWord ++ tailWord_854203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854220 : List Nat := [2, 2, 1, 6, 11]
def baseStart_854220 : Nat := 118140960795 + 854220 * 2 ^ 59
def prefixEnd_854220 : Nat := 4983230072969 + 3 ^ 40 * 854220 * 2
def baseEnd_854220 : Nat := 1203361988158444702391

theorem tailTrace_854220 : CollatzResearch.WordTrace tailWord_854220 prefixEnd_854220 1203361988158444702391 := by
  unfold tailWord_854220
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577981482657152003140057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20770641976876202670853409 15577981482657152003140057)
  ·
    refine ⟨11683486111992864002355043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15577981482657152003140057 11683486111992864002355043)
    ·
      refine ⟨17525229167989296003532565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683486111992864002355043 17525229167989296003532565)
      ·
        refine ⟨821495117249498250165589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17525229167989296003532565 821495117249498250165589)
        ·
          refine ⟨1203361988158444702391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 821495117249498250165589 1203361988158444702391)
          ·
            rfl

theorem cell22_854220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 11].length) (baseStart_854220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854220 prefixEnd_854220 := by exact prefixLift 854220
  have htrace : WordTrace (prefixWord ++ tailWord_854220) baseStart_854220 baseEnd_854220 := by
    simpa [prefixWord, tailWord_854220, baseEnd_854220] using wordTrace_append hprefix tailTrace_854220
  have hstable : (prefixWord ++ tailWord_854220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854220).length < 2 ^ (prefixWord ++ tailWord_854220).sum := by decide
  have hdescent : baseEnd_854220 < baseStart_854220 := by decide
  rcases family_descends (prefixWord ++ tailWord_854220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854222 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_854222 : Nat := 118140960795 + 854222 * 2 ^ 59
def prefixEnd_854222 : Nat := 4983230072969 + 3 ^ 40 * 854222 * 2
def baseEnd_854222 : Nat := 292417647763374724131007

theorem tailTrace_854222 : CollatzResearch.WordTrace tailWord_854222 prefixEnd_854222 292417647763374724131007 := by
  unfold tailWord_854222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894504488913382293481615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20770690607538038898568613 3894504488913382293481615)
  ·
    refine ⟨5841756733370073440222423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894504488913382293481615 5841756733370073440222423)
    ·
      refine ⟨8762635100055110160333635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841756733370073440222423 8762635100055110160333635)
      ·
        refine ⟨13143952650082665240500453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762635100055110160333635 13143952650082665240500453)
        ·
          refine ⟨2464491121890499732593835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13143952650082665240500453 2464491121890499732593835)
          ·
            refine ⟨3696736682835749598890753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464491121890499732593835 3696736682835749598890753)
            ·
              refine ⟨2772552512126812199168065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696736682835749598890753 2772552512126812199168065)
              ·
                refine ⟨2079414384095109149376049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772552512126812199168065 2079414384095109149376049)
                ·
                  refine ⟨1559560788071331862032037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079414384095109149376049 1559560788071331862032037)
                  ·
                    refine ⟨292417647763374724131007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559560788071331862032037 292417647763374724131007)
                    ·
                      rfl

theorem cell22_854222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_854222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854222 prefixEnd_854222 := by exact prefixLift 854222
  have htrace : WordTrace (prefixWord ++ tailWord_854222) baseStart_854222 baseEnd_854222 := by
    simpa [prefixWord, tailWord_854222, baseEnd_854222] using wordTrace_append hprefix tailTrace_854222
  have hstable : (prefixWord ++ tailWord_854222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854222).length < 2 ^ (prefixWord ++ tailWord_854222).sum := by decide
  have hdescent : baseEnd_854222 < baseStart_854222 := by decide
  rcases family_descends (prefixWord ++ tailWord_854222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854226 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_854226 : Nat := 118140960795 + 854226 * 2 ^ 59
def prefixEnd_854226 : Nat := 4983230072969 + 3 ^ 40 * 854226 * 2
def baseEnd_854226 : Nat := 97473005681706682343665

theorem tailTrace_854226 : CollatzResearch.WordTrace tailWord_854226 prefixEnd_854226 97473005681706682343665 := by
  unfold tailWord_854226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789045450823141757749633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20770787868861711353999021 7789045450823141757749633)
  ·
    refine ⟨5841784088117356318312225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7789045450823141757749633 5841784088117356318312225)
    ·
      refine ⟨4381338066088017238734169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5841784088117356318312225 4381338066088017238734169)
      ·
        refine ⟨3286003549566012929050627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4381338066088017238734169 3286003549566012929050627)
        ·
          refine ⟨4929005324349019393575941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286003549566012929050627 4929005324349019393575941)
          ·
            refine ⟨924188498315441136295489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4929005324349019393575941 924188498315441136295489)
            ·
              refine ⟨693141373736580852221617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924188498315441136295489 693141373736580852221617)
              ·
                refine ⟨519856030302435639166213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693141373736580852221617 519856030302435639166213)
                ·
                  refine ⟨97473005681706682343665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519856030302435639166213 97473005681706682343665)
                  ·
                    rfl

theorem cell22_854226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_854226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854226 prefixEnd_854226 := by exact prefixLift 854226
  have htrace : WordTrace (prefixWord ++ tailWord_854226) baseStart_854226 baseEnd_854226 := by
    simpa [prefixWord, tailWord_854226, baseEnd_854226] using wordTrace_append hprefix tailTrace_854226
  have hstable : (prefixWord ++ tailWord_854226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854226).length < 2 ^ (prefixWord ++ tailWord_854226).sum := by decide
  have hdescent : baseEnd_854226 < baseStart_854226 := by decide
  rcases family_descends (prefixWord ++ tailWord_854226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854237 : List Nat := [1, 4, 3, 2, 1, 1, 3, 7]
def baseStart_854237 : Nat := 118140960795 + 854237 * 2 ^ 59
def prefixEnd_854237 : Nat := 4983230072969 + 3 ^ 40 * 854237 * 2
def baseEnd_854237 : Nat := 32491420285546631667329

theorem tailTrace_854237 : CollatzResearch.WordTrace tailWord_854237 prefixEnd_854237 32491420285546631667329 := by
  unfold tailWord_854237
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156583006252715909648965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20771055337501810606432643 31156583006252715909648965)
  ·
    refine ⟨5841859313672384233059181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31156583006252715909648965 5841859313672384233059181)
    ·
      refine ⟨2190697242627144087397193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5841859313672384233059181 2190697242627144087397193)
      ·
        refine ⟨1643022931970358065547895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2190697242627144087397193 1643022931970358065547895)
        ·
          refine ⟨2464534397955537098321843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643022931970358065547895 2464534397955537098321843)
          ·
            refine ⟨3696801596933305647482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464534397955537098321843 3696801596933305647482765)
            ·
              refine ⟨1386300598849989617806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696801596933305647482765 1386300598849989617806037)
              ·
                refine ⟨32491420285546631667329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1386300598849989617806037 32491420285546631667329)
                ·
                  rfl

theorem cell22_854237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 7].length) (baseStart_854237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854237 prefixEnd_854237 := by exact prefixLift 854237
  have htrace : WordTrace (prefixWord ++ tailWord_854237) baseStart_854237 baseEnd_854237 := by
    simpa [prefixWord, tailWord_854237, baseEnd_854237] using wordTrace_append hprefix tailTrace_854237
  have hstable : (prefixWord ++ tailWord_854237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854237).length < 2 ^ (prefixWord ++ tailWord_854237).sum := by decide
  have hdescent : baseEnd_854237 < baseStart_854237 := by decide
  rcases family_descends (prefixWord ++ tailWord_854237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854250 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_854250 : Nat := 118140960795 + 854250 * 2 ^ 59
def prefixEnd_854250 : Nat := 4983230072969 + 3 ^ 40 * 854250 * 2
def baseEnd_854250 : Nat := 292427232735591984430921

theorem tailTrace_854250 : CollatzResearch.WordTrace tailWord_854250 prefixEnd_854250 292427232735591984430921 := by
  unfold tailWord_854250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789264288801404782468051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20771371436803746086581469 7789264288801404782468051)
  ·
    refine ⟨11683896433202107173702077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789264288801404782468051 11683896433202107173702077)
    ·
      refine ⟨4381461162450790190138279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11683896433202107173702077 4381461162450790190138279)
      ·
        refine ⟨6572191743676185285207419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381461162450790190138279 6572191743676185285207419)
        ·
          refine ⟨9858287615514277927811129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572191743676185285207419 9858287615514277927811129)
          ·
            refine ⟨7393715711635708445858347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9858287615514277927811129 7393715711635708445858347)
            ·
              refine ⟨11090573567453562668787521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393715711635708445858347 11090573567453562668787521)
              ·
                refine ⟨8317930175590172001590641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11090573567453562668787521 8317930175590172001590641)
                ·
                  refine ⟨6238447631692629001192981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317930175590172001590641 6238447631692629001192981)
                  ·
                    refine ⟨292427232735591984430921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6238447631692629001192981 292427232735591984430921)
                    ·
                      rfl

theorem cell22_854250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_854250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854250 prefixEnd_854250 := by exact prefixLift 854250
  have htrace : WordTrace (prefixWord ++ tailWord_854250) baseStart_854250 baseEnd_854250 := by
    simpa [prefixWord, tailWord_854250, baseEnd_854250] using wordTrace_append hprefix tailTrace_854250
  have hstable : (prefixWord ++ tailWord_854250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854250).length < 2 ^ (prefixWord ++ tailWord_854250).sum := by decide
  have hdescent : baseEnd_854250 < baseStart_854250 := by decide
  rcases family_descends (prefixWord ++ tailWord_854250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854252 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_854252 : Nat := 118140960795 + 854252 * 2 ^ 59
def prefixEnd_854252 : Nat := 4983230072969 + 3 ^ 40 * 854252 * 2
def baseEnd_854252 : Nat := 292427917376464645880915

theorem tailTrace_854252 : CollatzResearch.WordTrace tailWord_854252 prefixEnd_854252 292427917376464645880915 := by
  unfold tailWord_854252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578565050599186735722505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20771420067465582314296673 15578565050599186735722505)
  ·
    refine ⟨11683923787949390051791879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15578565050599186735722505 11683923787949390051791879)
    ·
      refine ⟨17525885681924085077687819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683923787949390051791879 17525885681924085077687819)
      ·
        refine ⟨26288828522886127616531729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17525885681924085077687819 26288828522886127616531729)
        ·
          refine ⟨19716621392164595712398797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26288828522886127616531729 19716621392164595712398797)
          ·
            refine ⟨7393733022061723392149549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19716621392164595712398797 7393733022061723392149549)
            ·
              refine ⟨2772649883273146272056081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7393733022061723392149549 2772649883273146272056081)
              ·
                refine ⟨2079487412454859704042061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772649883273146272056081 2079487412454859704042061)
                ·
                  refine ⟨779807779670572389015773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2079487412454859704042061 779807779670572389015773)
                  ·
                    refine ⟨292427917376464645880915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779807779670572389015773 292427917376464645880915)
                    ·
                      rfl

theorem cell22_854252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_854252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854252 prefixEnd_854252 := by exact prefixLift 854252
  have htrace : WordTrace (prefixWord ++ tailWord_854252) baseStart_854252 baseEnd_854252 := by
    simpa [prefixWord, tailWord_854252, baseEnd_854252] using wordTrace_append hprefix tailTrace_854252
  have hstable : (prefixWord ++ tailWord_854252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854252).length < 2 ^ (prefixWord ++ tailWord_854252).sum := by decide
  have hdescent : baseEnd_854252 < baseStart_854252 := by decide
  rcases family_descends (prefixWord ++ tailWord_854252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854282 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_854282 : Nat := 118140960795 + 854282 * 2 ^ 59
def prefixEnd_854282 : Nat := 4983230072969 + 3 ^ 40 * 854282 * 2
def baseEnd_854282 : Nat := 97479395663184855876941

theorem tailTrace_854282 : CollatzResearch.WordTrace tailWord_854282 prefixEnd_854282 97479395663184855876941 := by
  unfold tailWord_854282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789556072772422148759275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20772149527393125730024733 7789556072772422148759275)
  ·
    refine ⟨11684334109158633223138913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789556072772422148759275 11684334109158633223138913)
    ·
      refine ⟨8763250581868974917354185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11684334109158633223138913 8763250581868974917354185)
      ·
        refine ⟨6572437936401731188015639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8763250581868974917354185 6572437936401731188015639)
        ·
          refine ⟨9858656904602596782023459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572437936401731188015639 9858656904602596782023459)
          ·
            refine ⟨14787985356903895173035189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858656904602596782023459 14787985356903895173035189)
            ·
              refine ⟨1386373627209740172472049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14787985356903895173035189 1386373627209740172472049)
              ·
                refine ⟨1039780220407305129354037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386373627209740172472049 1039780220407305129354037)
                ·
                  refine ⟨97479395663184855876941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039780220407305129354037 97479395663184855876941)
                  ·
                    rfl

theorem cell22_854282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_854282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854282 prefixEnd_854282 := by exact prefixLift 854282
  have htrace : WordTrace (prefixWord ++ tailWord_854282) baseStart_854282 baseEnd_854282 := by
    simpa [prefixWord, tailWord_854282, baseEnd_854282] using wordTrace_append hprefix tailTrace_854282
  have hstable : (prefixWord ++ tailWord_854282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854282).length < 2 ^ (prefixWord ++ tailWord_854282).sum := by decide
  have hdescent : baseEnd_854282 < baseStart_854282 := by decide
  rcases family_descends (prefixWord ++ tailWord_854282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854329 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_854329 : Nat := 118140960795 + 854329 * 2 ^ 59
def prefixEnd_854329 : Nat := 4983230072969 + 3 ^ 40 * 854329 * 2
def baseEnd_854329 : Nat := 292454276050062111705679

theorem tailTrace_854329 : CollatzResearch.WordTrace tailWord_854329 prefixEnd_854329 292454276050062111705679 := by
  unfold tailWord_854329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159938521919415621998041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20773292347946277081332027 31159938521919415621998041)
  ·
    refine ⟨23369953891439561716498531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31159938521919415621998041 23369953891439561716498531)
    ·
      refine ⟨35054930837159342574747797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23369953891439561716498531 35054930837159342574747797)
      ·
        refine ⟨1643199882991844183191303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35054930837159342574747797 1643199882991844183191303)
        ·
          refine ⟨2464799824487766274786955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643199882991844183191303 2464799824487766274786955)
          ·
            refine ⟨3697199736731649412180433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464799824487766274786955 3697199736731649412180433)
            ·
              refine ⟨2772899802548737059135325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697199736731649412180433 2772899802548737059135325)
              ·
                refine ⟨1039837425955776397175747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2772899802548737059135325 1039837425955776397175747)
                ·
                  refine ⟨1559756138933664595763621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039837425955776397175747 1559756138933664595763621)
                  ·
                    refine ⟨292454276050062111705679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559756138933664595763621 292454276050062111705679)
                    ·
                      rfl

theorem cell22_854329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_854329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854329 prefixEnd_854329 := by exact prefixLift 854329
  have htrace : WordTrace (prefixWord ++ tailWord_854329) baseStart_854329 baseEnd_854329 := by
    simpa [prefixWord, tailWord_854329, baseEnd_854329] using wordTrace_append hprefix tailTrace_854329
  have hstable : (prefixWord ++ tailWord_854329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854329).length < 2 ^ (prefixWord ++ tailWord_854329).sum := by decide
  have hdescent : baseEnd_854329 < baseStart_854329 := by decide
  rcases family_descends (prefixWord ++ tailWord_854329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854359 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 2, 3]
def baseStart_854359 : Nat := 118140960795 + 854359 * 2 ^ 59
def prefixEnd_854359 : Nat := 4983230072969 + 3 ^ 40 * 854359 * 2
def baseEnd_854359 : Nat := 292464545663152033455587

theorem tailTrace_854359 : CollatzResearch.WordTrace tailWord_854359 prefixEnd_854359 292464545663152033455587 := by
  unfold tailWord_854359
  simp only [CollatzResearch.WordTrace]
  refine ⟨31161032711810730745590131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20774021807873820497060087 31161032711810730745590131)
  ·
    refine ⟨46741549067716096118385197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31161032711810730745590131 46741549067716096118385197)
    ·
      refine ⟨17528080900393536044394449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46741549067716096118385197 17528080900393536044394449)
      ·
        refine ⟨13146060675295152033295837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17528080900393536044394449 13146060675295152033295837)
        ·
          refine ⟨4929772753235682012485939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13146060675295152033295837 4929772753235682012485939)
          ·
            refine ⟨7394659129853523018728909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929772753235682012485939 7394659129853523018728909)
            ·
              refine ⟨2772997173695071132023341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7394659129853523018728909 2772997173695071132023341)
              ·
                refine ⟨1039873940135651674508753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2772997173695071132023341 1039873940135651674508753)
                ·
                  refine ⟨779905455101738755881565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039873940135651674508753 779905455101738755881565)
                  ·
                    refine ⟨292464545663152033455587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779905455101738755881565 292464545663152033455587)
                    ·
                      rfl

theorem cell22_854359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_854359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854359 prefixEnd_854359 := by exact prefixLift 854359
  have htrace : WordTrace (prefixWord ++ tailWord_854359) baseStart_854359 baseEnd_854359 := by
    simpa [prefixWord, tailWord_854359, baseEnd_854359] using wordTrace_append hprefix tailTrace_854359
  have hstable : (prefixWord ++ tailWord_854359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854359).length < 2 ^ (prefixWord ++ tailWord_854359).sum := by decide
  have hdescent : baseEnd_854359 < baseStart_854359 := by decide
  rcases family_descends (prefixWord ++ tailWord_854359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854387 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 5, 3]
def baseStart_854387 : Nat := 118140960795 + 854387 * 2 ^ 59
def prefixEnd_854387 : Nat := 4983230072969 + 3 ^ 40 * 854387 * 2
def baseEnd_854387 : Nat := 292474130635369293755501

theorem tailTrace_854387 : CollatzResearch.WordTrace tailWord_854387 prefixEnd_854387 292474130635369293755501 := by
  unfold tailWord_854387
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162053955709291527609415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20774702637139527685072943 31162053955709291527609415)
  ·
    refine ⟨46743080933563937291414123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31162053955709291527609415 46743080933563937291414123)
    ·
      refine ⟨70114621400345905937121185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46743080933563937291414123 70114621400345905937121185)
      ·
        refine ⟨52585966050259429452840889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70114621400345905937121185 52585966050259429452840889)
        ·
          refine ⟨39439474537694572089630667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52585966050259429452840889 39439474537694572089630667)
          ·
            refine ⟨59159211806541858134446001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39439474537694572089630667 59159211806541858134446001)
            ·
              refine ⟨44369408854906393600834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59159211806541858134446001 44369408854906393600834501)
              ·
                refine ⟨8319264160294948800156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44369408854906393600834501 8319264160294948800156469)
                ·
                  refine ⟨779931015027651450014669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8319264160294948800156469 779931015027651450014669)
                  ·
                    refine ⟨292474130635369293755501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779931015027651450014669 292474130635369293755501)
                    ·
                      rfl

theorem cell22_854387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].length) (baseStart_854387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854387 prefixEnd_854387 := by exact prefixLift 854387
  have htrace : WordTrace (prefixWord ++ tailWord_854387) baseStart_854387 baseEnd_854387 := by
    simpa [prefixWord, tailWord_854387, baseEnd_854387] using wordTrace_append hprefix tailTrace_854387
  have hstable : (prefixWord ++ tailWord_854387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854387).length < 2 ^ (prefixWord ++ tailWord_854387).sum := by decide
  have hdescent : baseEnd_854387 < baseStart_854387 := by decide
  rcases family_descends (prefixWord ++ tailWord_854387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854404 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_854404 : Nat := 118140960795 + 854404 * 2 ^ 59
def prefixEnd_854404 : Nat := 4983230072969 + 3 ^ 40 * 854404 * 2
def baseEnd_854404 : Nat := 292479950082786916080449

theorem tailTrace_854404 : CollatzResearch.WordTrace tailWord_854404 prefixEnd_854404 292479950082786916080449 := by
  unfold tailWord_854404
  simp only [CollatzResearch.WordTrace]
  refine ⟨15581336998323851715489133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20775115997765135620652177 15581336998323851715489133)
  ·
    refine ⟨5843001374371444393308425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15581336998323851715489133 5843001374371444393308425)
    ·
      refine ⟨4382251030778583294981319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5843001374371444393308425 4382251030778583294981319)
      ·
        refine ⟨6573376546167874942471979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382251030778583294981319 6573376546167874942471979)
        ·
          refine ⟨9860064819251812413707969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573376546167874942471979 9860064819251812413707969)
          ·
            refine ⟨7395048614438859310280977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9860064819251812413707969 7395048614438859310280977)
            ·
              refine ⟨5546286460829144482710733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395048614438859310280977 5546286460829144482710733)
              ·
                refine ⟨2079857422810929181016525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5546286460829144482710733 2079857422810929181016525)
                ·
                  refine ⟨779946533554098442881197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2079857422810929181016525 779946533554098442881197)
                  ·
                    refine ⟨292479950082786916080449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 779946533554098442881197 292479950082786916080449)
                    ·
                      rfl

theorem cell22_854404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_854404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854404 prefixEnd_854404 := by exact prefixLift 854404
  have htrace : WordTrace (prefixWord ++ tailWord_854404) baseStart_854404 baseEnd_854404 := by
    simpa [prefixWord, tailWord_854404, baseEnd_854404] using wordTrace_append hprefix tailTrace_854404
  have hstable : (prefixWord ++ tailWord_854404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854404).length < 2 ^ (prefixWord ++ tailWord_854404).sum := by decide
  have hdescent : baseEnd_854404 < baseStart_854404 := by decide
  rcases family_descends (prefixWord ++ tailWord_854404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854468 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_854468 : Nat := 118140960795 + 854468 * 2 ^ 59
def prefixEnd_854468 : Nat := 4983230072969 + 3 ^ 40 * 854468 * 2
def baseEnd_854468 : Nat := 97500619530237360826751

theorem tailTrace_854468 : CollatzResearch.WordTrace tailWord_854468 prefixEnd_854468 97500619530237360826751 := by
  unfold tailWord_854468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582504134207921180654029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20776672178943894907538705 15582504134207921180654029)
  ·
    refine ⟨5843439050327970442745261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15582504134207921180654029 5843439050327970442745261)
    ·
      refine ⟨2191289643872988916029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5843439050327970442745261 2191289643872988916029473)
      ·
        refine ⟨1643467232904741687022105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191289643872988916029473 1643467232904741687022105)
        ·
          refine ⟨1232600424678556265266579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643467232904741687022105 1232600424678556265266579)
          ·
            refine ⟨1848900637017834397899869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232600424678556265266579 1848900637017834397899869)
            ·
              refine ⟨693337738881687899212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1848900637017834397899869 693337738881687899212451)
              ·
                refine ⟨1040006608322531848818677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693337738881687899212451 1040006608322531848818677)
                ·
                  refine ⟨97500619530237360826751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040006608322531848818677 97500619530237360826751)
                  ·
                    rfl

theorem cell22_854468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_854468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854468 prefixEnd_854468 := by exact prefixLift 854468
  have htrace : WordTrace (prefixWord ++ tailWord_854468) baseStart_854468 baseEnd_854468 := by
    simpa [prefixWord, tailWord_854468, baseEnd_854468] using wordTrace_append hprefix tailTrace_854468
  have hstable : (prefixWord ++ tailWord_854468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854468).length < 2 ^ (prefixWord ++ tailWord_854468).sum := by decide
  have hdescent : baseEnd_854468 < baseStart_854468 := by decide
  rcases family_descends (prefixWord ++ tailWord_854468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854522 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_854522 : Nat := 118140960795 + 854522 * 2 ^ 59
def prefixEnd_854522 : Nat := 4983230072969 + 3 ^ 40 * 854522 * 2
def baseEnd_854522 : Nat := 292520343894273941630087

theorem tailTrace_854522 : CollatzResearch.WordTrace tailWord_854522 prefixEnd_854522 292520343894273941630087 := by
  unfold tailWord_854522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791744452555052395943455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20777985206813473055849213 7791744452555052395943455)
  ·
    refine ⟨11687616678832578593915183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791744452555052395943455 11687616678832578593915183)
    ·
      refine ⟨17531425018248867890872775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11687616678832578593915183 17531425018248867890872775)
      ·
        refine ⟨26297137527373301836309163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17531425018248867890872775 26297137527373301836309163)
        ·
          refine ⟨39445706291059952754463745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26297137527373301836309163 39445706291059952754463745)
          ·
            refine ⟨29584279718294964565847809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39445706291059952754463745 29584279718294964565847809)
            ·
              refine ⟨22188209788721223424385857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29584279718294964565847809 22188209788721223424385857)
              ·
                refine ⟨16641157341540917568289393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22188209788721223424385857 16641157341540917568289393)
                ·
                  refine ⟨12480868006155688176217045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16641157341540917568289393 12480868006155688176217045)
                  ·
                    refine ⟨292520343894273941630087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12480868006155688176217045 292520343894273941630087)
                    ·
                      rfl

theorem cell22_854522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_854522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854522 prefixEnd_854522 := by exact prefixLift 854522
  have htrace : WordTrace (prefixWord ++ tailWord_854522) baseStart_854522 baseEnd_854522 := by
    simpa [prefixWord, tailWord_854522, baseEnd_854522] using wordTrace_append hprefix tailTrace_854522
  have hstable : (prefixWord ++ tailWord_854522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854522).length < 2 ^ (prefixWord ++ tailWord_854522).sum := by decide
  have hdescent : baseEnd_854522 < baseStart_854522 := by decide
  rcases family_descends (prefixWord ++ tailWord_854522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854537 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_854537 : Nat := 118140960795 + 854537 * 2 ^ 59
def prefixEnd_854537 : Nat := 4983230072969 + 3 ^ 40 * 854537 * 2
def baseEnd_854537 : Nat := 292525478700818902505041

theorem tailTrace_854537 : CollatzResearch.WordTrace tailWord_854537 prefixEnd_854537 292525478700818902505041 := by
  unfold tailWord_854537
  simp only [CollatzResearch.WordTrace]
  refine ⟨31167524905165867145569865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20778349936777244763713243 31167524905165867145569865)
  ·
    refine ⟨23375643678874400359177399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31167524905165867145569865 23375643678874400359177399)
    ·
      refine ⟨35063465518311600538766099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23375643678874400359177399 35063465518311600538766099)
      ·
        refine ⟨52595198277467400808149149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35063465518311600538766099 52595198277467400808149149)
        ·
          refine ⟨19723199354050275303055931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52595198277467400808149149 19723199354050275303055931)
          ·
            refine ⟨29584799031075412954583897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19723199354050275303055931 29584799031075412954583897)
            ·
              refine ⟨22188599273306559715937923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29584799031075412954583897 22188599273306559715937923)
              ·
                refine ⟨33282898909959839573906885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22188599273306559715937923 33282898909959839573906885)
                ·
                  refine ⟨6240543545617469920107541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33282898909959839573906885 6240543545617469920107541)
                  ·
                    refine ⟨292525478700818902505041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6240543545617469920107541 292525478700818902505041)
                    ·
                      rfl

theorem cell22_854537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_854537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854537 prefixEnd_854537 := by exact prefixLift 854537
  have htrace : WordTrace (prefixWord ++ tailWord_854537) baseStart_854537 baseEnd_854537 := by
    simpa [prefixWord, tailWord_854537, baseEnd_854537] using wordTrace_append hprefix tailTrace_854537
  have hstable : (prefixWord ++ tailWord_854537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854537).length < 2 ^ (prefixWord ++ tailWord_854537).sum := by decide
  have hdescent : baseEnd_854537 < baseStart_854537 := by decide
  rcases family_descends (prefixWord ++ tailWord_854537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854584 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_854584 : Nat := 118140960795 + 854584 * 2 ^ 59
def prefixEnd_854584 : Nat := 4983230072969 + 3 ^ 40 * 854584 * 2
def baseEnd_854584 : Nat := 292541567761326446579897

theorem tailTrace_854584 : CollatzResearch.WordTrace tailWord_854584 prefixEnd_854584 292541567761326446579897 := by
  unfold tailWord_854584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584619567997797086265403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20779492757330396115020537 15584619567997797086265403)
  ·
    refine ⟨23376929351996695629398105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15584619567997797086265403 23376929351996695629398105)
    ·
      refine ⟨17532697013997521722048579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23376929351996695629398105 17532697013997521722048579)
      ·
        refine ⟨26299045520996282583072869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17532697013997521722048579 26299045520996282583072869)
        ·
          refine ⟨4931071035186802984326163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26299045520996282583072869 4931071035186802984326163)
          ·
            refine ⟨7396606552780204476489245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931071035186802984326163 7396606552780204476489245)
            ·
              refine ⟨2773727457292576678683467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7396606552780204476489245 2773727457292576678683467)
              ·
                refine ⟨4160591185938865018025201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773727457292576678683467 4160591185938865018025201)
                ·
                  refine ⟨3120443389454148763518901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4160591185938865018025201 3120443389454148763518901)
                  ·
                    refine ⟨292541567761326446579897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3120443389454148763518901 292541567761326446579897)
                    ·
                      rfl

theorem cell22_854584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_854584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854584 prefixEnd_854584 := by exact prefixLift 854584
  have htrace : WordTrace (prefixWord ++ tailWord_854584) baseStart_854584 baseEnd_854584 := by
    simpa [prefixWord, tailWord_854584, baseEnd_854584] using wordTrace_append hprefix tailTrace_854584
  have hstable : (prefixWord ++ tailWord_854584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854584).length < 2 ^ (prefixWord ++ tailWord_854584).sum := by decide
  have hdescent : baseEnd_854584 < baseStart_854584 := by decide
  rcases family_descends (prefixWord ++ tailWord_854584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854590 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_854590 : Nat := 118140960795 + 854590 * 2 ^ 59
def prefixEnd_854590 : Nat := 4983230072969 + 3 ^ 40 * 854590 * 2
def baseEnd_854590 : Nat := 292543621683944430929879

theorem tailTrace_854590 : CollatzResearch.WordTrace tailWord_854590 prefixEnd_854590 292543621683944430929879 := by
  unfold tailWord_854590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896182246746732149656153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20779638649315904798166149 3896182246746732149656153)
  ·
    refine ⟨2922136685060049112242115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3896182246746732149656153 2922136685060049112242115)
    ·
      refine ⟨4383205027590073668363173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922136685060049112242115 4383205027590073668363173)
      ·
        refine ⟨821850942673138812818095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4383205027590073668363173 821850942673138812818095)
        ·
          refine ⟨1232776414009708219227143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821850942673138812818095 1232776414009708219227143)
          ·
            refine ⟨1849164621014562328840715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232776414009708219227143 1849164621014562328840715)
            ·
              refine ⟨2773746931521843493261073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849164621014562328840715 2773746931521843493261073)
              ·
                refine ⟨2080310198641382619945805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773746931521843493261073 2080310198641382619945805)
                ·
                  refine ⟨780116324490518482479677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2080310198641382619945805 780116324490518482479677)
                  ·
                    refine ⟨292543621683944430929879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780116324490518482479677 292543621683944430929879)
                    ·
                      rfl

theorem cell22_854590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_854590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854590 prefixEnd_854590 := by exact prefixLift 854590
  have htrace : WordTrace (prefixWord ++ tailWord_854590) baseStart_854590 baseEnd_854590 := by
    simpa [prefixWord, tailWord_854590, baseEnd_854590] using wordTrace_append hprefix tailTrace_854590
  have hstable : (prefixWord ++ tailWord_854590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854590).length < 2 ^ (prefixWord ++ tailWord_854590).sum := by decide
  have hdescent : baseEnd_854590 < baseStart_854590 := by decide
  rcases family_descends (prefixWord ++ tailWord_854590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854620 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 5]
def baseStart_854620 : Nat := 118140960795 + 854620 * 2 ^ 59
def prefixEnd_854620 : Nat := 4983230072969 + 3 ^ 40 * 854620 * 2
def baseEnd_854620 : Nat := 97517963765678117559929

theorem tailTrace_854620 : CollatzResearch.WordTrace tailWord_854620 prefixEnd_854620 97517963765678117559929 := by
  unfold tailWord_854620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15585276081932586160420657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20780368109243448213894209 15585276081932586160420657)
  ·
    refine ⟨11688957061449439620315493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15585276081932586160420657 11688957061449439620315493)
    ·
      refine ⟨2191679449021769928809155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11688957061449439620315493 2191679449021769928809155)
      ·
        refine ⟨3287519173532654893213733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191679449021769928809155 3287519173532654893213733)
        ·
          refine ⟨616409845037372792477575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3287519173532654893213733 616409845037372792477575)
          ·
            refine ⟨924614767556059188716363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616409845037372792477575 924614767556059188716363)
            ·
              refine ⟨1386922151334088783074545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924614767556059188716363 1386922151334088783074545)
              ·
                refine ⟨1040191613500566587305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386922151334088783074545 1040191613500566587305909)
                ·
                  refine ⟨97517963765678117559929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040191613500566587305909 97517963765678117559929)
                  ·
                    rfl

theorem cell22_854620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_854620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854620 prefixEnd_854620 := by exact prefixLift 854620
  have htrace : WordTrace (prefixWord ++ tailWord_854620) baseStart_854620 baseEnd_854620 := by
    simpa [prefixWord, tailWord_854620, baseEnd_854620] using wordTrace_append hprefix tailTrace_854620
  have hstable : (prefixWord ++ tailWord_854620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854620).length < 2 ^ (prefixWord ++ tailWord_854620).sum := by decide
  have hdescent : baseEnd_854620 < baseStart_854620 := by decide
  rcases family_descends (prefixWord ++ tailWord_854620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854658 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_854658 : Nat := 118140960795 + 854658 * 2 ^ 59
def prefixEnd_854658 : Nat := 4983230072969 + 3 ^ 40 * 854658 * 2
def baseEnd_854658 : Nat := 292566899473614920229671

theorem tailTrace_854658 : CollatzResearch.WordTrace tailWord_854658 prefixEnd_854658 292566899473614920229671 := by
  unfold tailWord_854658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792984534431876202681157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20781292091818336540483085 7792984534431876202681157)
  ·
    refine ⟨1461184600205976788002717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7792984534431876202681157 1461184600205976788002717)
    ·
      refine ⟨547944225077241295501019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1461184600205976788002717 547944225077241295501019)
      ·
        refine ⟨821916337615861943251529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547944225077241295501019 821916337615861943251529)
        ·
          refine ⟨616437253211896457438647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821916337615861943251529 616437253211896457438647)
          ·
            refine ⟨924655879817844686157971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616437253211896457438647 924655879817844686157971)
            ·
              refine ⟨1386983819726767029236957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924655879817844686157971 1386983819726767029236957)
              ·
                refine ⟨520118932397537635963859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386983819726767029236957 520118932397537635963859)
                ·
                  refine ⟨780178398596306453945789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520118932397537635963859 780178398596306453945789)
                  ·
                    refine ⟨292566899473614920229671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780178398596306453945789 292566899473614920229671)
                    ·
                      rfl

theorem cell22_854658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_854658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854658 prefixEnd_854658 := by exact prefixLift 854658
  have htrace : WordTrace (prefixWord ++ tailWord_854658) baseStart_854658 baseEnd_854658 := by
    simpa [prefixWord, tailWord_854658, baseEnd_854658] using wordTrace_append hprefix tailTrace_854658
  have hstable : (prefixWord ++ tailWord_854658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854658).length < 2 ^ (prefixWord ++ tailWord_854658).sum := by decide
  have hdescent : baseEnd_854658 < baseStart_854658 := by decide
  rcases family_descends (prefixWord ++ tailWord_854658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854676 : List Nat := [2, 4, 2, 2, 1, 1, 10]
def baseStart_854676 : Nat := 118140960795 + 854676 * 2 ^ 59
def prefixEnd_854676 : Nat := 4983230072969 + 3 ^ 40 * 854676 * 2
def baseEnd_854676 : Nat := 10836039305239587899245

theorem tailTrace_854676 : CollatzResearch.WordTrace tailWord_854676 prefixEnd_854676 10836039305239587899245 := by
  unfold tailWord_854676
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586297325831146942439941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20781729767774862589919921 15586297325831146942439941)
  ·
    refine ⟨2922430748593340051707489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15586297325831146942439941 2922430748593340051707489)
    ·
      refine ⟨2191823061445005038780617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2922430748593340051707489 2191823061445005038780617)
      ·
        refine ⟨1643867296083753779085463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191823061445005038780617 1643867296083753779085463)
        ·
          refine ⟨2465800944125630668628195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643867296083753779085463 2465800944125630668628195)
          ·
            refine ⟨3698701416188446002942293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465800944125630668628195 3698701416188446002942293)
            ·
              refine ⟨10836039305239587899245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3698701416188446002942293 10836039305239587899245)
              ·
                rfl

theorem cell22_854676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 10].length) (baseStart_854676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854676 prefixEnd_854676 := by exact prefixLift 854676
  have htrace : WordTrace (prefixWord ++ tailWord_854676) baseStart_854676 baseEnd_854676 := by
    simpa [prefixWord, tailWord_854676, baseEnd_854676] using wordTrace_append hprefix tailTrace_854676
  have hstable : (prefixWord ++ tailWord_854676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854676).length < 2 ^ (prefixWord ++ tailWord_854676).sum := by decide
  have hdescent : baseEnd_854676 < baseStart_854676 := by decide
  rcases family_descends (prefixWord ++ tailWord_854676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854682 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_854682 : Nat := 118140960795 + 854682 * 2 ^ 59
def prefixEnd_854682 : Nat := 4983230072969 + 3 ^ 40 * 854682 * 2
def baseEnd_854682 : Nat := 97525038388028952543199

theorem tailTrace_854682 : CollatzResearch.WordTrace tailWord_854682 prefixEnd_854682 97525038388028952543199 := by
  unfold tailWord_854682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793203372410139227399575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20781875659760371273065533 7793203372410139227399575)
  ·
    refine ⟨11689805058615208841099363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793203372410139227399575 11689805058615208841099363)
    ·
      refine ⟨17534707587922813261649045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11689805058615208841099363 17534707587922813261649045)
      ·
        refine ⟨821939418183881871639799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17534707587922813261649045 821939418183881871639799)
        ·
          refine ⟨1232909127275822807459699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821939418183881871639799 1232909127275822807459699)
          ·
            refine ⟨1849363690913734211189549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232909127275822807459699 1849363690913734211189549)
            ·
              refine ⟨693511384092650329196081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1849363690913734211189549 693511384092650329196081)
              ·
                refine ⟨520133538069487746897061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693511384092650329196081 520133538069487746897061)
                ·
                  refine ⟨97525038388028952543199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520133538069487746897061 97525038388028952543199)
                  ·
                    rfl

theorem cell22_854682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_854682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854682 prefixEnd_854682 := by exact prefixLift 854682
  have htrace : WordTrace (prefixWord ++ tailWord_854682) baseStart_854682 baseEnd_854682 := by
    simpa [prefixWord, tailWord_854682, baseEnd_854682] using wordTrace_append hprefix tailTrace_854682
  have hstable : (prefixWord ++ tailWord_854682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854682).length < 2 ^ (prefixWord ++ tailWord_854682).sum := by decide
  have hdescent : baseEnd_854682 < baseStart_854682 := by decide
  rcases family_descends (prefixWord ++ tailWord_854682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854691 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 3, 3]
def baseStart_854691 : Nat := 118140960795 + 854691 * 2 ^ 59
def prefixEnd_854691 : Nat := 4983230072969 + 3 ^ 40 * 854691 * 2
def baseEnd_854691 : Nat := 292578196048013834154569

theorem tailTrace_854691 : CollatzResearch.WordTrace tailWord_854691 prefixEnd_854691 292578196048013834154569 := by
  unfold tailWord_854691
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173141746607951446675927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20782094497738634297783951 31173141746607951446675927)
  ·
    refine ⟨46759712619911927170013891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31173141746607951446675927 46759712619911927170013891)
    ·
      refine ⟨70139568929867890755020837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46759712619911927170013891 70139568929867890755020837)
      ·
        refine ⟨13151169174350229516566407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70139568929867890755020837 13151169174350229516566407)
        ·
          refine ⟨19726753761525344274849611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151169174350229516566407 19726753761525344274849611)
          ·
            refine ⟨29590130642288016412274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19726753761525344274849611 29590130642288016412274417)
            ·
              refine ⟨22192597981716012309205813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29590130642288016412274417 22192597981716012309205813)
              ·
                refine ⟨2080556060785876153988045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22192597981716012309205813 2080556060785876153988045)
                ·
                  refine ⟨780208522794703557745517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2080556060785876153988045 780208522794703557745517)
                  ·
                    refine ⟨292578196048013834154569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780208522794703557745517 292578196048013834154569)
                    ·
                      rfl

theorem cell22_854691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].length) (baseStart_854691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854691 prefixEnd_854691 := by exact prefixLift 854691
  have htrace : WordTrace (prefixWord ++ tailWord_854691) baseStart_854691 baseEnd_854691 := by
    simpa [prefixWord, tailWord_854691, baseEnd_854691] using wordTrace_append hprefix tailTrace_854691
  have hstable : (prefixWord ++ tailWord_854691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854691).length < 2 ^ (prefixWord ++ tailWord_854691).sum := by decide
  have hdescent : baseEnd_854691 < baseStart_854691 := by decide
  rcases family_descends (prefixWord ++ tailWord_854691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854751 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_854751 : Nat := 118140960795 + 854751 * 2 ^ 59
def prefixEnd_854751 : Nat := 4983230072969 + 3 ^ 40 * 854751 * 2
def baseEnd_854751 : Nat := 292598735274193677654385

theorem tailTrace_854751 : CollatzResearch.WordTrace tailWord_854751 prefixEnd_854751 292598735274193677654385 := by
  unfold tailWord_854751
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175330126390581693860107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20783553417593721129240071 31175330126390581693860107)
  ·
    refine ⟨46762995189585872540790161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175330126390581693860107 46762995189585872540790161)
    ·
      refine ⟨35072246392189404405592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46762995189585872540790161 35072246392189404405592621)
      ·
        refine ⟨13152092397071026652097233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35072246392189404405592621 13152092397071026652097233)
        ·
          refine ⟨9864069297803269989072925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13152092397071026652097233 9864069297803269989072925)
          ·
            refine ⟨3699025986676226245902347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9864069297803269989072925 3699025986676226245902347)
            ·
              refine ⟨5548538980014339368853521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699025986676226245902347 5548538980014339368853521)
              ·
                refine ⟨4161404235010754526640141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548538980014339368853521 4161404235010754526640141)
                ·
                  refine ⟨1560526588129032947490053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4161404235010754526640141 1560526588129032947490053)
                  ·
                    refine ⟨292598735274193677654385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1560526588129032947490053 292598735274193677654385)
                    ·
                      rfl

theorem cell22_854751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_854751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854751 prefixEnd_854751 := by exact prefixLift 854751
  have htrace : WordTrace (prefixWord ++ tailWord_854751) baseStart_854751 baseEnd_854751 := by
    simpa [prefixWord, tailWord_854751, baseEnd_854751] using wordTrace_append hprefix tailTrace_854751
  have hstable : (prefixWord ++ tailWord_854751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854751).length < 2 ^ (prefixWord ++ tailWord_854751).sum := by decide
  have hdescent : baseEnd_854751 < baseStart_854751 := by decide
  rcases family_descends (prefixWord ++ tailWord_854751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854766 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_854766 : Nat := 118140960795 + 854766 * 2 ^ 59
def prefixEnd_854766 : Nat := 4983230072969 + 3 ^ 40 * 854766 * 2
def baseEnd_854766 : Nat := 97534623360246212843113

theorem tailTrace_854766 : CollatzResearch.WordTrace tailWord_854766 prefixEnd_854766 97534623360246212843113 := by
  unfold tailWord_854766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896984652667029906957019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20783918147557492837104101 3896984652667029906957019)
  ·
    refine ⟨5845476979000544860435529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3896984652667029906957019 5845476979000544860435529)
    ·
      refine ⟨4384107734250408645326647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5845476979000544860435529 4384107734250408645326647)
      ·
        refine ⟨6576161601375612967989971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384107734250408645326647 6576161601375612967989971)
        ·
          refine ⟨9864242402063419451984957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576161601375612967989971 9864242402063419451984957)
          ·
            refine ⟨3699090900773782294494359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9864242402063419451984957 3699090900773782294494359)
            ·
              refine ⟨5548636351160673441741539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699090900773782294494359 5548636351160673441741539)
              ·
                refine ⟨8322954526741010162612309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548636351160673441741539 8322954526741010162612309)
                ·
                  refine ⟨97534623360246212843113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8322954526741010162612309 97534623360246212843113)
                  ·
                    rfl

theorem cell22_854766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_854766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854766 prefixEnd_854766 := by exact prefixLift 854766
  have htrace : WordTrace (prefixWord ++ tailWord_854766) baseStart_854766 baseEnd_854766 := by
    simpa [prefixWord, tailWord_854766, baseEnd_854766] using wordTrace_append hprefix tailTrace_854766
  have hstable : (prefixWord ++ tailWord_854766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854766).length < 2 ^ (prefixWord ++ tailWord_854766).sum := by decide
  have hdescent : baseEnd_854766 < baseStart_854766 := by decide
  rcases family_descends (prefixWord ++ tailWord_854766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854781 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_854781 : Nat := 118140960795 + 854781 * 2 ^ 59
def prefixEnd_854781 : Nat := 4983230072969 + 3 ^ 40 * 854781 * 2
def baseEnd_854781 : Nat := 292609004887283599404293

theorem tailTrace_854781 : CollatzResearch.WordTrace tailWord_854781 prefixEnd_854781 292609004887283599404293 := by
  unfold tailWord_854781
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176424316281896817452197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20784282877521264544968131 31176424316281896817452197)
  ·
    refine ⟨5845579559302855653272287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31176424316281896817452197 5845579559302855653272287)
    ·
      refine ⟨8768369338954283479908431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845579559302855653272287 8768369338954283479908431)
      ·
        refine ⟨13152554008431425219862647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8768369338954283479908431 13152554008431425219862647)
        ·
          refine ⟨19728831012647137829793971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13152554008431425219862647 19728831012647137829793971)
          ·
            refine ⟨29593246518970706744690957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19728831012647137829793971 29593246518970706744690957)
            ·
              refine ⟨11097467444614015029259109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29593246518970706744690957 11097467444614015029259109)
              ·
                refine ⟨2080775145865127817986083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11097467444614015029259109 2080775145865127817986083)
                ·
                  refine ⟨3121162718797691726979125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080775145865127817986083 3121162718797691726979125)
                  ·
                    refine ⟨292609004887283599404293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3121162718797691726979125 292609004887283599404293)
                    ·
                      rfl

theorem cell22_854781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_854781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854781 prefixEnd_854781 := by exact prefixLift 854781
  have htrace : WordTrace (prefixWord ++ tailWord_854781) baseStart_854781 baseEnd_854781 := by
    simpa [prefixWord, tailWord_854781, baseEnd_854781] using wordTrace_append hprefix tailTrace_854781
  have hstable : (prefixWord ++ tailWord_854781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854781).length < 2 ^ (prefixWord ++ tailWord_854781).sum := by decide
  have hdescent : baseEnd_854781 < baseStart_854781 := by decide
  rcases family_descends (prefixWord ++ tailWord_854781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854796 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_854796 : Nat := 118140960795 + 854796 * 2 ^ 59
def prefixEnd_854796 : Nat := 4983230072969 + 3 ^ 40 * 854796 * 2
def baseEnd_854796 : Nat := 292614139693828560279247

theorem tailTrace_854796 : CollatzResearch.WordTrace tailWord_854796 prefixEnd_854796 292614139693828560279247 := by
  unfold tailWord_854796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588485705613777189624121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20784647607485036252832161 15588485705613777189624121)
  ·
    refine ⟨11691364279210332892218091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15588485705613777189624121 11691364279210332892218091)
    ·
      refine ⟨17537046418815499338327137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691364279210332892218091 17537046418815499338327137)
      ·
        refine ⟨13152784814111624503745353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17537046418815499338327137 13152784814111624503745353)
        ·
          refine ⟨9864588610583718377809015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13152784814111624503745353 9864588610583718377809015)
          ·
            refine ⟨14796882915875577566713523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864588610583718377809015 14796882915875577566713523)
            ·
              refine ⟨22195324373813366350070285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796882915875577566713523 22195324373813366350070285)
              ·
                refine ⟨8323246640180012381276357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22195324373813366350070285 8323246640180012381276357)
                ·
                  refine ⟨1560608745033752321489317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8323246640180012381276357 1560608745033752321489317)
                  ·
                    refine ⟨292614139693828560279247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1560608745033752321489317 292614139693828560279247)
                    ·
                      rfl

theorem cell22_854796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_854796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854796 prefixEnd_854796 := by exact prefixLift 854796
  have htrace : WordTrace (prefixWord ++ tailWord_854796) baseStart_854796 baseEnd_854796 := by
    simpa [prefixWord, tailWord_854796, baseEnd_854796] using wordTrace_append hprefix tailTrace_854796
  have hstable : (prefixWord ++ tailWord_854796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854796).length < 2 ^ (prefixWord ++ tailWord_854796).sum := by decide
  have hdescent : baseEnd_854796 < baseStart_854796 := by decide
  rcases family_descends (prefixWord ++ tailWord_854796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854845 : List Nat := [1, 4, 1, 4, 3, 1, 8]
def baseStart_854845 : Nat := 118140960795 + 854845 * 2 ^ 59
def prefixEnd_854845 : Nat := 4983230072969 + 3 ^ 40 * 854845 * 2
def baseEnd_854845 : Nat := 10838181977600324659411

theorem tailTrace_854845 : CollatzResearch.WordTrace tailWord_854845 prefixEnd_854845 10838181977600324659411 := by
  unfold tailWord_854845
  simp only [CollatzResearch.WordTrace]
  refine ⟨31178758588050035747781989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20785839058700023831854659 31178758588050035747781989)
  ·
    refine ⟨5846017235259381702709123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31178758588050035747781989 5846017235259381702709123)
    ·
      refine ⟨8769025852889072554063685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846017235259381702709123 8769025852889072554063685)
      ·
        refine ⟨1644192347416701103886941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8769025852889072554063685 1644192347416701103886941)
        ·
          refine ⟨616572130281262913957603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1644192347416701103886941 616572130281262913957603)
          ·
            refine ⟨924858195421894370936405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616572130281262913957603 924858195421894370936405)
            ·
              refine ⟨10838181977600324659411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 924858195421894370936405 10838181977600324659411)
              ·
                rfl

theorem cell22_854845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 8].length) (baseStart_854845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854845 prefixEnd_854845 := by exact prefixLift 854845
  have htrace : WordTrace (prefixWord ++ tailWord_854845) baseStart_854845 baseEnd_854845 := by
    simpa [prefixWord, tailWord_854845, baseEnd_854845] using wordTrace_append hprefix tailTrace_854845
  have hstable : (prefixWord ++ tailWord_854845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854845).length < 2 ^ (prefixWord ++ tailWord_854845).sum := by decide
  have hdescent : baseEnd_854845 < baseStart_854845 := by decide
  rcases family_descends (prefixWord ++ tailWord_854845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854856 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_854856 : Nat := 118140960795 + 854856 * 2 ^ 59
def prefixEnd_854856 : Nat := 4983230072969 + 3 ^ 40 * 854856 * 2
def baseEnd_854856 : Nat := 97544892973336134593021

theorem tailTrace_854856 : CollatzResearch.WordTrace tailWord_854856 prefixEnd_854856 97544892973336134593021 := by
  unfold tailWord_854856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589579895505092313216211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20786106527340123084288281 15589579895505092313216211)
  ·
    refine ⟨23384369843257638469824317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15589579895505092313216211 23384369843257638469824317)
    ·
      refine ⟨8769138691221614426184119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23384369843257638469824317 8769138691221614426184119)
      ·
        refine ⟨13153708036832421639276179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769138691221614426184119 13153708036832421639276179)
        ·
          refine ⟨19730562055248632458914269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153708036832421639276179 19730562055248632458914269)
          ·
            refine ⟨7398960770718237172092851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19730562055248632458914269 7398960770718237172092851)
            ·
              refine ⟨11098441156077355758139277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398960770718237172092851 11098441156077355758139277)
              ·
                refine ⟨4161915433529008409302229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11098441156077355758139277 4161915433529008409302229)
                ·
                  refine ⟨97544892973336134593021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4161915433529008409302229 97544892973336134593021)
                  ·
                    rfl

theorem cell22_854856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_854856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854856 prefixEnd_854856 := by exact prefixLift 854856
  have htrace : WordTrace (prefixWord ++ tailWord_854856) baseStart_854856 baseEnd_854856 := by
    simpa [prefixWord, tailWord_854856, baseEnd_854856] using wordTrace_append hprefix tailTrace_854856
  have hstable : (prefixWord ++ tailWord_854856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854856).length < 2 ^ (prefixWord ++ tailWord_854856).sum := by decide
  have hdescent : baseEnd_854856 < baseStart_854856 := by decide
  rcases family_descends (prefixWord ++ tailWord_854856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854860 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_854860 : Nat := 118140960795 + 854860 * 2 ^ 59
def prefixEnd_854860 : Nat := 4983230072969 + 3 ^ 40 * 854860 * 2
def baseEnd_854860 : Nat := 292636048201753726679051

theorem tailTrace_854860 : CollatzResearch.WordTrace tailWord_854860 prefixEnd_854860 292636048201753726679051 := by
  unfold tailWord_854860
  simp only [CollatzResearch.WordTrace]
  refine ⟨15589652841497846654789017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20786203788663795539718689 15589652841497846654789017)
  ·
    refine ⟨11692239631123384991091763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15589652841497846654789017 11692239631123384991091763)
    ·
      refine ⟨17538359446685077486637645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11692239631123384991091763 17538359446685077486637645)
      ·
        refine ⟨6576884792506904057489117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17538359446685077486637645 6576884792506904057489117)
        ·
          refine ⟨2466331797190089021558419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6576884792506904057489117 2466331797190089021558419)
          ·
            refine ⟨3699497695785133532337629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466331797190089021558419 3699497695785133532337629)
            ·
              refine ⟨1387311635919425074626611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699497695785133532337629 1387311635919425074626611)
              ·
                refine ⟨2080967453879137611939917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387311635919425074626611 2080967453879137611939917)
                ·
                  refine ⟨780362795204676604477469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2080967453879137611939917 780362795204676604477469)
                  ·
                    refine ⟨292636048201753726679051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780362795204676604477469 292636048201753726679051)
                    ·
                      rfl

theorem cell22_854860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_854860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854860 prefixEnd_854860 := by exact prefixLift 854860
  have htrace : WordTrace (prefixWord ++ tailWord_854860) baseStart_854860 baseEnd_854860 := by
    simpa [prefixWord, tailWord_854860, baseEnd_854860] using wordTrace_append hprefix tailTrace_854860
  have hstable : (prefixWord ++ tailWord_854860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854860).length < 2 ^ (prefixWord ++ tailWord_854860).sum := by decide
  have hdescent : baseEnd_854860 < baseStart_854860 := by decide
  rcases family_descends (prefixWord ++ tailWord_854860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854873 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 5]
def baseStart_854873 : Nat := 118140960795 + 854873 * 2 ^ 59
def prefixEnd_854873 : Nat := 4983230072969 + 3 ^ 40 * 854873 * 2
def baseEnd_854873 : Nat := 97546832789142008701337

theorem tailTrace_854873 : CollatzResearch.WordTrace tailWord_854873 prefixEnd_854873 97546832789142008701337 := by
  unfold tailWord_854873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179779831948596529801273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20786519887965731019867515 31179779831948596529801273)
  ·
    refine ⟨23384834873961447397350955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31179779831948596529801273 23384834873961447397350955)
    ·
      refine ⟨35077252310942171096026433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23384834873961447397350955 35077252310942171096026433)
      ·
        refine ⟨26307939233206628322019825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35077252310942171096026433 26307939233206628322019825)
        ·
          refine ⟨19730954424904971241514869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26307939233206628322019825 19730954424904971241514869)
          ·
            refine ⟨1849776977334841053892019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19730954424904971241514869 1849776977334841053892019)
            ·
              refine ⟨2774665466002261580838029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849776977334841053892019 2774665466002261580838029)
              ·
                refine ⟨1040499549750848092814261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2774665466002261580838029 1040499549750848092814261)
                ·
                  refine ⟨97546832789142008701337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040499549750848092814261 97546832789142008701337)
                  ·
                    rfl

theorem cell22_854873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_854873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854873 prefixEnd_854873 := by exact prefixLift 854873
  have htrace : WordTrace (prefixWord ++ tailWord_854873) baseStart_854873 baseEnd_854873 := by
    simpa [prefixWord, tailWord_854873, baseEnd_854873] using wordTrace_append hprefix tailTrace_854873
  have hstable : (prefixWord ++ tailWord_854873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854873).length < 2 ^ (prefixWord ++ tailWord_854873).sum := by decide
  have hdescent : baseEnd_854873 < baseStart_854873 := by decide
  rcases family_descends (prefixWord ++ tailWord_854873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854903 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 1, 4]
def baseStart_854903 : Nat := 118140960795 + 854903 * 2 ^ 59
def prefixEnd_854903 : Nat := 4983230072969 + 3 ^ 40 * 854903 * 2
def baseEnd_854903 : Nat := 292650767980515947853919

theorem tailTrace_854903 : CollatzResearch.WordTrace tailWord_854903 prefixEnd_854903 292650767980515947853919 := by
  unfold tailWord_854903
  simp only [CollatzResearch.WordTrace]
  refine ⟨31180874021839911653393363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20787249347893274435595575 31180874021839911653393363)
  ·
    refine ⟨46771311032759867480090045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31180874021839911653393363 46771311032759867480090045)
    ·
      refine ⟨17539241637284950305033767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46771311032759867480090045 17539241637284950305033767)
      ·
        refine ⟨26308862455927425457550651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17539241637284950305033767 26308862455927425457550651)
        ·
          refine ⟨39463293683891138186325977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26308862455927425457550651 39463293683891138186325977)
          ·
            refine ⟨29597470262918353639744483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39463293683891138186325977 29597470262918353639744483)
            ·
              refine ⟨44396205394377530459616725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29597470262918353639744483 44396205394377530459616725)
              ·
                refine ⟨1040536063930723370147267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44396205394377530459616725 1040536063930723370147267)
                ·
                  refine ⟨1560804095896085055220901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040536063930723370147267 1560804095896085055220901)
                  ·
                    refine ⟨292650767980515947853919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1560804095896085055220901 292650767980515947853919)
                    ·
                      rfl

theorem cell22_854903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_854903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854903 prefixEnd_854903 := by exact prefixLift 854903
  have htrace : WordTrace (prefixWord ++ tailWord_854903) baseStart_854903 baseEnd_854903 := by
    simpa [prefixWord, tailWord_854903, baseEnd_854903] using wordTrace_append hprefix tailTrace_854903
  have hstable : (prefixWord ++ tailWord_854903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854903).length < 2 ^ (prefixWord ++ tailWord_854903).sum := by decide
  have hdescent : baseEnd_854903 < baseStart_854903 := by decide
  rcases family_descends (prefixWord ++ tailWord_854903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854933 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_854933 : Nat := 118140960795 + 854933 * 2 ^ 59
def prefixEnd_854933 : Nat := 4983230072969 + 3 ^ 40 * 854933 * 2
def baseEnd_854933 : Nat := 292661037593605869603827

theorem tailTrace_854933 : CollatzResearch.WordTrace tailWord_854933 prefixEnd_854933 292661037593605869603827 := by
  unfold tailWord_854933
  simp only [CollatzResearch.WordTrace]
  refine ⟨31181968211731226776985453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20787978807820817851323635 31181968211731226776985453)
  ·
    refine ⟨11693238079399210041369545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31181968211731226776985453 11693238079399210041369545)
    ·
      refine ⟨8769928559549407531027159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11693238079399210041369545 8769928559549407531027159)
      ·
        refine ⟨13154892839324111296540739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769928559549407531027159 13154892839324111296540739)
        ·
          refine ⟨19732339258986166944811109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13154892839324111296540739 19732339258986166944811109)
          ·
            refine ⟨3699813611059906302152083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19732339258986166944811109 3699813611059906302152083)
            ·
              refine ⟨5549720416589859453228125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699813611059906302152083 5549720416589859453228125)
              ·
                refine ⟨2081145156221197294960547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5549720416589859453228125 2081145156221197294960547)
                ·
                  refine ⟨3121717734331795942440821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081145156221197294960547 3121717734331795942440821)
                  ·
                    refine ⟨292661037593605869603827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3121717734331795942440821 292661037593605869603827)
                    ·
                      rfl

theorem cell22_854933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_854933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854933 prefixEnd_854933 := by exact prefixLift 854933
  have htrace : WordTrace (prefixWord ++ tailWord_854933) baseStart_854933 baseEnd_854933 := by
    simpa [prefixWord, tailWord_854933, baseEnd_854933] using wordTrace_append hprefix tailTrace_854933
  have hstable : (prefixWord ++ tailWord_854933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854933).length < 2 ^ (prefixWord ++ tailWord_854933).sum := by decide
  have hdescent : baseEnd_854933 < baseStart_854933 := by decide
  rcases family_descends (prefixWord ++ tailWord_854933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854948 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_854948 : Nat := 118140960795 + 854948 * 2 ^ 59
def prefixEnd_854948 : Nat := 4983230072969 + 3 ^ 40 * 854948 * 2
def baseEnd_854948 : Nat := 292666172400150830478781

theorem tailTrace_854948 : CollatzResearch.WordTrace tailWord_854948 prefixEnd_854948 292666172400150830478781 := by
  unfold tailWord_854948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591257653338442169390749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20788343537784589559187665 15591257653338442169390749)
  ·
    refine ⟨5846721620001915813521531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15591257653338442169390749 5846721620001915813521531)
    ·
      refine ⟨8770082430002873720282297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846721620001915813521531 8770082430002873720282297)
      ·
        refine ⟨6577561822502155290211723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770082430002873720282297 6577561822502155290211723)
        ·
          refine ⟨9866342733753232935317585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577561822502155290211723 9866342733753232935317585)
          ·
            refine ⟨7399757050314924701488189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866342733753232935317585 7399757050314924701488189)
            ·
              refine ⟨2774908893868096763058071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7399757050314924701488189 2774908893868096763058071)
              ·
                refine ⟨4162363340802145144587107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774908893868096763058071 4162363340802145144587107)
                ·
                  refine ⟨6243545011203217716880661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162363340802145144587107 6243545011203217716880661)
                  ·
                    refine ⟨292666172400150830478781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6243545011203217716880661 292666172400150830478781)
                    ·
                      rfl

theorem cell22_854948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_854948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854948 prefixEnd_854948 := by exact prefixLift 854948
  have htrace : WordTrace (prefixWord ++ tailWord_854948) baseStart_854948 baseEnd_854948 := by
    simpa [prefixWord, tailWord_854948, baseEnd_854948] using wordTrace_append hprefix tailTrace_854948
  have hstable : (prefixWord ++ tailWord_854948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854948).length < 2 ^ (prefixWord ++ tailWord_854948).sum := by decide
  have hdescent : baseEnd_854948 < baseStart_854948 := by decide
  rcases family_descends (prefixWord ++ tailWord_854948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854984 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_854984 : Nat := 118140960795 + 854984 * 2 ^ 59
def prefixEnd_854984 : Nat := 4983230072969 + 3 ^ 40 * 854984 * 2
def baseEnd_854984 : Nat := 292678495935858736578671

theorem tailTrace_854984 : CollatzResearch.WordTrace tailWord_854984 prefixEnd_854984 292678495935858736578671 := by
  unfold tailWord_854984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591914167273231243546003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20789218889697641658061337 15591914167273231243546003)
  ·
    refine ⟨23387871250909846865319005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15591914167273231243546003 23387871250909846865319005)
    ·
      refine ⟨8770451719091192574494627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23387871250909846865319005 8770451719091192574494627)
      ·
        refine ⟨13155677578636788861741941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8770451719091192574494627 13155677578636788861741941)
        ·
          refine ⟨1233344772997198955788307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13155677578636788861741941 1233344772997198955788307)
          ·
            refine ⟨1850017159495798433682461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233344772997198955788307 1850017159495798433682461)
            ·
              refine ⟨693756434810924412630923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1850017159495798433682461 693756434810924412630923)
              ·
                refine ⟨1040634652216386618946385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693756434810924412630923 1040634652216386618946385)
                ·
                  refine ⟨780475989162289964209789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040634652216386618946385 780475989162289964209789)
                  ·
                    refine ⟨292678495935858736578671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780475989162289964209789 292678495935858736578671)
                    ·
                      rfl

theorem cell22_854984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_854984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854984 prefixEnd_854984 := by exact prefixLift 854984
  have htrace : WordTrace (prefixWord ++ tailWord_854984) baseStart_854984 baseEnd_854984 := by
    simpa [prefixWord, tailWord_854984, baseEnd_854984] using wordTrace_append hprefix tailTrace_854984
  have hstable : (prefixWord ++ tailWord_854984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854984).length < 2 ^ (prefixWord ++ tailWord_854984).sum := by decide
  have hdescent : baseEnd_854984 < baseStart_854984 := by decide
  rcases family_descends (prefixWord ++ tailWord_854984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854997 : List Nat := [1, 3, 2, 3, 3, 2, 2, 6]
def baseStart_854997 : Nat := 118140960795 + 854997 * 2 ^ 59
def prefixEnd_854997 : Nat := 4983230072969 + 3 ^ 40 * 854997 * 2
def baseEnd_854997 : Nat := 32520327344614559555959

theorem tailTrace_854997 : CollatzResearch.WordTrace tailWord_854997 prefixEnd_854997 32520327344614559555959 := by
  unfold tailWord_854997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184302483499365707315245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20789534988999577138210163 31184302483499365707315245)
  ·
    refine ⟨11694113431312262140243217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31184302483499365707315245 11694113431312262140243217)
    ·
      refine ⟨8770585073484196605182413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11694113431312262140243217 8770585073484196605182413)
      ·
        refine ⟨3288969402556573726943405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8770585073484196605182413 3288969402556573726943405)
        ·
          refine ⟨1233363525958715147603777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3288969402556573726943405 1233363525958715147603777)
          ·
            refine ⟨925022644469036360702833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233363525958715147603777 925022644469036360702833)
            ·
              refine ⟨693766983351777270527125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925022644469036360702833 693766983351777270527125)
              ·
                refine ⟨32520327344614559555959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 693766983351777270527125 32520327344614559555959)
                ·
                  rfl

theorem cell22_854997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 6].length) (baseStart_854997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_854997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_854997 prefixEnd_854997 := by exact prefixLift 854997
  have htrace : WordTrace (prefixWord ++ tailWord_854997) baseStart_854997 baseEnd_854997 := by
    simpa [prefixWord, tailWord_854997, baseEnd_854997] using wordTrace_append hprefix tailTrace_854997
  have hstable : (prefixWord ++ tailWord_854997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854997).length < 2 ^ (prefixWord ++ tailWord_854997).sum := by decide
  have hdescent : baseEnd_854997 < baseStart_854997 := by decide
  rcases family_descends (prefixWord ++ tailWord_854997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855012 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_855012 : Nat := 118140960795 + 855012 * 2 ^ 59
def prefixEnd_855012 : Nat := 4983230072969 + 3 ^ 40 * 855012 * 2
def baseEnd_855012 : Nat := 292688080908075996878585

theorem tailTrace_855012 : CollatzResearch.WordTrace tailWord_855012 prefixEnd_855012 292688080908075996878585 := by
  unfold tailWord_855012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592424789222511634555645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20789899718963348846074193 15592424789222511634555645)
  ·
    refine ⟨5847159295958441862958367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15592424789222511634555645 5847159295958441862958367)
    ·
      refine ⟨8770738943937662794437551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847159295958441862958367 8770738943937662794437551)
      ·
        refine ⟨13156108415906494191656327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8770738943937662794437551 13156108415906494191656327)
        ·
          refine ⟨19734162623859741287484491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13156108415906494191656327 19734162623859741287484491)
          ·
            refine ⟨29601243935789611931226737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19734162623859741287484491 29601243935789611931226737)
            ·
              refine ⟨22200932951842208948420053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29601243935789611931226737 22200932951842208948420053)
              ·
                refine ⟨520334366058801772228595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22200932951842208948420053 520334366058801772228595)
                ·
                  refine ⟨780501549088202658342893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520334366058801772228595 780501549088202658342893)
                  ·
                    refine ⟨292688080908075996878585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 780501549088202658342893 292688080908075996878585)
                    ·
                      rfl

theorem cell22_855012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_855012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855012 prefixEnd_855012 := by exact prefixLift 855012
  have htrace : WordTrace (prefixWord ++ tailWord_855012) baseStart_855012 baseEnd_855012 := by
    simpa [prefixWord, tailWord_855012, baseEnd_855012] using wordTrace_append hprefix tailTrace_855012
  have hstable : (prefixWord ++ tailWord_855012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855012).length < 2 ^ (prefixWord ++ tailWord_855012).sum := by decide
  have hdescent : baseEnd_855012 < baseStart_855012 := by decide
  rcases family_descends (prefixWord ++ tailWord_855012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855102 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_855102 : Nat := 118140960795 + 855102 * 2 ^ 59
def prefixEnd_855102 : Nat := 4983230072969 + 3 ^ 40 * 855102 * 2
def baseEnd_855102 : Nat := 292718889747345762128309

theorem tailTrace_855102 : CollatzResearch.WordTrace tailWord_855102 prefixEnd_855102 292718889747345762128309 := by
  unfold tailWord_855102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898516518514871079985945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20792088098745979093258373 3898516518514871079985945)
  ·
    refine ⟨2923887388886153309989459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3898516518514871079985945 2923887388886153309989459)
    ·
      refine ⟨4385831083329229964984189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923887388886153309989459 4385831083329229964984189)
      ·
        refine ⟨1644686656248461236869071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4385831083329229964984189 1644686656248461236869071)
        ·
          refine ⟨2467029984372691855303607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644686656248461236869071 2467029984372691855303607)
          ·
            refine ⟨3700544976559037782955411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467029984372691855303607 3700544976559037782955411)
            ·
              refine ⟨5550817464838556674433117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700544976559037782955411 5550817464838556674433117)
              ·
                refine ⟨2081556549314458752912419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5550817464838556674433117 2081556549314458752912419)
                ·
                  refine ⟨3122334823971688129368629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081556549314458752912419 3122334823971688129368629)
                  ·
                    refine ⟨292718889747345762128309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3122334823971688129368629 292718889747345762128309)
                    ·
                      rfl

theorem cell22_855102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_855102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855102 prefixEnd_855102 := by exact prefixLift 855102
  have htrace : WordTrace (prefixWord ++ tailWord_855102) baseStart_855102 baseEnd_855102 := by
    simpa [prefixWord, tailWord_855102, baseEnd_855102] using wordTrace_append hprefix tailTrace_855102
  have hstable : (prefixWord ++ tailWord_855102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855102).length < 2 ^ (prefixWord ++ tailWord_855102).sum := by decide
  have hdescent : baseEnd_855102 < baseStart_855102 := by decide
  rcases family_descends (prefixWord ++ tailWord_855102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855113 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_855113 : Nat := 118140960795 + 855113 * 2 ^ 59
def prefixEnd_855113 : Nat := 4983230072969 + 3 ^ 40 * 855113 * 2
def baseEnd_855113 : Nat := 292722655272145400103275

theorem tailTrace_855113 : CollatzResearch.WordTrace tailWord_855113 prefixEnd_855113 292722655272145400103275 := by
  unfold tailWord_855113
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188533351079117518537993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792355567386078345691995 31188533351079117518537993)
  ·
    refine ⟨23391400013309338138903495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31188533351079117518537993 23391400013309338138903495)
    ·
      refine ⟨35087100019964007208355243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23391400013309338138903495 35087100019964007208355243)
      ·
        refine ⟨52630650029946010812532865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35087100019964007208355243 52630650029946010812532865)
        ·
          refine ⟨39472987522459508109399649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52630650029946010812532865 39472987522459508109399649)
          ·
            refine ⟨29604740641844631082049737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39472987522459508109399649 29604740641844631082049737)
            ·
              refine ⟨22203555481383473311537303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29604740641844631082049737 22203555481383473311537303)
              ·
                refine ⟨33305333222075209967305955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22203555481383473311537303 33305333222075209967305955)
                ·
                  refine ⟨49957999833112814950958933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33305333222075209967305955 49957999833112814950958933)
                  ·
                    refine ⟨292722655272145400103275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49957999833112814950958933 292722655272145400103275)
                    ·
                      rfl

theorem cell22_855113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_855113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855113 prefixEnd_855113 := by exact prefixLift 855113
  have htrace : WordTrace (prefixWord ++ tailWord_855113) baseStart_855113 baseEnd_855113 := by
    simpa [prefixWord, tailWord_855113, baseEnd_855113] using wordTrace_append hprefix tailTrace_855113
  have hstable : (prefixWord ++ tailWord_855113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855113).length < 2 ^ (prefixWord ++ tailWord_855113).sum := by decide
  have hdescent : baseEnd_855113 < baseStart_855113 := by decide
  rcases family_descends (prefixWord ++ tailWord_855113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855117 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_855117 : Nat := 118140960795 + 855117 * 2 ^ 59
def prefixEnd_855117 : Nat := 4983230072969 + 3 ^ 40 * 855117 * 2
def baseEnd_855117 : Nat := 292724024553890723003263

theorem tailTrace_855117 : CollatzResearch.WordTrace tailWord_855117 prefixEnd_855117 292724024553890723003263 := by
  unfold tailWord_855117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188679243064626201683605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792452828709750801122403 31188679243064626201683605)
  ·
    refine ⟨1461969339518654353203919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31188679243064626201683605 1461969339518654353203919)
    ·
      refine ⟨2192954009277981529805879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461969339518654353203919 2192954009277981529805879)
      ·
        refine ⟨3289431013916972294708819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2192954009277981529805879 3289431013916972294708819)
        ·
          refine ⟨4934146520875458442063229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289431013916972294708819 4934146520875458442063229)
          ·
            refine ⟨1850304945328296915773711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4934146520875458442063229 1850304945328296915773711)
            ·
              refine ⟨2775457417992445373660567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850304945328296915773711 2775457417992445373660567)
              ·
                refine ⟨4163186126988668060490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775457417992445373660567 4163186126988668060490851)
                ·
                  refine ⟨6244779190483002090736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163186126988668060490851 6244779190483002090736277)
                  ·
                    refine ⟨292724024553890723003263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6244779190483002090736277 292724024553890723003263)
                    ·
                      rfl

theorem cell22_855117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_855117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855117 prefixEnd_855117 := by exact prefixLift 855117
  have htrace : WordTrace (prefixWord ++ tailWord_855117) baseStart_855117 baseEnd_855117 := by
    simpa [prefixWord, tailWord_855117, baseEnd_855117] using wordTrace_append hprefix tailTrace_855117
  have hstable : (prefixWord ++ tailWord_855117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855117).length < 2 ^ (prefixWord ++ tailWord_855117).sum := by decide
  have hdescent : baseEnd_855117 < baseStart_855117 := by decide
  rcases family_descends (prefixWord ++ tailWord_855117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855160 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 5]
def baseStart_855160 : Nat := 118140960795 + 855160 * 2 ^ 59
def prefixEnd_855160 : Nat := 4983230072969 + 3 ^ 40 * 855160 * 2
def baseEnd_855160 : Nat := 97579581444217648059377

theorem tailTrace_855160 : CollatzResearch.WordTrace tailWord_855160 prefixEnd_855160 97579581444217648059377 := by
  unfold tailWord_855160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595123790954422272749467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20793498387939229696999289 15595123790954422272749467)
  ·
    refine ⟨23392685686431633409124201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15595123790954422272749467 23392685686431633409124201)
    ·
      refine ⟨17544514264823725056843151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23392685686431633409124201 17544514264823725056843151)
      ·
        refine ⟨26316771397235587585264727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17544514264823725056843151 26316771397235587585264727)
        ·
          refine ⟨39475157095853381377897091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26316771397235587585264727 39475157095853381377897091)
          ·
            refine ⟨59212735643780072066845637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39475157095853381377897091 59212735643780072066845637)
            ·
              refine ⟨11102387933208763512533557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59212735643780072066845637 11102387933208763512533557)
              ·
                refine ⟨1040848868738321579300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11102387933208763512533557 1040848868738321579300021)
                ·
                  refine ⟨97579581444217648059377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040848868738321579300021 97579581444217648059377)
                  ·
                    rfl

theorem cell22_855160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 5].length) (baseStart_855160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855160 prefixEnd_855160 := by exact prefixLift 855160
  have htrace : WordTrace (prefixWord ++ tailWord_855160) baseStart_855160 baseEnd_855160 := by
    simpa [prefixWord, tailWord_855160, baseEnd_855160] using wordTrace_append hprefix tailTrace_855160
  have hstable : (prefixWord ++ tailWord_855160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855160).length < 2 ^ (prefixWord ++ tailWord_855160).sum := by decide
  have hdescent : baseEnd_855160 < baseStart_855160 := by decide
  rcases family_descends (prefixWord ++ tailWord_855160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855166 : List Nat := [4, 2, 4, 1, 1, 1, 1, 8]
def baseStart_855166 : Nat := 118140960795 + 855166 * 2 ^ 59
def prefixEnd_855166 : Nat := 4983230072969 + 3 ^ 40 * 855166 * 2
def baseEnd_855166 : Nat := 32526755361696769836457

theorem tailTrace_855166 : CollatzResearch.WordTrace tailWord_855166 prefixEnd_855166 32526755361696769836457 := by
  unfold tailWord_855166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898808302485888446277169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20793644279924738380144901 3898808302485888446277169)
  ·
    refine ⟨2924106226864416334707877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3898808302485888446277169 2924106226864416334707877)
    ·
      refine ⟨548269917537078062757727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2924106226864416334707877 548269917537078062757727)
      ·
        refine ⟨822404876305617094136591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548269917537078062757727 822404876305617094136591)
        ·
          refine ⟨1233607314458425641204887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822404876305617094136591 1233607314458425641204887)
          ·
            refine ⟨1850410971687638461807331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233607314458425641204887 1850410971687638461807331)
            ·
              refine ⟨2775616457531457692710997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850410971687638461807331 2775616457531457692710997)
              ·
                refine ⟨32526755361696769836457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2775616457531457692710997 32526755361696769836457)
                ·
                  rfl

theorem cell22_855166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_855166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855166 prefixEnd_855166 := by exact prefixLift 855166
  have htrace : WordTrace (prefixWord ++ tailWord_855166) baseStart_855166 baseEnd_855166 := by
    simpa [prefixWord, tailWord_855166, baseEnd_855166] using wordTrace_append hprefix tailTrace_855166
  have hstable : (prefixWord ++ tailWord_855166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855166).length < 2 ^ (prefixWord ++ tailWord_855166).sum := by decide
  have hdescent : baseEnd_855166 < baseStart_855166 := by decide
  rcases family_descends (prefixWord ++ tailWord_855166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855359 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 1, 4]
def baseStart_855359 : Nat := 118140960795 + 855359 * 2 ^ 59
def prefixEnd_855359 : Nat := 4983230072969 + 3 ^ 40 * 855359 * 2
def baseEnd_855359 : Nat := 292806866099482758452521

theorem tailTrace_855359 : CollatzResearch.WordTrace tailWord_855359 prefixEnd_855359 292806866099482758452521 := by
  unfold tailWord_855359
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197505708187901531993131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20798337138791934354662087 31197505708187901531993131)
  ·
    refine ⟨46796258562281852297989697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31197505708187901531993131 46796258562281852297989697)
    ·
      refine ⟨35097193921711389223492273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46796258562281852297989697 35097193921711389223492273)
      ·
        refine ⟨26322895441283541917619205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35097193921711389223492273 26322895441283541917619205)
        ·
          refine ⟨4935542895240664109553601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26322895441283541917619205 4935542895240664109553601)
          ·
            refine ⟨3701657171430498082165201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935542895240664109553601 3701657171430498082165201)
            ·
              refine ⟨2776242878572873561623901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701657171430498082165201 2776242878572873561623901)
              ·
                refine ⟨1041091079464827585608963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776242878572873561623901 1041091079464827585608963)
                ·
                  refine ⟨1561636619197241378413445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041091079464827585608963 1561636619197241378413445)
                  ·
                    refine ⟨292806866099482758452521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561636619197241378413445 292806866099482758452521)
                    ·
                      rfl

theorem cell22_855359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_855359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855359 prefixEnd_855359 := by exact prefixLift 855359
  have htrace : WordTrace (prefixWord ++ tailWord_855359) baseStart_855359 baseEnd_855359 := by
    simpa [prefixWord, tailWord_855359, baseEnd_855359] using wordTrace_append hprefix tailTrace_855359
  have hstable : (prefixWord ++ tailWord_855359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855359).length < 2 ^ (prefixWord ++ tailWord_855359).sum := by decide
  have hdescent : baseEnd_855359 < baseStart_855359 := by decide
  rcases family_descends (prefixWord ++ tailWord_855359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855404 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_855404 : Nat := 118140960795 + 855404 * 2 ^ 59
def prefixEnd_855404 : Nat := 4983230072969 + 3 ^ 40 * 855404 * 2
def baseEnd_855404 : Nat := 292822270519117641077383

theorem tailTrace_855404 : CollatzResearch.WordTrace tailWord_855404 prefixEnd_855404 292822270519117641077383 := by
  unfold tailWord_855404
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599573496512437108690633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20799431328683249478254177 15599573496512437108690633)
  ·
    refine ⟨11699680122384327831517975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15599573496512437108690633 11699680122384327831517975)
    ·
      refine ⟨17549520183576491747276963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11699680122384327831517975 17549520183576491747276963)
      ·
        refine ⟨26324280275364737620915445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17549520183576491747276963 26324280275364737620915445)
        ·
          refine ⟨2467901275815444151960823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26324280275364737620915445 2467901275815444151960823)
          ·
            refine ⟨3701851913723166227941235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467901275815444151960823 3701851913723166227941235)
            ·
              refine ⟨5552777870584749341911853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701851913723166227941235 5552777870584749341911853)
              ·
                refine ⟨2082291701469281003216945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5552777870584749341911853 2082291701469281003216945)
                ·
                  refine ⟨1561718776101960752412709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082291701469281003216945 1561718776101960752412709)
                  ·
                    refine ⟨292822270519117641077383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561718776101960752412709 292822270519117641077383)
                    ·
                      rfl

theorem cell22_855404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_855404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855404 prefixEnd_855404 := by exact prefixLift 855404
  have htrace : WordTrace (prefixWord ++ tailWord_855404) baseStart_855404 baseEnd_855404 := by
    simpa [prefixWord, tailWord_855404, baseEnd_855404] using wordTrace_append hprefix tailTrace_855404
  have hstable : (prefixWord ++ tailWord_855404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855404).length < 2 ^ (prefixWord ++ tailWord_855404).sum := by decide
  have hdescent : baseEnd_855404 < baseStart_855404 := by decide
  rcases family_descends (prefixWord ++ tailWord_855404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855425 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 4]
def baseStart_855425 : Nat := 118140960795 + 855425 * 2 ^ 59
def prefixEnd_855425 : Nat := 4983230072969 + 3 ^ 40 * 855425 * 2
def baseEnd_855425 : Nat := 97609819749426862100773

theorem tailTrace_855425 : CollatzResearch.WordTrace tailWord_855425 prefixEnd_855425 97609819749426862100773 := by
  unfold tailWord_855425
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199912925948794803895729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20799941950632529869263819 31199912925948794803895729)
  ·
    refine ⟨23399934694461596102921797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31199912925948794803895729 23399934694461596102921797)
    ·
      refine ⟨4387487755211549269297837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23399934694461596102921797 4387487755211549269297837)
      ·
        refine ⟨1645307908204330975986689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4387487755211549269297837 1645307908204330975986689)
        ·
          refine ⟨1233980931153248231990017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645307908204330975986689 1233980931153248231990017)
          ·
            refine ⟨925485698364936173992513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233980931153248231990017 925485698364936173992513)
            ·
              refine ⟨694114273773702130494385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925485698364936173992513 694114273773702130494385)
              ·
                refine ⟨520585705330276597870789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694114273773702130494385 520585705330276597870789)
                ·
                  refine ⟨97609819749426862100773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520585705330276597870789 97609819749426862100773)
                  ·
                    rfl

theorem cell22_855425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_855425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855425 prefixEnd_855425 := by exact prefixLift 855425
  have htrace : WordTrace (prefixWord ++ tailWord_855425) baseStart_855425 baseEnd_855425 := by
    simpa [prefixWord, tailWord_855425, baseEnd_855425] using wordTrace_append hprefix tailTrace_855425
  have hstable : (prefixWord ++ tailWord_855425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855425).length < 2 ^ (prefixWord ++ tailWord_855425).sum := by decide
  have hdescent : baseEnd_855425 < baseStart_855425 := by decide
  rcases family_descends (prefixWord ++ tailWord_855425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855447 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 9]
def baseStart_855447 : Nat := 118140960795 + 855447 * 2 ^ 59
def prefixEnd_855447 : Nat := 4983230072969 + 3 ^ 40 * 855447 * 2
def baseEnd_855447 : Nat := 97612330099293287417417

theorem tailTrace_855447 : CollatzResearch.WordTrace tailWord_855447 prefixEnd_855447 97612330099293287417417 := by
  unfold tailWord_855447
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200715331869092561196595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20800476887912728374131063 31200715331869092561196595)
  ·
    refine ⟨46801072997803638841794893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31200715331869092561196595 46801072997803638841794893)
    ·
      refine ⟨17550402374176364565673085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46801072997803638841794893 17550402374176364565673085)
      ·
        refine ⟨6581400890316136712127407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17550402374176364565673085 6581400890316136712127407)
        ·
          refine ⟨9872101335474205068191111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581400890316136712127407 9872101335474205068191111)
          ·
            refine ⟨14808152003211307602286667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872101335474205068191111 14808152003211307602286667)
            ·
              refine ⟨22212228004816961403430001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808152003211307602286667 22212228004816961403430001)
              ·
                refine ⟨16659171003612721052572501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22212228004816961403430001 16659171003612721052572501)
                ·
                  refine ⟨97612330099293287417417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16659171003612721052572501 97612330099293287417417)
                  ·
                    rfl

theorem cell22_855447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_855447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855447 prefixEnd_855447 := by exact prefixLift 855447
  have htrace : WordTrace (prefixWord ++ tailWord_855447) baseStart_855447 baseEnd_855447 := by
    simpa [prefixWord, tailWord_855447, baseEnd_855447] using wordTrace_append hprefix tailTrace_855447
  have hstable : (prefixWord ++ tailWord_855447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855447).length < 2 ^ (prefixWord ++ tailWord_855447).sum := by decide
  have hdescent : baseEnd_855447 < baseStart_855447 := by decide
  rcases family_descends (prefixWord ++ tailWord_855447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855509 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 6]
def baseStart_855509 : Nat := 118140960795 + 855509 * 2 ^ 59
def prefixEnd_855509 : Nat := 4983230072969 + 3 ^ 40 * 855509 * 2
def baseEnd_855509 : Nat := 97619404721644122400687

theorem tailTrace_855509 : CollatzResearch.WordTrace tailWord_855509 prefixEnd_855509 97619404721644122400687 := by
  unfold tailWord_855509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31202976657644477149953581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20801984438429651433302387 31202976657644477149953581)
  ·
    refine ⟨11701116246616678931232593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31202976657644477149953581 11701116246616678931232593)
    ·
      refine ⟨8775837184962509198424445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11701116246616678931232593 8775837184962509198424445)
      ·
        refine ⟨3290938944360940949409167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8775837184962509198424445 3290938944360940949409167)
        ·
          refine ⟨4936408416541411424113751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290938944360940949409167 4936408416541411424113751)
          ·
            refine ⟨7404612624812117136170627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936408416541411424113751 7404612624812117136170627)
            ·
              refine ⟨11106918937218175704255941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404612624812117136170627 11106918937218175704255941)
              ·
                refine ⟨2082547300728407944547989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11106918937218175704255941 2082547300728407944547989)
                ·
                  refine ⟨97619404721644122400687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2082547300728407944547989 97619404721644122400687)
                  ·
                    rfl

theorem cell22_855509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_855509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855509 prefixEnd_855509 := by exact prefixLift 855509
  have htrace : WordTrace (prefixWord ++ tailWord_855509) baseStart_855509 baseEnd_855509 := by
    simpa [prefixWord, tailWord_855509, baseEnd_855509] using wordTrace_append hprefix tailTrace_855509
  have hstable : (prefixWord ++ tailWord_855509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855509).length < 2 ^ (prefixWord ++ tailWord_855509).sum := by decide
  have hdescent : baseEnd_855509 < baseStart_855509 := by decide
  rcases family_descends (prefixWord ++ tailWord_855509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855524 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_855524 : Nat := 118140960795 + 855524 * 2 ^ 59
def prefixEnd_855524 : Nat := 4983230072969 + 3 ^ 40 * 855524 * 2
def baseEnd_855524 : Nat := 292863348971477328077015

theorem tailTrace_855524 : CollatzResearch.WordTrace tailWord_855524 prefixEnd_855524 292863348971477328077015 := by
  unfold tailWord_855524
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601761876295067355874813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20802349168393423141166417 15601761876295067355874813)
  ·
    refine ⟨5850660703610650258453055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15601761876295067355874813 5850660703610650258453055)
    ·
      refine ⟨8775991055415975387679583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850660703610650258453055 8775991055415975387679583)
      ·
        refine ⟨13163986583123963081519375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775991055415975387679583 13163986583123963081519375)
        ·
          refine ⟨19745979874685944622279063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13163986583123963081519375 19745979874685944622279063)
          ·
            refine ⟨29618969812028916933418595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19745979874685944622279063 29618969812028916933418595)
            ·
              refine ⟨44428454718043375400127893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29618969812028916933418595 44428454718043375400127893)
              ·
                refine ⟨2082583814908283221880995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44428454718043375400127893 2082583814908283221880995)
                ·
                  refine ⟨3123875722362424832821493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082583814908283221880995 3123875722362424832821493)
                  ·
                    refine ⟨292863348971477328077015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3123875722362424832821493 292863348971477328077015)
                    ·
                      rfl

theorem cell22_855524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_855524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855524 prefixEnd_855524 := by exact prefixLift 855524
  have htrace : WordTrace (prefixWord ++ tailWord_855524) baseStart_855524 baseEnd_855524 := by
    simpa [prefixWord, tailWord_855524, baseEnd_855524] using wordTrace_append hprefix tailTrace_855524
  have hstable : (prefixWord ++ tailWord_855524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855524).length < 2 ^ (prefixWord ++ tailWord_855524).sum := by decide
  have hdescent : baseEnd_855524 < baseStart_855524 := by decide
  rcases family_descends (prefixWord ++ tailWord_855524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855691 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_855691 : Nat := 118140960795 + 855691 * 2 ^ 59
def prefixEnd_855691 : Nat := 4983230072969 + 3 ^ 40 * 855691 * 2
def baseEnd_855691 : Nat := 292920516484344559151503

theorem tailTrace_855691 : CollatzResearch.WordTrace tailWord_855691 prefixEnd_855691 292920516484344559151503 := by
  unfold tailWord_855691
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209614742985122233078927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20806409828656748155385951 31209614742985122233078927)
  ·
    refine ⟨46814422114477683349618391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31209614742985122233078927 46814422114477683349618391)
    ·
      refine ⟨70221633171716525024427587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46814422114477683349618391 70221633171716525024427587)
      ·
        refine ⟨105332449757574787536641381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70221633171716525024427587 105332449757574787536641381)
        ·
          refine ⟨19749834329545272663120259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105332449757574787536641381 19749834329545272663120259)
          ·
            refine ⟨29624751494317908994680389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19749834329545272663120259 29624751494317908994680389)
            ·
              refine ⟨5554640905184607936502573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29624751494317908994680389 5554640905184607936502573)
              ·
                refine ⟨2082990339444227976188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5554640905184607936502573 2082990339444227976188465)
                ·
                  refine ⟨1562242754583170982141349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082990339444227976188465 1562242754583170982141349)
                  ·
                    refine ⟨292920516484344559151503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1562242754583170982141349 292920516484344559151503)
                    ·
                      rfl

theorem cell22_855691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_855691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855691 prefixEnd_855691 := by exact prefixLift 855691
  have htrace : WordTrace (prefixWord ++ tailWord_855691) baseStart_855691 baseEnd_855691 := by
    simpa [prefixWord, tailWord_855691, baseEnd_855691] using wordTrace_append hprefix tailTrace_855691
  have hstable : (prefixWord ++ tailWord_855691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855691).length < 2 ^ (prefixWord ++ tailWord_855691).sum := by decide
  have hdescent : baseEnd_855691 < baseStart_855691 := by decide
  rcases family_descends (prefixWord ++ tailWord_855691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855710 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_855710 : Nat := 118140960795 + 855710 * 2 ^ 59
def prefixEnd_855710 : Nat := 4983230072969 + 3 ^ 40 * 855710 * 2
def baseEnd_855710 : Nat := 292927020572634842926445

theorem tailTrace_855710 : CollatzResearch.WordTrace tailWord_855710 prefixEnd_855710 292927020572634842926445 := by
  unfold tailWord_855710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901288466239536059752573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20806871819944192318680389 3901288466239536059752573)
  ·
    refine ⟨1462983174839826022407215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3901288466239536059752573 1462983174839826022407215)
    ·
      refine ⟨2194474762259739033610823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462983174839826022407215 2194474762259739033610823)
      ·
        refine ⟨3291712143389608550416235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194474762259739033610823 3291712143389608550416235)
        ·
          refine ⟨4937568215084412825624353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291712143389608550416235 4937568215084412825624353)
          ·
            refine ⟨3703176161313309619218265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4937568215084412825624353 3703176161313309619218265)
            ·
              refine ⟨2777382120984982214413699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703176161313309619218265 2777382120984982214413699)
              ·
                refine ⟨4166073181477473321620549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777382120984982214413699 4166073181477473321620549)
                ·
                  refine ⟨781138721527026247803853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4166073181477473321620549 781138721527026247803853)
                  ·
                    refine ⟨292927020572634842926445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781138721527026247803853 292927020572634842926445)
                    ·
                      rfl

theorem cell22_855710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_855710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855710 prefixEnd_855710 := by exact prefixLift 855710
  have htrace : WordTrace (prefixWord ++ tailWord_855710) baseStart_855710 baseEnd_855710 := by
    simpa [prefixWord, tailWord_855710, baseEnd_855710] using wordTrace_append hprefix tailTrace_855710
  have hstable : (prefixWord ++ tailWord_855710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855710).length < 2 ^ (prefixWord ++ tailWord_855710).sum := by decide
  have hdescent : baseEnd_855710 < baseStart_855710 := by decide
  rcases family_descends (prefixWord ++ tailWord_855710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855768 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 5]
def baseStart_855768 : Nat := 118140960795 + 855768 * 2 ^ 59
def prefixEnd_855768 : Nat := 4983230072969 + 3 ^ 40 * 855768 * 2
def baseEnd_855768 : Nat := 97648958385980674992089

theorem tailTrace_855768 : CollatzResearch.WordTrace tailWord_855768 prefixEnd_855768 97648958385980674992089 := by
  unfold tailWord_855768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15606211581853082191815979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20808282109137442922421305 15606211581853082191815979)
  ·
    refine ⟨23409317372779623287723969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15606211581853082191815979 23409317372779623287723969)
    ·
      refine ⟨17556988029584717465792977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23409317372779623287723969 17556988029584717465792977)
      ·
        refine ⟨13167741022188538099344733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17556988029584717465792977 13167741022188538099344733)
        ·
          refine ⟨4937902883320701787254275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13167741022188538099344733 4937902883320701787254275)
          ·
            refine ⟨7406854324981052680881413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937902883320701787254275 7406854324981052680881413)
            ·
              refine ⟨1388785185933947377665265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7406854324981052680881413 1388785185933947377665265)
              ·
                refine ⟨1041588889450460533248949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388785185933947377665265 1041588889450460533248949)
                ·
                  refine ⟨97648958385980674992089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1041588889450460533248949 97648958385980674992089)
                  ·
                    rfl

theorem cell22_855768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 5].length) (baseStart_855768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855768 prefixEnd_855768 := by exact prefixLift 855768
  have htrace : WordTrace (prefixWord ++ tailWord_855768) baseStart_855768 baseEnd_855768 := by
    simpa [prefixWord, tailWord_855768, baseEnd_855768] using wordTrace_append hprefix tailTrace_855768
  have hstable : (prefixWord ++ tailWord_855768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855768).length < 2 ^ (prefixWord ++ tailWord_855768).sum := by decide
  have hdescent : baseEnd_855768 < baseStart_855768 := by decide
  rcases family_descends (prefixWord ++ tailWord_855768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855845 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_855845 : Nat := 118140960795 + 855845 * 2 ^ 59
def prefixEnd_855845 : Nat := 4983230072969 + 3 ^ 40 * 855845 * 2
def baseEnd_855845 : Nat := 292973233831539490801031

theorem tailTrace_855845 : CollatzResearch.WordTrace tailWord_855845 prefixEnd_855845 292973233831539490801031 := by
  unfold tailWord_855845
  simp only [CollatzResearch.WordTrace]
  refine ⟨31215231584427206534184989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20810154389618137689456659 31215231584427206534184989)
  ·
    refine ⟨11705711844160202450319371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31215231584427206534184989 11705711844160202450319371)
    ·
      refine ⟨17558567766240303675479057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11705711844160202450319371 17558567766240303675479057)
      ·
        refine ⟨13168925824680227756609293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17558567766240303675479057 13168925824680227756609293)
        ·
          refine ⟨4938347184255085408728485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13168925824680227756609293 4938347184255085408728485)
          ·
            refine ⟨925940097047828514136591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4938347184255085408728485 925940097047828514136591)
            ·
              refine ⟨1388910145571742771204887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925940097047828514136591 1388910145571742771204887)
              ·
                refine ⟨2083365218357614156807331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388910145571742771204887 2083365218357614156807331)
                ·
                  refine ⟨3125047827536421235210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083365218357614156807331 3125047827536421235210997)
                  ·
                    refine ⟨292973233831539490801031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3125047827536421235210997 292973233831539490801031)
                    ·
                      rfl

theorem cell22_855845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_855845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855845 prefixEnd_855845 := by exact prefixLift 855845
  have htrace : WordTrace (prefixWord ++ tailWord_855845) baseStart_855845 baseEnd_855845 := by
    simpa [prefixWord, tailWord_855845, baseEnd_855845] using wordTrace_append hprefix tailTrace_855845
  have hstable : (prefixWord ++ tailWord_855845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855845).length < 2 ^ (prefixWord ++ tailWord_855845).sum := by decide
  have hdescent : baseEnd_855845 < baseStart_855845 := by decide
  rcases family_descends (prefixWord ++ tailWord_855845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855858 : List Nat := [3, 2, 1, 1, 3, 3, 1, 8]
def baseStart_855858 : Nat := 118140960795 + 855858 * 2 ^ 59
def prefixEnd_855858 : Nat := 4983230072969 + 3 ^ 40 * 855858 * 2
def baseEnd_855858 : Nat := 32553075999690198913999

theorem tailTrace_855858 : CollatzResearch.WordTrace tailWord_855858 prefixEnd_855858 32553075999690198913999 := by
  unfold tailWord_855858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803926433345027438602057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20810470488920073169605485 7803926433345027438602057)
  ·
    refine ⟨5852944825008770578951543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7803926433345027438602057 5852944825008770578951543)
    ·
      refine ⟨8779417237513155868427315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852944825008770578951543 8779417237513155868427315)
      ·
        refine ⟨13169125856269733802640973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779417237513155868427315 13169125856269733802640973)
        ·
          refine ⟨4938422196101150175990365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13169125856269733802640973 4938422196101150175990365)
          ·
            refine ⟨1851908323537931315996387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4938422196101150175990365 1851908323537931315996387)
            ·
              refine ⟨2777862485306896973994581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851908323537931315996387 2777862485306896973994581)
              ·
                refine ⟨32553075999690198913999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2777862485306896973994581 32553075999690198913999)
                ·
                  rfl

theorem cell22_855858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_855858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855858 prefixEnd_855858 := by exact prefixLift 855858
  have htrace : WordTrace (prefixWord ++ tailWord_855858) baseStart_855858 baseEnd_855858 := by
    simpa [prefixWord, tailWord_855858, baseEnd_855858] using wordTrace_append hprefix tailTrace_855858
  have hstable : (prefixWord ++ tailWord_855858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855858).length < 2 ^ (prefixWord ++ tailWord_855858).sum := by decide
  have hdescent : baseEnd_855858 < baseStart_855858 := by decide
  rcases family_descends (prefixWord ++ tailWord_855858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855860 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_855860 : Nat := 118140960795 + 855860 * 2 ^ 59
def prefixEnd_855860 : Nat := 4983230072969 + 3 ^ 40 * 855860 * 2
def baseEnd_855860 : Nat := 292978368638084451675985

theorem tailTrace_855860 : CollatzResearch.WordTrace tailWord_855860 prefixEnd_855860 292978368638084451675985 := by
  unfold tailWord_855860
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607889339686432047990517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20810519119581909397320689 15607889339686432047990517)
  ·
    refine ⟨1463239625595603004499111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15607889339686432047990517 1463239625595603004499111)
    ·
      refine ⟨2194859438393404506748667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463239625595603004499111 2194859438393404506748667)
      ·
        refine ⟨3292289157590106760123001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194859438393404506748667 3292289157590106760123001)
        ·
          refine ⟨2469216868192580070092251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292289157590106760123001 2469216868192580070092251)
          ·
            refine ⟨3703825302288870105138377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469216868192580070092251 3703825302288870105138377)
            ·
              refine ⟨2777868976716652578853783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703825302288870105138377 2777868976716652578853783)
              ·
                refine ⟨4166803465074978868280675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777868976716652578853783 4166803465074978868280675)
                ·
                  refine ⟨6250205197612468302421013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166803465074978868280675 6250205197612468302421013)
                  ·
                    refine ⟨292978368638084451675985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6250205197612468302421013 292978368638084451675985)
                    ·
                      rfl

theorem cell22_855860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_855860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855860 prefixEnd_855860 := by exact prefixLift 855860
  have htrace : WordTrace (prefixWord ++ tailWord_855860) baseStart_855860 baseEnd_855860 := by
    simpa [prefixWord, tailWord_855860, baseEnd_855860] using wordTrace_append hprefix tailTrace_855860
  have hstable : (prefixWord ++ tailWord_855860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855860).length < 2 ^ (prefixWord ++ tailWord_855860).sum := by decide
  have hdescent : baseEnd_855860 < baseStart_855860 := by decide
  rcases family_descends (prefixWord ++ tailWord_855860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855862 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_855862 : Nat := 118140960795 + 855862 * 2 ^ 59
def prefixEnd_855862 : Nat := 4983230072969 + 3 ^ 40 * 855862 * 2
def baseEnd_855862 : Nat := 292979053278957113125979

theorem tailTrace_855862 : CollatzResearch.WordTrace tailWord_855862 prefixEnd_855862 292979053278957113125979 := by
  unfold tailWord_855862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950990726585351152347115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20810567750243745625035893 1950990726585351152347115)
  ·
    refine ⟨2926486089878026728520673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950990726585351152347115 2926486089878026728520673)
    ·
      refine ⟨2194864567408520046390505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2926486089878026728520673 2194864567408520046390505)
      ·
        refine ⟨1646148425556390034792879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2194864567408520046390505 1646148425556390034792879)
        ·
          refine ⟨2469222638334585052189319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646148425556390034792879 2469222638334585052189319)
          ·
            refine ⟨3703833957501877578283979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469222638334585052189319 3703833957501877578283979)
            ·
              refine ⟨5555750936252816367425969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703833957501877578283979 5555750936252816367425969)
              ·
                refine ⟨4166813202189612275569477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5555750936252816367425969 4166813202189612275569477)
                ·
                  refine ⟨781277475410552301669277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4166813202189612275569477 781277475410552301669277)
                  ·
                    refine ⟨292979053278957113125979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781277475410552301669277 292979053278957113125979)
                    ·
                      rfl

theorem cell22_855862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_855862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855862 prefixEnd_855862 := by exact prefixLift 855862
  have htrace : WordTrace (prefixWord ++ tailWord_855862) baseStart_855862 baseEnd_855862 := by
    simpa [prefixWord, tailWord_855862, baseEnd_855862] using wordTrace_append hprefix tailTrace_855862
  have hstable : (prefixWord ++ tailWord_855862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855862).length < 2 ^ (prefixWord ++ tailWord_855862).sum := by decide
  have hdescent : baseEnd_855862 < baseStart_855862 := by decide
  rcases family_descends (prefixWord ++ tailWord_855862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855948 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 6]
def baseStart_855948 : Nat := 118140960795 + 855948 * 2 ^ 59
def prefixEnd_855948 : Nat := 4983230072969 + 3 ^ 40 * 855948 * 2
def baseEnd_855948 : Nat := 97669497612160518491905

theorem tailTrace_855948 : CollatzResearch.WordTrace tailWord_855948 prefixEnd_855948 97669497612160518491905 := by
  unfold tailWord_855948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609494151527027562592249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20812658868702703416789665 15609494151527027562592249)
  ·
    refine ⟨11707120613645270671944187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15609494151527027562592249 11707120613645270671944187)
    ·
      refine ⟨17560680920467906007916281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11707120613645270671944187 17560680920467906007916281)
      ·
        refine ⟨13170510690350929505937211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17560680920467906007916281 13170510690350929505937211)
        ·
          refine ⟨19755766035526394258905817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170510690350929505937211 19755766035526394258905817)
          ·
            refine ⟨14816824526644795694179363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19755766035526394258905817 14816824526644795694179363)
            ·
              refine ⟨22225236789967193541269045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14816824526644795694179363 22225236789967193541269045)
              ·
                refine ⟨2083615949059424394493973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22225236789967193541269045 2083615949059424394493973)
                ·
                  refine ⟨97669497612160518491905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2083615949059424394493973 97669497612160518491905)
                  ·
                    rfl

theorem cell22_855948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_855948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855948 prefixEnd_855948 := by exact prefixLift 855948
  have htrace : WordTrace (prefixWord ++ tailWord_855948) baseStart_855948 baseEnd_855948 := by
    simpa [prefixWord, tailWord_855948, baseEnd_855948] using wordTrace_append hprefix tailTrace_855948
  have hstable : (prefixWord ++ tailWord_855948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855948).length < 2 ^ (prefixWord ++ tailWord_855948).sum := by decide
  have hdescent : baseEnd_855948 < baseStart_855948 := by decide
  rcases family_descends (prefixWord ++ tailWord_855948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855965 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 6]
def baseStart_855965 : Nat := 118140960795 + 855965 * 2 ^ 59
def prefixEnd_855965 : Nat := 4983230072969 + 3 ^ 40 * 855965 * 2
def baseEnd_855965 : Nat := 97671437427966392600221

theorem tailTrace_855965 : CollatzResearch.WordTrace tailWord_855965 prefixEnd_855965 97671437427966392600221 := by
  unfold tailWord_855965
  simp only [CollatzResearch.WordTrace]
  refine ⟨31219608343992467028553349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20813072229328311352368899 31219608343992467028553349)
  ·
    refine ⟨5853676564498587567853753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31219608343992467028553349 5853676564498587567853753)
    ·
      refine ⟨4390257423373940675890315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5853676564498587567853753 4390257423373940675890315)
      ·
        refine ⟨6585386135060911013835473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4390257423373940675890315 6585386135060911013835473)
        ·
          refine ⟨4939039601295683260376605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6585386135060911013835473 4939039601295683260376605)
          ·
            refine ⟨1852139850485881222641227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4939039601295683260376605 1852139850485881222641227)
            ·
              refine ⟨2778209775728821833961841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852139850485881222641227 2778209775728821833961841)
              ·
                refine ⟨2083657331796616375471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778209775728821833961841 2083657331796616375471381)
                ·
                  refine ⟨97671437427966392600221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2083657331796616375471381 97671437427966392600221)
                  ·
                    rfl

theorem cell22_855965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_855965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855965 prefixEnd_855965 := by exact prefixLift 855965
  have htrace : WordTrace (prefixWord ++ tailWord_855965) baseStart_855965 baseEnd_855965 := by
    simpa [prefixWord, tailWord_855965, baseEnd_855965] using wordTrace_append hprefix tailTrace_855965
  have hstable : (prefixWord ++ tailWord_855965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855965).length < 2 ^ (prefixWord ++ tailWord_855965).sum := by decide
  have hdescent : baseEnd_855965 < baseStart_855965 := by decide
  rcases family_descends (prefixWord ++ tailWord_855965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855993 : List Nat := [1, 2, 1, 4, 2, 1, 11]
def baseStart_855993 : Nat := 118140960795 + 855993 * 2 ^ 59
def prefixEnd_855993 : Nat := 4983230072969 + 3 ^ 40 * 855993 * 2
def baseEnd_855993 : Nat := 10852736935411719929651

theorem tailTrace_855993 : CollatzResearch.WordTrace tailWord_855993 prefixEnd_855993 10852736935411719929651 := by
  unfold tailWord_855993
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220629587891027810572633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20813753058594018540381755 31220629587891027810572633)
  ·
    refine ⟨23415472190918270857929475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31220629587891027810572633 23415472190918270857929475)
    ·
      refine ⟨35123208286377406286894213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23415472190918270857929475 35123208286377406286894213)
      ·
        refine ⟨6585601553695763678792665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35123208286377406286894213 6585601553695763678792665)
        ·
          refine ⟨4939201165271822759094499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6585601553695763678792665 4939201165271822759094499)
          ·
            refine ⟨7408801747907734138641749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939201165271822759094499 7408801747907734138641749)
            ·
              refine ⟨10852736935411719929651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7408801747907734138641749 10852736935411719929651)
              ·
                rfl

theorem cell22_855993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 11].length) (baseStart_855993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855993 prefixEnd_855993 := by exact prefixLift 855993
  have htrace : WordTrace (prefixWord ++ tailWord_855993) baseStart_855993 baseEnd_855993 := by
    simpa [prefixWord, tailWord_855993, baseEnd_855993] using wordTrace_append hprefix tailTrace_855993
  have hstable : (prefixWord ++ tailWord_855993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855993).length < 2 ^ (prefixWord ++ tailWord_855993).sum := by decide
  have hdescent : baseEnd_855993 < baseStart_855993 := by decide
  rcases family_descends (prefixWord ++ tailWord_855993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855997 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_855997 : Nat := 118140960795 + 855997 * 2 ^ 59
def prefixEnd_855997 : Nat := 4983230072969 + 3 ^ 40 * 855997 * 2
def baseEnd_855997 : Nat := 293025266537861761000565

theorem tailTrace_855997 : CollatzResearch.WordTrace tailWord_855997 prefixEnd_855997 293025266537861761000565 := by
  unfold tailWord_855997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220775479876536493718245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20813850319917690995812163 31220775479876536493718245)
  ·
    refine ⟨5853895402476850592572171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31220775479876536493718245 5853895402476850592572171)
    ·
      refine ⟨8780843103715275888858257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853895402476850592572171 8780843103715275888858257)
      ·
        refine ⟨6585632327786456916643693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8780843103715275888858257 6585632327786456916643693)
        ·
          refine ⟨2469612122919921343741385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6585632327786456916643693 2469612122919921343741385)
          ·
            refine ⟨1852209092189941007806039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469612122919921343741385 1852209092189941007806039)
            ·
              refine ⟨2778313638284911511709059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852209092189941007806039 2778313638284911511709059)
              ·
                refine ⟨4167470457427367267563589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778313638284911511709059 4167470457427367267563589)
                ·
                  refine ⟨781400710767631362668173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4167470457427367267563589 781400710767631362668173)
                  ·
                    refine ⟨293025266537861761000565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781400710767631362668173 293025266537861761000565)
                    ·
                      rfl

theorem cell22_855997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_855997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_855997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_855997 prefixEnd_855997 := by exact prefixLift 855997
  have htrace : WordTrace (prefixWord ++ tailWord_855997) baseStart_855997 baseEnd_855997 := by
    simpa [prefixWord, tailWord_855997, baseEnd_855997] using wordTrace_append hprefix tailTrace_855997
  have hstable : (prefixWord ++ tailWord_855997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855997).length < 2 ^ (prefixWord ++ tailWord_855997).sum := by decide
  have hdescent : baseEnd_855997 < baseStart_855997 := by decide
  rcases family_descends (prefixWord ++ tailWord_855997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856014 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_856014 : Nat := 118140960795 + 856014 * 2 ^ 59
def prefixEnd_856014 : Nat := 4983230072969 + 3 ^ 40 * 856014 * 2
def baseEnd_856014 : Nat := 293031085985279383325513

theorem tailTrace_856014 : CollatzResearch.WordTrace tailWord_856014 prefixEnd_856014 293031085985279383325513 := by
  unfold tailWord_856014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902674440101868549635887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20814263680543298931391397 3902674440101868549635887)
  ·
    refine ⟨5854011660152802824453831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902674440101868549635887 5854011660152802824453831)
    ·
      refine ⟨8781017490229204236680747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854011660152802824453831 8781017490229204236680747)
      ·
        refine ⟨13171526235343806355021121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781017490229204236680747 13171526235343806355021121)
        ·
          refine ⟨9878644676507854766265841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13171526235343806355021121 9878644676507854766265841)
          ·
            refine ⟨7408983507380891074699381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9878644676507854766265841 7408983507380891074699381)
            ·
              refine ⟨694592203816958538253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7408983507380891074699381 694592203816958538253067)
              ·
                refine ⟨1041888305725437807379601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694592203816958538253067 1041888305725437807379601)
                ·
                  refine ⟨781416229294078355534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1041888305725437807379601 781416229294078355534701)
                  ·
                    refine ⟨293031085985279383325513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781416229294078355534701 293031085985279383325513)
                    ·
                      rfl

theorem cell22_856014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_856014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856014 prefixEnd_856014 := by exact prefixLift 856014
  have htrace : WordTrace (prefixWord ++ tailWord_856014) baseStart_856014 baseEnd_856014 := by
    simpa [prefixWord, tailWord_856014, baseEnd_856014] using wordTrace_append hprefix tailTrace_856014
  have hstable : (prefixWord ++ tailWord_856014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856014).length < 2 ^ (prefixWord ++ tailWord_856014).sum := by decide
  have hdescent : baseEnd_856014 < baseStart_856014 := by decide
  rcases family_descends (prefixWord ++ tailWord_856014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856134 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_856134 : Nat := 118140960795 + 856134 * 2 ^ 59
def prefixEnd_856134 : Nat := 4983230072969 + 3 ^ 40 * 856134 * 2
def baseEnd_856134 : Nat := 97690721479213023441715

theorem tailTrace_856134 : CollatzResearch.WordTrace tailWord_856134 prefixEnd_856134 97690721479213023441715 := by
  unfold tailWord_856134
  simp only [CollatzResearch.WordTrace]
  refine ⟨975805383761881527857983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20817181520253472594303637 975805383761881527857983)
  ·
    refine ⟨1463708075642822291786975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975805383761881527857983 1463708075642822291786975)
    ·
      refine ⟨2195562113464233437680463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463708075642822291786975 2195562113464233437680463)
      ·
        refine ⟨3293343170196350156520695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195562113464233437680463 3293343170196350156520695)
        ·
          refine ⟨4940014755294525234781043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293343170196350156520695 4940014755294525234781043)
          ·
            refine ⟨7410022132941787852171565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940014755294525234781043 7410022132941787852171565)
            ·
              refine ⟨2778758299853170444564337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410022132941787852171565 2778758299853170444564337)
              ·
                refine ⟨2084068724889877833423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778758299853170444564337 2084068724889877833423253)
                ·
                  refine ⟨97690721479213023441715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2084068724889877833423253 97690721479213023441715)
                  ·
                    rfl

theorem cell22_856134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_856134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856134 prefixEnd_856134 := by exact prefixLift 856134
  have htrace : WordTrace (prefixWord ++ tailWord_856134) baseStart_856134 baseEnd_856134 := by
    simpa [prefixWord, tailWord_856134, baseEnd_856134] using wordTrace_append hprefix tailTrace_856134
  have hstable : (prefixWord ++ tailWord_856134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856134).length < 2 ^ (prefixWord ++ tailWord_856134).sum := by decide
  have hdescent : baseEnd_856134 < baseStart_856134 := by decide
  rcases family_descends (prefixWord ++ tailWord_856134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856228 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_856228 : Nat := 118140960795 + 856228 * 2 ^ 59
def prefixEnd_856228 : Nat := 4983230072969 + 3 ^ 40 * 856228 * 2
def baseEnd_856228 : Nat := 293104342558654158474857

theorem tailTrace_856228 : CollatzResearch.WordTrace tailWord_856228 prefixEnd_856228 293104342558654158474857 := by
  unfold tailWord_856228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614600371019831472688669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20819467161359775296918225 15614600371019831472688669)
  ·
    refine ⟨5855475139132436802258251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15614600371019831472688669 5855475139132436802258251)
    ·
      refine ⟨8783212708698655203387377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855475139132436802258251 8783212708698655203387377)
      ·
        refine ⟨6587409531523991402540533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8783212708698655203387377 6587409531523991402540533)
        ·
          refine ⟨617569643580374193988175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6587409531523991402540533 617569643580374193988175)
          ·
            refine ⟨926354465370561290982263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617569643580374193988175 926354465370561290982263)
            ·
              refine ⟨1389531698055841936473395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926354465370561290982263 1389531698055841936473395)
              ·
                refine ⟨2084297547083762904710093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389531698055841936473395 2084297547083762904710093)
                ·
                  refine ⟨781611580156411089266285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2084297547083762904710093 781611580156411089266285)
                  ·
                    refine ⟨293104342558654158474857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781611580156411089266285 293104342558654158474857)
                    ·
                      rfl

theorem cell22_856228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_856228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856228 prefixEnd_856228 := by exact prefixLift 856228
  have htrace : WordTrace (prefixWord ++ tailWord_856228) baseStart_856228 baseEnd_856228 := by
    simpa [prefixWord, tailWord_856228, baseEnd_856228] using wordTrace_append hprefix tailTrace_856228
  have hstable : (prefixWord ++ tailWord_856228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856228).length < 2 ^ (prefixWord ++ tailWord_856228).sum := by decide
  have hdescent : baseEnd_856228 < baseStart_856228 := by decide
  rcases family_descends (prefixWord ++ tailWord_856228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856267 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_856267 : Nat := 118140960795 + 856267 * 2 ^ 59
def prefixEnd_856267 : Nat := 4983230072969 + 3 ^ 40 * 856267 * 2
def baseEnd_856267 : Nat := 293117693055671056749737

theorem tailTrace_856267 : CollatzResearch.WordTrace tailWord_856267 prefixEnd_856267 293117693055671056749737 := by
  unfold tailWord_856267
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230623188898372606047055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20820415459265581737364703 31230623188898372606047055)
  ·
    refine ⟨46845934783347558909070583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31230623188898372606047055 46845934783347558909070583)
    ·
      refine ⟨70268902175021338363605875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845934783347558909070583 70268902175021338363605875)
      ·
        refine ⟨105403353262532007545408813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70268902175021338363605875 105403353262532007545408813)
        ·
          refine ⟨39526257473449502829528305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105403353262532007545408813 39526257473449502829528305)
          ·
            refine ⟨29644693105087127122146229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39526257473449502829528305 29644693105087127122146229)
            ·
              refine ⟨2779189978601918167701209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29644693105087127122146229 2779189978601918167701209)
              ·
                refine ⟨2084392483951438625775907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779189978601918167701209 2084392483951438625775907)
                ·
                  refine ⟨3126588725927157938663861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084392483951438625775907 3126588725927157938663861)
                  ·
                    refine ⟨293117693055671056749737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3126588725927157938663861 293117693055671056749737)
                    ·
                      rfl

theorem cell22_856267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_856267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856267 prefixEnd_856267 := by exact prefixLift 856267
  have htrace : WordTrace (prefixWord ++ tailWord_856267) baseStart_856267 baseEnd_856267 := by
    simpa [prefixWord, tailWord_856267, baseEnd_856267] using wordTrace_append hprefix tailTrace_856267
  have hstable : (prefixWord ++ tailWord_856267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856267).length < 2 ^ (prefixWord ++ tailWord_856267).sum := by decide
  have hdescent : baseEnd_856267 < baseStart_856267 := by decide
  rcases family_descends (prefixWord ++ tailWord_856267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856301 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_856301 : Nat := 118140960795 + 856301 * 2 ^ 59
def prefixEnd_856301 : Nat := 4983230072969 + 3 ^ 40 * 856301 * 2
def baseEnd_856301 : Nat := 293129331950506301399633

theorem tailTrace_856301 : CollatzResearch.WordTrace tailWord_856301 prefixEnd_856301 293129331950506301399633 := by
  unfold tailWord_856301
  simp only [CollatzResearch.WordTrace]
  refine ⟨31231863270775196412784757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20821242180516797608523171 31231863270775196412784757)
  ·
    refine ⟨2927987181635174663698571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31231863270775196412784757 2927987181635174663698571)
    ·
      refine ⟨4391980772452761995547857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927987181635174663698571 4391980772452761995547857)
      ·
        refine ⟨3293985579339571496660893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4391980772452761995547857 3293985579339571496660893)
        ·
          refine ⟨1235244592252339311247835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3293985579339571496660893 1235244592252339311247835)
          ·
            refine ⟨1852866888378508966871753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235244592252339311247835 1852866888378508966871753)
            ·
              refine ⟨1389650166283881725153815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852866888378508966871753 1389650166283881725153815)
              ·
                refine ⟨2084475249425822587730723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389650166283881725153815 2084475249425822587730723)
                ·
                  refine ⟨3126712874138733881596085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084475249425822587730723 3126712874138733881596085)
                  ·
                    refine ⟨293129331950506301399633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3126712874138733881596085 293129331950506301399633)
                    ·
                      rfl

theorem cell22_856301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_856301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856301 prefixEnd_856301 := by exact prefixLift 856301
  have htrace : WordTrace (prefixWord ++ tailWord_856301) baseStart_856301 baseEnd_856301 := by
    simpa [prefixWord, tailWord_856301, baseEnd_856301] using wordTrace_append hprefix tailTrace_856301
  have hstable : (prefixWord ++ tailWord_856301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856301).length < 2 ^ (prefixWord ++ tailWord_856301).sum := by decide
  have hdescent : baseEnd_856301 < baseStart_856301 := by decide
  rcases family_descends (prefixWord ++ tailWord_856301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856314 : List Nat := [3, 1, 1, 1, 1, 6, 3, 6]
def baseStart_856314 : Nat := 118140960795 + 856314 * 2 ^ 59
def prefixEnd_856314 : Nat := 4983230072969 + 3 ^ 40 * 856314 * 2
def baseEnd_856314 : Nat := 32570420235130955647177

theorem tailTrace_856314 : CollatzResearch.WordTrace tailWord_856314 prefixEnd_856314 32570420235130955647177 := by
  unfold tailWord_856314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808084354932024908251999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20821558279818733088671997 7808084354932024908251999)
  ·
    refine ⟨11712126532398037362377999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7808084354932024908251999 11712126532398037362377999)
    ·
      refine ⟨17568189798597056043566999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11712126532398037362377999 17568189798597056043566999)
      ·
        refine ⟨26352284697895584065350499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17568189798597056043566999 26352284697895584065350499)
        ·
          refine ⟨39528427046843376098025749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26352284697895584065350499 39528427046843376098025749)
          ·
            refine ⟨1852895017820783254594957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39528427046843376098025749 1852895017820783254594957)
            ·
              refine ⟨694835631682793720473109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852895017820783254594957 694835631682793720473109)
              ·
                refine ⟨32570420235130955647177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 694835631682793720473109 32570420235130955647177)
                ·
                  rfl

theorem cell22_856314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_856314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856314 prefixEnd_856314 := by exact prefixLift 856314
  have htrace : WordTrace (prefixWord ++ tailWord_856314) baseStart_856314 baseEnd_856314 := by
    simpa [prefixWord, tailWord_856314, baseEnd_856314] using wordTrace_append hprefix tailTrace_856314
  have hstable : (prefixWord ++ tailWord_856314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856314).length < 2 ^ (prefixWord ++ tailWord_856314).sum := by decide
  have hdescent : baseEnd_856314 < baseStart_856314 := by decide
  rcases family_descends (prefixWord ++ tailWord_856314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856316 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_856316 : Nat := 118140960795 + 856316 * 2 ^ 59
def prefixEnd_856316 : Nat := 4983230072969 + 3 ^ 40 * 856316 * 2
def baseEnd_856316 : Nat := 293134466757051262274587

theorem tailTrace_856316 : CollatzResearch.WordTrace tailWord_856316 prefixEnd_856316 293134466757051262274587 := by
  unfold tailWord_856316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616205182860426987290401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20821606910480569316387201 15616205182860426987290401)
  ·
    refine ⟨11712153887145320240467801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15616205182860426987290401 11712153887145320240467801)
    ·
      refine ⟨8784115415358990180350851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11712153887145320240467801 8784115415358990180350851)
      ·
        refine ⟨13176173123038485270526277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8784115415358990180350851 13176173123038485270526277)
        ·
          refine ⟨2470532460569715988223677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13176173123038485270526277 2470532460569715988223677)
          ·
            refine ⟨926449672713643495583879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2470532460569715988223677 926449672713643495583879)
            ·
              refine ⟨1389674509070465243375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926449672713643495583879 1389674509070465243375819)
              ·
                refine ⟨2084511763605697865063729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389674509070465243375819 2084511763605697865063729)
                ·
                  refine ⟨1563383822704273398797797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084511763605697865063729 1563383822704273398797797)
                  ·
                    refine ⟨293134466757051262274587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563383822704273398797797 293134466757051262274587)
                    ·
                      rfl

theorem cell22_856316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_856316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856316 prefixEnd_856316 := by exact prefixLift 856316
  have htrace : WordTrace (prefixWord ++ tailWord_856316) baseStart_856316 baseEnd_856316 := by
    simpa [prefixWord, tailWord_856316, baseEnd_856316] using wordTrace_append hprefix tailTrace_856316
  have hstable : (prefixWord ++ tailWord_856316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856316).length < 2 ^ (prefixWord ++ tailWord_856316).sum := by decide
  have hdescent : baseEnd_856316 < baseStart_856316 := by decide
  rcases family_descends (prefixWord ++ tailWord_856316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856365 : List Nat := [1, 5, 3, 1, 3, 1, 2, 6]
def baseStart_856365 : Nat := 118140960795 + 856365 * 2 ^ 59
def prefixEnd_856365 : Nat := 4983230072969 + 3 ^ 40 * 856365 * 2
def baseEnd_856365 : Nat := 32572360050936829755493

theorem tailTrace_856365 : CollatzResearch.WordTrace tailWord_856365 prefixEnd_856365 32572360050936829755493 := by
  unfold tailWord_856365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234197542543335343114549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20822798361695556895409699 31234197542543335343114549)
  ·
    refine ⟨2928206019613437688416989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31234197542543335343114549 2928206019613437688416989)
    ·
      refine ⟨1098077257355039133156371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2928206019613437688416989 1098077257355039133156371)
      ·
        refine ⟨1647115886032558699734557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098077257355039133156371 1647115886032558699734557)
        ·
          refine ⟨617668457262209512400459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1647115886032558699734557 617668457262209512400459)
          ·
            refine ⟨926502685893314268600689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617668457262209512400459 926502685893314268600689)
            ·
              refine ⟨694877014419985701450517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926502685893314268600689 694877014419985701450517)
              ·
                refine ⟨32572360050936829755493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 694877014419985701450517 32572360050936829755493)
                ·
                  rfl

theorem cell22_856365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 6].length) (baseStart_856365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856365 prefixEnd_856365 := by exact prefixLift 856365
  have htrace : WordTrace (prefixWord ++ tailWord_856365) baseStart_856365 baseEnd_856365 := by
    simpa [prefixWord, tailWord_856365, baseEnd_856365] using wordTrace_append hprefix tailTrace_856365
  have hstable : (prefixWord ++ tailWord_856365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856365).length < 2 ^ (prefixWord ++ tailWord_856365).sum := by decide
  have hdescent : baseEnd_856365 < baseStart_856365 := by decide
  rcases family_descends (prefixWord ++ tailWord_856365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856387 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 8]
def baseStart_856387 : Nat := 118140960795 + 856387 * 2 ^ 59
def prefixEnd_856387 : Nat := 4983230072969 + 3 ^ 40 * 856387 * 2
def baseEnd_856387 : Nat := 97719590502676914583123

theorem tailTrace_856387 : CollatzResearch.WordTrace tailWord_856387 prefixEnd_856387 97719590502676914583123 := by
  unfold tailWord_856387
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234999948463633100415415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20823333298975755400276943 31234999948463633100415415)
  ·
    refine ⟨46852499922695449650623123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31234999948463633100415415 46852499922695449650623123)
    ·
      refine ⟨70278749884043174475934685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46852499922695449650623123 70278749884043174475934685)
      ·
        refine ⟨26354531206516190428475507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70278749884043174475934685 26354531206516190428475507)
        ·
          refine ⟨39531796809774285642713261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26354531206516190428475507 39531796809774285642713261)
          ·
            refine ⟨14824423803665357116017473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39531796809774285642713261 14824423803665357116017473)
            ·
              refine ⟨11118317852749017837013105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14824423803665357116017473 11118317852749017837013105)
              ·
                refine ⟨8338738389561763377759829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11118317852749017837013105 8338738389561763377759829)
                ·
                  refine ⟨97719590502676914583123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8338738389561763377759829 97719590502676914583123)
                  ·
                    rfl

theorem cell22_856387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_856387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856387 prefixEnd_856387 := by exact prefixLift 856387
  have htrace : WordTrace (prefixWord ++ tailWord_856387) baseStart_856387 baseEnd_856387 := by
    simpa [prefixWord, tailWord_856387, baseEnd_856387] using wordTrace_append hprefix tailTrace_856387
  have hstable : (prefixWord ++ tailWord_856387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856387).length < 2 ^ (prefixWord ++ tailWord_856387).sum := by decide
  have hdescent : baseEnd_856387 < baseStart_856387 := by decide
  rcases family_descends (prefixWord ++ tailWord_856387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856419 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_856419 : Nat := 118140960795 + 856419 * 2 ^ 59
def prefixEnd_856419 : Nat := 4983230072969 + 3 ^ 40 * 856419 * 2
def baseEnd_856419 : Nat := 293169725761993326949271

theorem tailTrace_856419 : CollatzResearch.WordTrace tailWord_856419 prefixEnd_856419 293169725761993326949271 := by
  unfold tailWord_856419
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236167084347702565580311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20824111389565135043720207 31236167084347702565580311)
  ·
    refine ⟨46854250626521553848370467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31236167084347702565580311 46854250626521553848370467)
    ·
      refine ⟨70281375939782330772555701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46854250626521553848370467 70281375939782330772555701)
      ·
        refine ⟨6588878994354593509927097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70281375939782330772555701 6588878994354593509927097)
        ·
          refine ⟨4941659245765945132445323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6588878994354593509927097 4941659245765945132445323)
          ·
            refine ⟨7412488868648917698667985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941659245765945132445323 7412488868648917698667985)
            ·
              refine ⟨5559366651486688274000989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7412488868648917698667985 5559366651486688274000989)
              ·
                refine ⟨2084762494307508102750371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5559366651486688274000989 2084762494307508102750371)
                ·
                  refine ⟨3127143741461262154125557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084762494307508102750371 3127143741461262154125557)
                  ·
                    refine ⟨293169725761993326949271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3127143741461262154125557 293169725761993326949271)
                    ·
                      rfl

theorem cell22_856419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_856419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856419 prefixEnd_856419 := by exact prefixLift 856419
  have htrace : WordTrace (prefixWord ++ tailWord_856419) baseStart_856419 baseEnd_856419 := by
    simpa [prefixWord, tailWord_856419, baseEnd_856419] using wordTrace_append hprefix tailTrace_856419
  have hstable : (prefixWord ++ tailWord_856419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856419).length < 2 ^ (prefixWord ++ tailWord_856419).sum := by decide
  have hdescent : baseEnd_856419 < baseStart_856419 := by decide
  rcases family_descends (prefixWord ++ tailWord_856419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856423 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 1, 4]
def baseStart_856423 : Nat := 118140960795 + 856423 * 2 ^ 59
def prefixEnd_856423 : Nat := 4983230072969 + 3 ^ 40 * 856423 * 2
def baseEnd_856423 : Nat := 293171095043738649849259

theorem tailTrace_856423 : CollatzResearch.WordTrace tailWord_856423 prefixEnd_856423 293171095043738649849259 := by
  unfold tailWord_856423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236312976333211248725923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20824208650888807499150615 31236312976333211248725923)
  ·
    refine ⟨46854469464499816873088885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31236312976333211248725923 46854469464499816873088885)
    ·
      refine ⟨4392606512296857831852083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46854469464499816873088885 4392606512296857831852083)
      ·
        refine ⟨6588909768445286747778125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392606512296857831852083 6588909768445286747778125)
        ·
          refine ⟨2470841163166982530416797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6588909768445286747778125 2470841163166982530416797)
          ·
            refine ⟨926565436187618448906299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2470841163166982530416797 926565436187618448906299)
            ·
              refine ⟨1389848154281427673359449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926565436187618448906299 1389848154281427673359449)
              ·
                refine ⟨1042386115711070755019587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389848154281427673359449 1042386115711070755019587)
                ·
                  refine ⟨1563579173566606132529381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042386115711070755019587 1563579173566606132529381)
                  ·
                    refine ⟨293171095043738649849259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563579173566606132529381 293171095043738649849259)
                    ·
                      rfl

theorem cell22_856423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_856423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856423 prefixEnd_856423 := by exact prefixLift 856423
  have htrace : WordTrace (prefixWord ++ tailWord_856423) baseStart_856423 baseEnd_856423 := by
    simpa [prefixWord, tailWord_856423, baseEnd_856423] using wordTrace_append hprefix tailTrace_856423
  have hstable : (prefixWord ++ tailWord_856423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856423).length < 2 ^ (prefixWord ++ tailWord_856423).sum := by decide
  have hdescent : baseEnd_856423 < baseStart_856423 := by decide
  rcases family_descends (prefixWord ++ tailWord_856423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856449 : List Nat := [1, 2, 4, 3, 1, 11]
def baseStart_856449 : Nat := 118140960795 + 856449 * 2 ^ 59
def prefixEnd_856449 : Nat := 4983230072969 + 3 ^ 40 * 856449 * 2
def baseEnd_856449 : Nat := 3619506115741768502459

theorem tailTrace_856449 : CollatzResearch.WordTrace tailWord_856449 prefixEnd_856449 3619506115741768502459 := by
  unfold tailWord_856449
  simp only [CollatzResearch.WordTrace]
  refine ⟨31237261274239017689172401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20824840849492678459448267 31237261274239017689172401)
  ·
    refine ⟨23427945955679263266879301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31237261274239017689172401 23427945955679263266879301)
    ·
      refine ⟨4392739866689861862539869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23427945955679263266879301 4392739866689861862539869)
      ·
        refine ⟨1647277450008698198452451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4392739866689861862539869 1647277450008698198452451)
        ·
          refine ⟨2470916175013047297678677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647277450008698198452451 2470916175013047297678677)
          ·
            refine ⟨3619506115741768502459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2470916175013047297678677 3619506115741768502459)
            ·
              rfl

theorem cell22_856449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 11].length) (baseStart_856449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856449 prefixEnd_856449 := by exact prefixLift 856449
  have htrace : WordTrace (prefixWord ++ tailWord_856449) baseStart_856449 baseEnd_856449 := by
    simpa [prefixWord, tailWord_856449, baseEnd_856449] using wordTrace_append hprefix tailTrace_856449
  have hstable : (prefixWord ++ tailWord_856449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856449).length < 2 ^ (prefixWord ++ tailWord_856449).sum := by decide
  have hdescent : baseEnd_856449 < baseStart_856449 := by decide
  rcases family_descends (prefixWord ++ tailWord_856449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856479 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_856479 : Nat := 118140960795 + 856479 * 2 ^ 59
def prefixEnd_856479 : Nat := 4983230072969 + 3 ^ 40 * 856479 * 2
def baseEnd_856479 : Nat := 293190264988173170449087

theorem tailTrace_856479 : CollatzResearch.WordTrace tailWord_856479 prefixEnd_856479 293190264988173170449087 := by
  unfold tailWord_856479
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238355464130332812764491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825570309420221875176327 31238355464130332812764491)
  ·
    refine ⟨46857533196195499219146737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31238355464130332812764491 46857533196195499219146737)
    ·
      refine ⟨35143149897146624414360053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46857533196195499219146737 35143149897146624414360053)
      ·
        refine ⟨3294670302857496038846255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35143149897146624414360053 3294670302857496038846255)
        ·
          refine ⟨4942005454286244058269383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294670302857496038846255 4942005454286244058269383)
          ·
            refine ⟨7413008181429366087404075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942005454286244058269383 7413008181429366087404075)
            ·
              refine ⟨11119512272144049131106113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413008181429366087404075 11119512272144049131106113)
              ·
                refine ⟨8339634204108036848329585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11119512272144049131106113 8339634204108036848329585)
                ·
                  refine ⟨6254725653081027636247189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339634204108036848329585 6254725653081027636247189)
                  ·
                    refine ⟨293190264988173170449087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6254725653081027636247189 293190264988173170449087)
                    ·
                      rfl

theorem cell22_856479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_856479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856479 prefixEnd_856479 := by exact prefixLift 856479
  have htrace : WordTrace (prefixWord ++ tailWord_856479) baseStart_856479 baseEnd_856479 := by
    simpa [prefixWord, tailWord_856479, baseEnd_856479] using wordTrace_append hprefix tailTrace_856479
  have hstable : (prefixWord ++ tailWord_856479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856479).length < 2 ^ (prefixWord ++ tailWord_856479).sum := by decide
  have hdescent : baseEnd_856479 < baseStart_856479 := by decide
  rcases family_descends (prefixWord ++ tailWord_856479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856549 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_856549 : Nat := 118140960795 + 856549 * 2 ^ 59
def prefixEnd_856549 : Nat := 4983230072969 + 3 ^ 40 * 856549 * 2
def baseEnd_856549 : Nat := 293214227418716321198873

theorem tailTrace_856549 : CollatzResearch.WordTrace tailWord_856549 prefixEnd_856549 293214227418716321198873 := by
  unfold tailWord_856549
  simp only [CollatzResearch.WordTrace]
  refine ⟨31240908573876734767812701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20827272382584489845208467 31240908573876734767812701)
  ·
    refine ⟨11715340715203775537929763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31240908573876734767812701 11715340715203775537929763)
    ·
      refine ⟨17573011072805663306894645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11715340715203775537929763 17573011072805663306894645)
      ·
        refine ⟨1647469788075530935021373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17573011072805663306894645 1647469788075530935021373)
        ·
          refine ⟨617801170528324100633015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1647469788075530935021373 617801170528324100633015)
          ·
            refine ⟨926701755792486150949523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617801170528324100633015 926701755792486150949523)
            ·
              refine ⟨1390052633688729226424285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926701755792486150949523 1390052633688729226424285)
              ·
                refine ⟨521269737633273459909107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390052633688729226424285 521269737633273459909107)
                ·
                  refine ⟨781904606449910189863661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521269737633273459909107 781904606449910189863661)
                  ·
                    refine ⟨293214227418716321198873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781904606449910189863661 293214227418716321198873)
                    ·
                      rfl

theorem cell22_856549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_856549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856549 prefixEnd_856549 := by exact prefixLift 856549
  have htrace : WordTrace (prefixWord ++ tailWord_856549) baseStart_856549 baseEnd_856549 := by
    simpa [prefixWord, tailWord_856549, baseEnd_856549] using wordTrace_append hprefix tailTrace_856549
  have hstable : (prefixWord ++ tailWord_856549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856549).length < 2 ^ (prefixWord ++ tailWord_856549).sum := by decide
  have hdescent : baseEnd_856549 < baseStart_856549 := by decide
  rcases family_descends (prefixWord ++ tailWord_856549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856558 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_856558 : Nat := 118140960795 + 856558 * 2 ^ 59
def prefixEnd_856558 : Nat := 4983230072969 + 3 ^ 40 * 856558 * 2
def baseEnd_856558 : Nat := 293217308302643297723845

theorem tailTrace_856558 : CollatzResearch.WordTrace tailWord_856558 prefixEnd_856558 293217308302643297723845 := by
  unfold tailWord_856558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905154603855516163111291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20827491220562752869926885 3905154603855516163111291)
  ·
    refine ⟨5857731905783274244666937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905154603855516163111291 5857731905783274244666937)
    ·
      refine ⟨4393298929337455683500203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5857731905783274244666937 4393298929337455683500203)
      ·
        refine ⟨6589948394006183525250305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393298929337455683500203 6589948394006183525250305)
        ·
          refine ⟨4942461295504637643937729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6589948394006183525250305 4942461295504637643937729)
          ·
            refine ⟨3706845971628478232953297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4942461295504637643937729 3706845971628478232953297)
            ·
              refine ⟨2780134478721358674714973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706845971628478232953297 2780134478721358674714973)
              ·
                refine ⟨1042550429520509503018115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2780134478721358674714973 1042550429520509503018115)
                ·
                  refine ⟨1563825644280764254527173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042550429520509503018115 1563825644280764254527173)
                  ·
                    refine ⟨293217308302643297723845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563825644280764254527173 293217308302643297723845)
                    ·
                      rfl

theorem cell22_856558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_856558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856558 prefixEnd_856558 := by exact prefixLift 856558
  have htrace : WordTrace (prefixWord ++ tailWord_856558) baseStart_856558 baseEnd_856558 := by
    simpa [prefixWord, tailWord_856558, baseEnd_856558] using wordTrace_append hprefix tailTrace_856558
  have hstable : (prefixWord ++ tailWord_856558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856558).length < 2 ^ (prefixWord ++ tailWord_856558).sum := by decide
  have hdescent : baseEnd_856558 < baseStart_856558 := by decide
  rcases family_descends (prefixWord ++ tailWord_856558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856586 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_856586 : Nat := 118140960795 + 856586 * 2 ^ 59
def prefixEnd_856586 : Nat := 4983230072969 + 3 ^ 40 * 856586 * 2
def baseEnd_856586 : Nat := 293226893274860558023759

theorem tailTrace_856586 : CollatzResearch.WordTrace tailWord_856586 prefixEnd_856586 293226893274860558023759 := by
  unfold tailWord_856586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810564518685672521727403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20828172049828460057939741 7810564518685672521727403)
  ·
    refine ⟨11715846778028508782591105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7810564518685672521727403 11715846778028508782591105)
    ·
      refine ⟨8786885083521381586943329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11715846778028508782591105 8786885083521381586943329)
      ·
        refine ⟨6590163812641036190207497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8786885083521381586943329 6590163812641036190207497)
        ·
          refine ⟨4942622859480777142655623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6590163812641036190207497 4942622859480777142655623)
          ·
            refine ⟨7413934289221165713983435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942622859480777142655623 7413934289221165713983435)
            ·
              refine ⟨11120901433831748570975153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413934289221165713983435 11120901433831748570975153)
              ·
                refine ⟨8340676075373811428231365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11120901433831748570975153 8340676075373811428231365)
                ·
                  refine ⟨1563876764132589642793381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8340676075373811428231365 1563876764132589642793381)
                  ·
                    refine ⟨293226893274860558023759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563876764132589642793381 293226893274860558023759)
                    ·
                      rfl

theorem cell22_856586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_856586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856586 prefixEnd_856586 := by exact prefixLift 856586
  have htrace : WordTrace (prefixWord ++ tailWord_856586) baseStart_856586 baseEnd_856586 := by
    simpa [prefixWord, tailWord_856586, baseEnd_856586] using wordTrace_append hprefix tailTrace_856586
  have hstable : (prefixWord ++ tailWord_856586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856586).length < 2 ^ (prefixWord ++ tailWord_856586).sum := by decide
  have hdescent : baseEnd_856586 < baseStart_856586 := by decide
  rcases family_descends (prefixWord ++ tailWord_856586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856622 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_856622 : Nat := 118140960795 + 856622 * 2 ^ 59
def prefixEnd_856622 : Nat := 4983230072969 + 3 ^ 40 * 856622 * 2
def baseEnd_856622 : Nat := 293239216810568464123649

theorem tailTrace_856622 : CollatzResearch.WordTrace tailWord_856622 prefixEnd_856622 293239216810568464123649 := by
  unfold tailWord_856622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905446387826533529402515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20829047401741512156813413 3905446387826533529402515)
  ·
    refine ⟨5858169581739800294103773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905446387826533529402515 5858169581739800294103773)
    ·
      refine ⟨2196813593152425110288915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5858169581739800294103773 2196813593152425110288915)
      ·
        refine ⟨3295220389728637665433373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196813593152425110288915 3295220389728637665433373)
        ·
          refine ⟨1235707646148239124537515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3295220389728637665433373 1235707646148239124537515)
          ·
            refine ⟨1853561469222358686806273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235707646148239124537515 1853561469222358686806273)
            ·
              refine ⟨1390171101916769015104705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853561469222358686806273 1390171101916769015104705)
              ·
                refine ⟨1042628326437576761328529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390171101916769015104705 1042628326437576761328529)
                ·
                  refine ⟨781971244828182570996397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042628326437576761328529 781971244828182570996397)
                  ·
                    refine ⟨293239216810568464123649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781971244828182570996397 293239216810568464123649)
                    ·
                      rfl

theorem cell22_856622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_856622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856622 prefixEnd_856622 := by exact prefixLift 856622
  have htrace : WordTrace (prefixWord ++ tailWord_856622) baseStart_856622 baseEnd_856622 := by
    simpa [prefixWord, tailWord_856622, baseEnd_856622] using wordTrace_append hprefix tailTrace_856622
  have hstable : (prefixWord ++ tailWord_856622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856622).length < 2 ^ (prefixWord ++ tailWord_856622).sum := by decide
  have hdescent : baseEnd_856622 < baseStart_856622 := by decide
  rcases family_descends (prefixWord ++ tailWord_856622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856633 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_856633 : Nat := 118140960795 + 856633 * 2 ^ 59
def prefixEnd_856633 : Nat := 4983230072969 + 3 ^ 40 * 856633 * 2
def baseEnd_856633 : Nat := 293242982335368102098615

theorem tailTrace_856633 : CollatzResearch.WordTrace tailWord_856633 prefixEnd_856633 293242982335368102098615 := by
  unfold tailWord_856633
  simp only [CollatzResearch.WordTrace]
  refine ⟨31243972305572417113870553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20829314870381611409247035 31243972305572417113870553)
  ·
    refine ⟨23432979229179312835402915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31243972305572417113870553 23432979229179312835402915)
    ·
      refine ⟨35149468843768969253104373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23432979229179312835402915 35149468843768969253104373)
      ·
        refine ⟨3295262704103340867478535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35149468843768969253104373 3295262704103340867478535)
        ·
          refine ⟨4942894056155011301217803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295262704103340867478535 4942894056155011301217803)
          ·
            refine ⟨7414341084232516951826705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942894056155011301217803 7414341084232516951826705)
            ·
              refine ⟨5560755813174387713870029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414341084232516951826705 5560755813174387713870029)
              ·
                refine ⟨2085283429940395392701261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5560755813174387713870029 2085283429940395392701261)
                ·
                  refine ⟨781981286227648272262973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2085283429940395392701261 781981286227648272262973)
                  ·
                    refine ⟨293242982335368102098615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 781981286227648272262973 293242982335368102098615)
                    ·
                      rfl

theorem cell22_856633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_856633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856633 prefixEnd_856633 := by exact prefixLift 856633
  have htrace : WordTrace (prefixWord ++ tailWord_856633) baseStart_856633 baseEnd_856633 := by
    simpa [prefixWord, tailWord_856633, baseEnd_856633] using wordTrace_append hprefix tailTrace_856633
  have hstable : (prefixWord ++ tailWord_856633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856633).length < 2 ^ (prefixWord ++ tailWord_856633).sum := by decide
  have hdescent : baseEnd_856633 < baseStart_856633 := by decide
  rcases family_descends (prefixWord ++ tailWord_856633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856708 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 6]
def baseStart_856708 : Nat := 118140960795 + 856708 * 2 ^ 59
def prefixEnd_856708 : Nat := 4983230072969 + 3 ^ 40 * 856708 * 2
def baseEnd_856708 : Nat := 97756218789364302157795

theorem tailTrace_856708 : CollatzResearch.WordTrace tailWord_856708 prefixEnd_856708 97756218789364302157795 := by
  unfold tailWord_856708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623353890150352461425389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20831138520200469948567185 15623353890150352461425389)
  ·
    refine ⟨5858757708806382173034521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15623353890150352461425389 5858757708806382173034521)
    ·
      refine ⟨4394068281604786629775891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5858757708806382173034521 4394068281604786629775891)
      ·
        refine ⟨6591102422407179944663837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394068281604786629775891 6591102422407179944663837)
        ·
          refine ⟨2471663408402692479248939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6591102422407179944663837 2471663408402692479248939)
          ·
            refine ⟨3707495112604038718873409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471663408402692479248939 3707495112604038718873409)
            ·
              refine ⟨2780621334453029039155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707495112604038718873409 2780621334453029039155057)
              ·
                refine ⟨2085466000839771779366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780621334453029039155057 2085466000839771779366293)
                ·
                  refine ⟨97756218789364302157795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2085466000839771779366293 97756218789364302157795)
                  ·
                    rfl

theorem cell22_856708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_856708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856708 prefixEnd_856708 := by exact prefixLift 856708
  have htrace : WordTrace (prefixWord ++ tailWord_856708) baseStart_856708 baseEnd_856708 := by
    simpa [prefixWord, tailWord_856708, baseEnd_856708] using wordTrace_append hprefix tailTrace_856708
  have hstable : (prefixWord ++ tailWord_856708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856708).length < 2 ^ (prefixWord ++ tailWord_856708).sum := by decide
  have hdescent : baseEnd_856708 < baseStart_856708 := by decide
  rcases family_descends (prefixWord ++ tailWord_856708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856740 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_856740 : Nat := 118140960795 + 856740 * 2 ^ 59
def prefixEnd_856740 : Nat := 4983230072969 + 3 ^ 40 * 856740 * 2
def baseEnd_856740 : Nat := 293279610622055489673287

theorem tailTrace_856740 : CollatzResearch.WordTrace tailWord_856740 prefixEnd_856740 293279610622055489673287 := by
  unfold tailWord_856740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623937458092387194007837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20831916610789849592010449 15623937458092387194007837)
  ·
    refine ⟨5858976546784645197752939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15623937458092387194007837 5858976546784645197752939)
    ·
      refine ⟨8788464820176967796629409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858976546784645197752939 8788464820176967796629409)
      ·
        refine ⟨6591348615132725847472057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8788464820176967796629409 6591348615132725847472057)
        ·
          refine ⟨4943511461349544385604043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6591348615132725847472057 4943511461349544385604043)
          ·
            refine ⟨7415267192024316578406065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943511461349544385604043 7415267192024316578406065)
            ·
              refine ⟨5561450394018237433804549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415267192024316578406065 5561450394018237433804549)
              ·
                refine ⟨1042771948878419518838353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5561450394018237433804549 1042771948878419518838353)
                ·
                  refine ⟨782078961658814639128765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042771948878419518838353 782078961658814639128765)
                  ·
                    refine ⟨293279610622055489673287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782078961658814639128765 293279610622055489673287)
                    ·
                      rfl

theorem cell22_856740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_856740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856740 prefixEnd_856740 := by exact prefixLift 856740
  have htrace : WordTrace (prefixWord ++ tailWord_856740) baseStart_856740 baseEnd_856740 := by
    simpa [prefixWord, tailWord_856740, baseEnd_856740] using wordTrace_append hprefix tailTrace_856740
  have hstable : (prefixWord ++ tailWord_856740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856740).length < 2 ^ (prefixWord ++ tailWord_856740).sum := by decide
  have hdescent : baseEnd_856740 < baseStart_856740 := by decide
  rcases family_descends (prefixWord ++ tailWord_856740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856757 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_856757 : Nat := 118140960795 + 856757 * 2 ^ 59
def prefixEnd_856757 : Nat := 4983230072969 + 3 ^ 40 * 856757 * 2
def baseEnd_856757 : Nat := 293285430069473111998235

theorem tailTrace_856757 : CollatzResearch.WordTrace tailWord_856757 prefixEnd_856757 293285430069473111998235 := by
  unfold tailWord_856757
  simp only [CollatzResearch.WordTrace]
  refine ⟨31248494957123186291384525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20832329971415457527589683 31248494957123186291384525)
  ·
    refine ⟨11718185608921194859269197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31248494957123186291384525 11718185608921194859269197)
    ·
      refine ⟨4394319603345448072225949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11718185608921194859269197 4394319603345448072225949)
      ·
        refine ⟨1647869851254543027084731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4394319603345448072225949 1647869851254543027084731)
        ·
          refine ⟨2471804776881814540627097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647869851254543027084731 2471804776881814540627097)
          ·
            refine ⟨1853853582661360905470323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471804776881814540627097 1853853582661360905470323)
            ·
              refine ⟨2780780373992041358205485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853853582661360905470323 2780780373992041358205485)
              ·
                refine ⟨1042792640247015509327057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2780780373992041358205485 1042792640247015509327057)
                ·
                  refine ⟨782094480185261631995293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042792640247015509327057 782094480185261631995293)
                  ·
                    refine ⟨293285430069473111998235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782094480185261631995293 293285430069473111998235)
                    ·
                      rfl

theorem cell22_856757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_856757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856757 prefixEnd_856757 := by exact prefixLift 856757
  have htrace : WordTrace (prefixWord ++ tailWord_856757) baseStart_856757 baseEnd_856757 := by
    simpa [prefixWord, tailWord_856757, baseEnd_856757] using wordTrace_append hprefix tailTrace_856757
  have hstable : (prefixWord ++ tailWord_856757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856757).length < 2 ^ (prefixWord ++ tailWord_856757).sum := by decide
  have hdescent : baseEnd_856757 < baseStart_856757 := by decide
  rcases family_descends (prefixWord ++ tailWord_856757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856774 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_856774 : Nat := 118140960795 + 856774 * 2 ^ 59
def prefixEnd_856774 : Nat := 4983230072969 + 3 ^ 40 * 856774 * 2
def baseEnd_856774 : Nat := 293291249516890734323183

theorem tailTrace_856774 : CollatzResearch.WordTrace tailWord_856774 prefixEnd_856774 293291249516890734323183 := by
  unfold tailWord_856774
  simp only [CollatzResearch.WordTrace]
  refine ⟨976534843689424943586043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20832743332041065463168917 976534843689424943586043)
  ·
    refine ⟨1464802265534137415379065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976534843689424943586043 1464802265534137415379065)
    ·
      refine ⟨1098601699150603061534299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464802265534137415379065 1098601699150603061534299)
      ·
        refine ⟨1647902548725904592301449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098601699150603061534299 1647902548725904592301449)
        ·
          refine ⟨1235926911544428444226087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647902548725904592301449 1235926911544428444226087)
          ·
            refine ⟨1853890367316642666339131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235926911544428444226087 1853890367316642666339131)
            ·
              refine ⟨2780835550974963999508697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853890367316642666339131 2780835550974963999508697)
              ·
                refine ⟨2085626663231222999631523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780835550974963999508697 2085626663231222999631523)
                ·
                  refine ⟨3128439994846834499447285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085626663231222999631523 3128439994846834499447285)
                  ·
                    refine ⟨293291249516890734323183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3128439994846834499447285 293291249516890734323183)
                    ·
                      rfl

theorem cell22_856774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_856774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856774 prefixEnd_856774 := by exact prefixLift 856774
  have htrace : WordTrace (prefixWord ++ tailWord_856774) baseStart_856774 baseEnd_856774 := by
    simpa [prefixWord, tailWord_856774, baseEnd_856774] using wordTrace_append hprefix tailTrace_856774
  have hstable : (prefixWord ++ tailWord_856774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856774).length < 2 ^ (prefixWord ++ tailWord_856774).sum := by decide
  have hdescent : baseEnd_856774 < baseStart_856774 := by decide
  rcases family_descends (prefixWord ++ tailWord_856774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856860 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_856860 : Nat := 118140960795 + 856860 * 2 ^ 59
def prefixEnd_856860 : Nat := 4983230072969 + 3 ^ 40 * 856860 * 2
def baseEnd_856860 : Nat := 97773563024805058890973

theorem tailTrace_856860 : CollatzResearch.WordTrace tailWord_856860 prefixEnd_856860 97773563024805058890973 := by
  unfold tailWord_856860
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626125837875017441192017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20834834450500023254922689 15626125837875017441192017)
  ·
    refine ⟨11719594378406263080894013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15626125837875017441192017 11719594378406263080894013)
    ·
      refine ⟨4394847891902348655335255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11719594378406263080894013 4394847891902348655335255)
      ·
        refine ⟨6592271837853522983002883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394847891902348655335255 6592271837853522983002883)
        ·
          refine ⟨9888407756780284474504325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592271837853522983002883 9888407756780284474504325)
          ·
            refine ⟨1854076454396303338969561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9888407756780284474504325 1854076454396303338969561)
            ·
              refine ⟨1390557340797227504227171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854076454396303338969561 1390557340797227504227171)
              ·
                refine ⟨2085836011195841256340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390557340797227504227171 2085836011195841256340757)
                ·
                  refine ⟨97773563024805058890973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2085836011195841256340757 97773563024805058890973)
                  ·
                    rfl

theorem cell22_856860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_856860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856860 prefixEnd_856860 := by exact prefixLift 856860
  have htrace : WordTrace (prefixWord ++ tailWord_856860) baseStart_856860 baseEnd_856860 := by
    simpa [prefixWord, tailWord_856860, baseEnd_856860] using wordTrace_append hprefix tailTrace_856860
  have hstable : (prefixWord ++ tailWord_856860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856860).length < 2 ^ (prefixWord ++ tailWord_856860).sum := by decide
  have hdescent : baseEnd_856860 < baseStart_856860 := by decide
  rcases family_descends (prefixWord ++ tailWord_856860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_856873 : Nat := 118140960795 + 856873 * 2 ^ 59
def prefixEnd_856873 : Nat := 4983230072969 + 3 ^ 40 * 856873 * 2
def baseEnd_856873 : Nat := 293325139240087476097879

theorem tailTrace_856873 : CollatzResearch.WordTrace tailWord_856873 prefixEnd_856873 293325139240087476097879 := by
  unfold tailWord_856873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252725824702938102607273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835150549801958735071515 31252725824702938102607273)
  ·
    refine ⟨23439544368527203576955455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31252725824702938102607273 23439544368527203576955455)
    ·
      refine ⟨35159316552790805365433183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23439544368527203576955455 35159316552790805365433183)
      ·
        refine ⟨52738974829186208048149775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35159316552790805365433183 52738974829186208048149775)
        ·
          refine ⟨79108462243779312072224663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52738974829186208048149775 79108462243779312072224663)
          ·
            refine ⟨118662693365668968108336995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79108462243779312072224663 118662693365668968108336995)
            ·
              refine ⟨177994040048503452162505493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118662693365668968108336995 177994040048503452162505493)
              ·
                refine ⟨8343470627273599320117445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177994040048503452162505493 8343470627273599320117445)
                ·
                  refine ⟨1564400742613799872522021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8343470627273599320117445 1564400742613799872522021)
                  ·
                    refine ⟨293325139240087476097879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564400742613799872522021 293325139240087476097879)
                    ·
                      rfl

theorem cell22_856873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_856873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856873 prefixEnd_856873 := by exact prefixLift 856873
  have htrace : WordTrace (prefixWord ++ tailWord_856873) baseStart_856873 baseEnd_856873 := by
    simpa [prefixWord, tailWord_856873, baseEnd_856873] using wordTrace_append hprefix tailTrace_856873
  have hstable : (prefixWord ++ tailWord_856873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856873).length < 2 ^ (prefixWord ++ tailWord_856873).sum := by decide
  have hdescent : baseEnd_856873 < baseStart_856873 := by decide
  rcases family_descends (prefixWord ++ tailWord_856873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856888 : List Nat := [2, 1, 2, 1, 3, 2, 3, 8]
def baseStart_856888 : Nat := 118140960795 + 856888 * 2 ^ 59
def prefixEnd_856888 : Nat := 4983230072969 + 3 ^ 40 * 856888 * 2
def baseEnd_856888 : Nat := 32592252671848048552537

theorem tailTrace_856888 : CollatzResearch.WordTrace tailWord_856888 prefixEnd_856888 32592252671848048552537 := by
  unfold tailWord_856888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626636459824297832201659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20835515279765730442935545 15626636459824297832201659)
  ·
    refine ⟨23439954689736446748302489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15626636459824297832201659 23439954689736446748302489)
    ·
      refine ⟨17579966017302335061226867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23439954689736446748302489 17579966017302335061226867)
      ·
        refine ⟨26369949025953502591840301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17579966017302335061226867 26369949025953502591840301)
        ·
          refine ⟨9888730884732563471940113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26369949025953502591840301 9888730884732563471940113)
          ·
            refine ⟨7416548163549422603955085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9888730884732563471940113 7416548163549422603955085)
            ·
              refine ⟨2781205561331033476483157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7416548163549422603955085 2781205561331033476483157)
              ·
                refine ⟨32592252671848048552537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2781205561331033476483157 32592252671848048552537)
                ·
                  rfl

theorem cell22_856888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_856888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856888 prefixEnd_856888 := by exact prefixLift 856888
  have htrace : WordTrace (prefixWord ++ tailWord_856888) baseStart_856888 baseEnd_856888 := by
    simpa [prefixWord, tailWord_856888, baseEnd_856888] using wordTrace_append hprefix tailTrace_856888
  have hstable : (prefixWord ++ tailWord_856888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856888).length < 2 ^ (prefixWord ++ tailWord_856888).sum := by decide
  have hdescent : baseEnd_856888 < baseStart_856888 := by decide
  rcases family_descends (prefixWord ++ tailWord_856888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856967 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 5]
def baseStart_856967 : Nat := 118140960795 + 856967 * 2 ^ 59
def prefixEnd_856967 : Nat := 4983230072969 + 3 ^ 40 * 856967 * 2
def baseEnd_856967 : Nat := 97785772453700854749197

theorem tailTrace_856967 : CollatzResearch.WordTrace tailWord_856967 prefixEnd_856967 97785772453700854749197 := by
  unfold tailWord_856967
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256154286362392156529155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20837436190908261437686103 31256154286362392156529155)
  ·
    refine ⟨46884231429543588234793733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31256154286362392156529155 46884231429543588234793733)
    ·
      refine ⟨8790793393039422794023825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46884231429543588234793733 8790793393039422794023825)
      ·
        refine ⟨6593095044779567095517869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8790793393039422794023825 6593095044779567095517869)
        ·
          refine ⟨2472410641792337660819201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6593095044779567095517869 2472410641792337660819201)
          ·
            refine ⟨1854307981344253245614401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472410641792337660819201 1854307981344253245614401)
            ·
              refine ⟨1390730986008189934210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854307981344253245614401 1390730986008189934210801)
              ·
                refine ⟨1043048239506142450658101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390730986008189934210801 1043048239506142450658101)
                ·
                  refine ⟨97785772453700854749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1043048239506142450658101 97785772453700854749197)
                  ·
                    rfl

theorem cell22_856967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].length) (baseStart_856967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_856967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_856967 prefixEnd_856967 := by exact prefixLift 856967
  have htrace : WordTrace (prefixWord ++ tailWord_856967) baseStart_856967 baseEnd_856967 := by
    simpa [prefixWord, tailWord_856967, baseEnd_856967] using wordTrace_append hprefix tailTrace_856967
  have hstable : (prefixWord ++ tailWord_856967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856967).length < 2 ^ (prefixWord ++ tailWord_856967).sum := by decide
  have hdescent : baseEnd_856967 < baseStart_856967 := by decide
  rcases family_descends (prefixWord ++ tailWord_856967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857042 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_857042 : Nat := 118140960795 + 857042 * 2 ^ 59
def prefixEnd_857042 : Nat := 4983230072969 + 3 ^ 40 * 857042 * 2
def baseEnd_857042 : Nat := 293382991393827368622361

theorem tailTrace_857042 : CollatzResearch.WordTrace tailWord_857042 prefixEnd_857042 293382991393827368622361 := by
  unfold tailWord_857042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814722440272669991377345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20839259840727119977006253 7814722440272669991377345)
  ·
    refine ⟨5861041830204502493533009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7814722440272669991377345 5861041830204502493533009)
    ·
      refine ⟨4395781372653376870149757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5861041830204502493533009 4395781372653376870149757)
      ·
        refine ⟨1648418014745016326306159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4395781372653376870149757 1648418014745016326306159)
        ·
          refine ⟨2472627022117524489459239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648418014745016326306159 2472627022117524489459239)
          ·
            refine ⟨3708940533176286734188859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472627022117524489459239 3708940533176286734188859)
            ·
              refine ⟨5563410799764430101283289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708940533176286734188859 5563410799764430101283289)
              ·
                refine ⟨4172558099823322575962467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563410799764430101283289 4172558099823322575962467)
                ·
                  refine ⟨6258837149734983863943701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172558099823322575962467 6258837149734983863943701)
                  ·
                    refine ⟨293382991393827368622361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6258837149734983863943701 293382991393827368622361)
                    ·
                      rfl

theorem cell22_857042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_857042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857042 prefixEnd_857042 := by exact prefixLift 857042
  have htrace : WordTrace (prefixWord ++ tailWord_857042) baseStart_857042 baseEnd_857042 := by
    simpa [prefixWord, tailWord_857042, baseEnd_857042] using wordTrace_append hprefix tailTrace_857042
  have hstable : (prefixWord ++ tailWord_857042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857042).length < 2 ^ (prefixWord ++ tailWord_857042).sum := by decide
  have hdescent : baseEnd_857042 < baseStart_857042 := by decide
  rcases family_descends (prefixWord ++ tailWord_857042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857044 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_857044 : Nat := 118140960795 + 857044 * 2 ^ 59
def prefixEnd_857044 : Nat := 4983230072969 + 3 ^ 40 * 857044 * 2
def baseEnd_857044 : Nat := 293383676034700030072355

theorem tailTrace_857044 : CollatzResearch.WordTrace tailWord_857044 prefixEnd_857044 293383676034700030072355 := by
  unfold tailWord_857044
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629481353541717153541093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20839308471388956204721457 15629481353541717153541093)
  ·
    refine ⟨2930527753789071966288955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15629481353541717153541093 2930527753789071966288955)
    ·
      refine ⟨4395791630683607949433433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930527753789071966288955 4395791630683607949433433)
      ·
        refine ⟨3296843723012705962075075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4395791630683607949433433 3296843723012705962075075)
        ·
          refine ⟨4945265584519058943112613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296843723012705962075075 4945265584519058943112613)
          ·
            refine ⟨927237297097323551833615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4945265584519058943112613 927237297097323551833615)
            ·
              refine ⟨1390855945645985327750423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927237297097323551833615 1390855945645985327750423)
              ·
                refine ⟨2086283918468977991625635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390855945645985327750423 2086283918468977991625635)
                ·
                  refine ⟨3129425877703466987438453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086283918468977991625635 3129425877703466987438453)
                  ·
                    refine ⟨293383676034700030072355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3129425877703466987438453 293383676034700030072355)
                    ·
                      rfl

theorem cell22_857044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_857044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857044 prefixEnd_857044 := by exact prefixLift 857044
  have htrace : WordTrace (prefixWord ++ tailWord_857044) baseStart_857044 baseEnd_857044 := by
    simpa [prefixWord, tailWord_857044, baseEnd_857044] using wordTrace_append hprefix tailTrace_857044
  have hstable : (prefixWord ++ tailWord_857044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857044).length < 2 ^ (prefixWord ++ tailWord_857044).sum := by decide
  have hdescent : baseEnd_857044 < baseStart_857044 := by decide
  rcases family_descends (prefixWord ++ tailWord_857044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857074 : List Nat := [3, 2, 1, 5, 1, 2, 8]
def baseStart_857074 : Nat := 118140960795 + 857074 * 2 ^ 59
def prefixEnd_857074 : Nat := 4983230072969 + 3 ^ 40 * 857074 * 2
def baseEnd_857074 : Nat := 10866442431399627845269

theorem tailTrace_857074 : CollatzResearch.WordTrace tailWord_857074 prefixEnd_857074 10866442431399627845269 := by
  unfold tailWord_857074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815014224243687357668569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20840037931316499620449517 7815014224243687357668569)
  ·
    refine ⟨5861260668182765518251427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7815014224243687357668569 5861260668182765518251427)
    ·
      refine ⟨8791891002274148277377141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5861260668182765518251427 8791891002274148277377141)
      ·
        refine ⟨824239781463201401004107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8791891002274148277377141 824239781463201401004107)
        ·
          refine ⟨1236359672194802101506161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824239781463201401004107 1236359672194802101506161)
          ·
            refine ⟨927269754146101576129621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236359672194802101506161 927269754146101576129621)
            ·
              refine ⟨10866442431399627845269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 927269754146101576129621 10866442431399627845269)
              ·
                rfl

theorem cell22_857074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 8].length) (baseStart_857074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857074 prefixEnd_857074 := by exact prefixLift 857074
  have htrace : WordTrace (prefixWord ++ tailWord_857074) baseStart_857074 baseEnd_857074 := by
    simpa [prefixWord, tailWord_857074, baseEnd_857074] using wordTrace_append hprefix tailTrace_857074
  have hstable : (prefixWord ++ tailWord_857074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857074).length < 2 ^ (prefixWord ++ tailWord_857074).sum := by decide
  have hdescent : baseEnd_857074 < baseStart_857074 := by decide
  rcases family_descends (prefixWord ++ tailWord_857074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857089 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_857089 : Nat := 118140960795 + 857089 * 2 ^ 59
def prefixEnd_857089 : Nat := 4983230072969 + 3 ^ 40 * 857089 * 2
def baseEnd_857089 : Nat := 293399080454334912697217

theorem tailTrace_857089 : CollatzResearch.WordTrace tailWord_857089 prefixEnd_857089 293399080454334912697217 := by
  unfold tailWord_857089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31260603991920406992470321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20840402661280271328313547 31260603991920406992470321)
  ·
    refine ⟨23445452993940305244352741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31260603991920406992470321 23445452993940305244352741)
    ·
      refine ⟨4396022436363807233316139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23445452993940305244352741 4396022436363807233316139)
      ·
        refine ⟨6594033654545710849974209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396022436363807233316139 6594033654545710849974209)
        ·
          refine ⟨4945525240909283137480657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594033654545710849974209 4945525240909283137480657)
          ·
            refine ⟨3709143930681962353110493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945525240909283137480657 3709143930681962353110493)
            ·
              refine ⟨1390928974005735882416435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3709143930681962353110493 1390928974005735882416435)
              ·
                refine ⟨2086393461008603823624653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390928974005735882416435 2086393461008603823624653)
                ·
                  refine ⟨782397547878226433859245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2086393461008603823624653 782397547878226433859245)
                  ·
                    refine ⟨293399080454334912697217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782397547878226433859245 293399080454334912697217)
                    ·
                      rfl

theorem cell22_857089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_857089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857089 prefixEnd_857089 := by exact prefixLift 857089
  have htrace : WordTrace (prefixWord ++ tailWord_857089) baseStart_857089 baseEnd_857089 := by
    simpa [prefixWord, tailWord_857089, baseEnd_857089] using wordTrace_append hprefix tailTrace_857089
  have hstable : (prefixWord ++ tailWord_857089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857089).length < 2 ^ (prefixWord ++ tailWord_857089).sum := by decide
  have hdescent : baseEnd_857089 < baseStart_857089 := by decide
  rcases family_descends (prefixWord ++ tailWord_857089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857140 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_857140 : Nat := 118140960795 + 857140 * 2 ^ 59
def prefixEnd_857140 : Nat := 4983230072969 + 3 ^ 40 * 857140 * 2
def baseEnd_857140 : Nat := 293416538796587779672061

theorem tailTrace_857140 : CollatzResearch.WordTrace tailWord_857140 prefixEnd_857140 293416538796587779672061 := by
  unfold tailWord_857140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631232057367821351288437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20841642743157095135051249 15631232057367821351288437)
  ·
    refine ⟨1465428005378233251683291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15631232057367821351288437 1465428005378233251683291)
    ·
      refine ⟨2198142008067349877524937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465428005378233251683291 2198142008067349877524937)
      ·
        refine ⟨1648606506050512408143703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198142008067349877524937 1648606506050512408143703)
        ·
          refine ⟨2472909759075768612215555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648606506050512408143703 2472909759075768612215555)
          ·
            refine ⟨3709364638613652918323333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472909759075768612215555 3709364638613652918323333)
            ·
              refine ⟨695505869740059922185625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3709364638613652918323333 695505869740059922185625)
              ·
                refine ⟨521629402305044941639219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695505869740059922185625 521629402305044941639219)
                ·
                  refine ⟨782444103457567412458829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521629402305044941639219 782444103457567412458829)
                  ·
                    refine ⟨293416538796587779672061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782444103457567412458829 293416538796587779672061)
                    ·
                      rfl

theorem cell22_857140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_857140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857140 prefixEnd_857140 := by exact prefixLift 857140
  have htrace : WordTrace (prefixWord ++ tailWord_857140) baseStart_857140 baseEnd_857140 := by
    simpa [prefixWord, tailWord_857140, baseEnd_857140] using wordTrace_append hprefix tailTrace_857140
  have hstable : (prefixWord ++ tailWord_857140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857140).length < 2 ^ (prefixWord ++ tailWord_857140).sum := by decide
  have hdescent : baseEnd_857140 < baseStart_857140 := by decide
  rcases family_descends (prefixWord ++ tailWord_857140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857162 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_857162 : Nat := 118140960795 + 857162 * 2 ^ 59
def prefixEnd_857162 : Nat := 4983230072969 + 3 ^ 40 * 857162 * 2
def baseEnd_857162 : Nat := 293424069846187055621993

theorem tailTrace_857162 : CollatzResearch.WordTrace tailWord_857162 prefixEnd_857162 293424069846187055621993 := by
  unfold tailWord_857162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815816630163985114969435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20842177680437293639918493 7815816630163985114969435)
  ·
    refine ⟨11723724945245977672454153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815816630163985114969435 11723724945245977672454153)
    ·
      refine ⟨8792793708934483254340615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11723724945245977672454153 8792793708934483254340615)
      ·
        refine ⟨13189190563401724881510923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792793708934483254340615 13189190563401724881510923)
        ·
          refine ⟨19783785845102587322266385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189190563401724881510923 19783785845102587322266385)
          ·
            refine ⟨14837839383826940491699789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19783785845102587322266385 14837839383826940491699789)
            ·
              refine ⟨5564189768935102684387421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14837839383826940491699789 5564189768935102684387421)
              ·
                refine ⟨2086571163350663506645283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5564189768935102684387421 2086571163350663506645283)
                ·
                  refine ⟨3129856745025995259967925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086571163350663506645283 3129856745025995259967925)
                  ·
                    refine ⟨293424069846187055621993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3129856745025995259967925 293424069846187055621993)
                    ·
                      rfl

theorem cell22_857162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_857162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857162 prefixEnd_857162 := by exact prefixLift 857162
  have htrace : WordTrace (prefixWord ++ tailWord_857162) baseStart_857162 baseEnd_857162 := by
    simpa [prefixWord, tailWord_857162, baseEnd_857162] using wordTrace_append hprefix tailTrace_857162
  have hstable : (prefixWord ++ tailWord_857162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857162).length < 2 ^ (prefixWord ++ tailWord_857162).sum := by decide
  have hdescent : baseEnd_857162 < baseStart_857162 := by decide
  rcases family_descends (prefixWord ++ tailWord_857162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857177 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_857177 : Nat := 118140960795 + 857177 * 2 ^ 59
def prefixEnd_857177 : Nat := 4983230072969 + 3 ^ 40 * 857177 * 2
def baseEnd_857177 : Nat := 293429204652732016496947

theorem tailTrace_857177 : CollatzResearch.WordTrace tailWord_857177 prefixEnd_857177 293429204652732016496947 := by
  unfold tailWord_857177
  simp only [CollatzResearch.WordTrace]
  refine ⟨31263813615601598021673785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20842542410401065347782523 31263813615601598021673785)
  ·
    refine ⟨23447860211701198516255339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31263813615601598021673785 23447860211701198516255339)
    ·
      refine ⟨35171790317551797774383009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23447860211701198516255339 35171790317551797774383009)
      ·
        refine ⟨26378842738163848330787257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35171790317551797774383009 26378842738163848330787257)
        ·
          refine ⟨19784132053622886248090443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26378842738163848330787257 19784132053622886248090443)
          ·
            refine ⟨29676198080434329372135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19784132053622886248090443 29676198080434329372135665)
            ·
              refine ⟨22257148560325747029101749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29676198080434329372135665 22257148560325747029101749)
              ·
                refine ⟨2086607677530538783978289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22257148560325747029101749 2086607677530538783978289)
                ·
                  refine ⟨1564955758147904087983717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086607677530538783978289 1564955758147904087983717)
                  ·
                    refine ⟨293429204652732016496947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564955758147904087983717 293429204652732016496947)
                    ·
                      rfl

theorem cell22_857177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_857177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857177 prefixEnd_857177 := by exact prefixLift 857177
  have htrace : WordTrace (prefixWord ++ tailWord_857177) baseStart_857177 baseEnd_857177 := by
    simpa [prefixWord, tailWord_857177, baseEnd_857177] using wordTrace_append hprefix tailTrace_857177
  have hstable : (prefixWord ++ tailWord_857177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857177).length < 2 ^ (prefixWord ++ tailWord_857177).sum := by decide
  have hdescent : baseEnd_857177 < baseStart_857177 := by decide
  rcases family_descends (prefixWord ++ tailWord_857177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857258 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_857258 : Nat := 118140960795 + 857258 * 2 ^ 59
def prefixEnd_857258 : Nat := 4983230072969 + 3 ^ 40 * 857258 * 2
def baseEnd_857258 : Nat := 293456932608074805221699

theorem tailTrace_857258 : CollatzResearch.WordTrace tailWord_857258 prefixEnd_857258 293456932608074805221699 := by
  unfold tailWord_857258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816691982077037213843107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20844511952205432570248285 7816691982077037213843107)
  ·
    refine ⟨11725037973115555820764661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7816691982077037213843107 11725037973115555820764661)
    ·
      refine ⟨1099222309979583358196687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11725037973115555820764661 1099222309979583358196687)
      ·
        refine ⟨1648833464969375037295031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099222309979583358196687 1648833464969375037295031)
        ·
          refine ⟨2473250197454062555942547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648833464969375037295031 2473250197454062555942547)
          ·
            refine ⟨3709875296181093833913821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473250197454062555942547 3709875296181093833913821)
            ·
              refine ⟨1391203236067910187717683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3709875296181093833913821 1391203236067910187717683)
              ·
                refine ⟨2086804854101865281576525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391203236067910187717683 2086804854101865281576525)
                ·
                  refine ⟨782551820288199480591197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2086804854101865281576525 782551820288199480591197)
                  ·
                    refine ⟨293456932608074805221699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782551820288199480591197 293456932608074805221699)
                    ·
                      rfl

theorem cell22_857258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_857258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857258 prefixEnd_857258 := by exact prefixLift 857258
  have htrace : WordTrace (prefixWord ++ tailWord_857258) baseStart_857258 baseEnd_857258 := by
    simpa [prefixWord, tailWord_857258, baseEnd_857258] using wordTrace_append hprefix tailTrace_857258
  have hstable : (prefixWord ++ tailWord_857258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857258).length < 2 ^ (prefixWord ++ tailWord_857258).sum := by decide
  have hdescent : baseEnd_857258 < baseStart_857258 := by decide
  rcases family_descends (prefixWord ++ tailWord_857258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857309 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_857309 : Nat := 118140960795 + 857309 * 2 ^ 59
def prefixEnd_857309 : Nat := 4983230072969 + 3 ^ 40 * 857309 * 2
def baseEnd_857309 : Nat := 293474390950327672196543

theorem tailTrace_857309 : CollatzResearch.WordTrace tailWord_857309 prefixEnd_857309 293474390950327672196543 := by
  unfold tailWord_857309
  simp only [CollatzResearch.WordTrace]
  refine ⟨31268628051123384565478981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20845752034082256376985987 31268628051123384565478981)
  ·
    refine ⟨5862867759585634606027309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31268628051123384565478981 5862867759585634606027309)
    ·
      refine ⟨2198575409844612977260241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5862867759585634606027309 2198575409844612977260241)
      ·
        refine ⟨1648931557383459732945181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198575409844612977260241 1648931557383459732945181)
        ·
          refine ⟨618349334018797399854443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648931557383459732945181 618349334018797399854443)
          ·
            refine ⟨927524001028196099781665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618349334018797399854443 927524001028196099781665)
            ·
              refine ⟨695643000771147074836249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927524001028196099781665 695643000771147074836249)
              ·
                refine ⟨521732250578360306127187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695643000771147074836249 521732250578360306127187)
                ·
                  refine ⟨782598375867540459190781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521732250578360306127187 782598375867540459190781)
                  ·
                    refine ⟨293474390950327672196543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782598375867540459190781 293474390950327672196543)
                    ·
                      rfl

theorem cell22_857309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_857309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857309 prefixEnd_857309 := by exact prefixLift 857309
  have htrace : WordTrace (prefixWord ++ tailWord_857309) baseStart_857309 baseEnd_857309 := by
    simpa [prefixWord, tailWord_857309, baseEnd_857309] using wordTrace_append hprefix tailTrace_857309
  have hstable : (prefixWord ++ tailWord_857309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857309).length < 2 ^ (prefixWord ++ tailWord_857309).sum := by decide
  have hdescent : baseEnd_857309 < baseStart_857309 := by decide
  rcases family_descends (prefixWord ++ tailWord_857309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857331 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 2, 3]
def baseStart_857331 : Nat := 118140960795 + 857331 * 2 ^ 59
def prefixEnd_857331 : Nat := 4983230072969 + 3 ^ 40 * 857331 * 2
def baseEnd_857331 : Nat := 293481921999926948146475

theorem tailTrace_857331 : CollatzResearch.WordTrace tailWord_857331 prefixEnd_857331 293481921999926948146475 := by
  unfold tailWord_857331
  simp only [CollatzResearch.WordTrace]
  refine ⟨31269430457043682322779847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20846286971362454881853231 31269430457043682322779847)
  ·
    refine ⟨46904145685565523484169771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31269430457043682322779847 46904145685565523484169771)
    ·
      refine ⟨70356218528348285226254657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46904145685565523484169771 70356218528348285226254657)
      ·
        refine ⟨52767163896261213919690993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70356218528348285226254657 52767163896261213919690993)
        ·
          refine ⟨39575372922195910439768245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52767163896261213919690993 39575372922195910439768245)
          ·
            refine ⟨3710191211455866603728273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39575372922195910439768245 3710191211455866603728273)
            ·
              refine ⟨2782643408591899952796205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710191211455866603728273 2782643408591899952796205)
              ·
                refine ⟨1043491278221962482298577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782643408591899952796205 1043491278221962482298577)
                ·
                  refine ⟨782618458666471861723933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043491278221962482298577 782618458666471861723933)
                  ·
                    refine ⟨293481921999926948146475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782618458666471861723933 293481921999926948146475)
                    ·
                      rfl

theorem cell22_857331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].length) (baseStart_857331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857331 prefixEnd_857331 := by exact prefixLift 857331
  have htrace : WordTrace (prefixWord ++ tailWord_857331) baseStart_857331 baseEnd_857331 := by
    simpa [prefixWord, tailWord_857331, baseEnd_857331] using wordTrace_append hprefix tailTrace_857331
  have hstable : (prefixWord ++ tailWord_857331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857331).length < 2 ^ (prefixWord ++ tailWord_857331).sum := by decide
  have hdescent : baseEnd_857331 < baseStart_857331 := by decide
  rcases family_descends (prefixWord ++ tailWord_857331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857453 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_857453 : Nat := 118140960795 + 857453 * 2 ^ 59
def prefixEnd_857453 : Nat := 4983230072969 + 3 ^ 40 * 857453 * 2
def baseEnd_857453 : Nat := 293523685093159296596101

theorem tailTrace_857453 : CollatzResearch.WordTrace tailWord_857453 prefixEnd_857453 293523685093159296596101 := by
  unfold tailWord_857453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31273880162601697158721013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20849253441734464772480675 31273880162601697158721013)
  ·
    refine ⟨2931926265243909108630095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31273880162601697158721013 2931926265243909108630095)
    ·
      refine ⟨4397889397865863662945143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931926265243909108630095 4397889397865863662945143)
      ·
        refine ⟨6596834096798795494417715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397889397865863662945143 6596834096798795494417715)
        ·
          refine ⟨9895251145198193241626573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596834096798795494417715 9895251145198193241626573)
          ·
            refine ⟨3710719179449322465609965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9895251145198193241626573 3710719179449322465609965)
            ·
              refine ⟨1391519692293495924603737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710719179449322465609965 1391519692293495924603737)
              ·
                refine ⟨1043639769220121943452803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391519692293495924603737 1043639769220121943452803)
                ·
                  refine ⟨1565459653830182915179205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043639769220121943452803 1565459653830182915179205)
                  ·
                    refine ⟨293523685093159296596101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565459653830182915179205 293523685093159296596101)
                    ·
                      rfl

theorem cell22_857453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_857453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857453 prefixEnd_857453 := by exact prefixLift 857453
  have htrace : WordTrace (prefixWord ++ tailWord_857453) baseStart_857453 baseEnd_857453 := by
    simpa [prefixWord, tailWord_857453, baseEnd_857453] using wordTrace_append hprefix tailTrace_857453
  have hstable : (prefixWord ++ tailWord_857453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857453).length < 2 ^ (prefixWord ++ tailWord_857453).sum := by decide
  have hdescent : baseEnd_857453 < baseStart_857453 := by decide
  rcases family_descends (prefixWord ++ tailWord_857453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857479 : List Nat := [1, 1, 4, 2, 2, 12]
def baseStart_857479 : Nat := 118140960795 + 857479 * 2 ^ 59
def prefixEnd_857479 : Nat := 4983230072969 + 3 ^ 40 * 857479 * 2
def baseEnd_857479 : Nat := 3623859079314862906741

theorem tailTrace_857479 : CollatzResearch.WordTrace tailWord_857479 prefixEnd_857479 3623859079314862906741 := by
  unfold tailWord_857479
  simp only [CollatzResearch.WordTrace]
  refine ⟨31274828460507503599167491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20849885640338335732778327 31274828460507503599167491)
  ·
    refine ⟨46912242690761255398751237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31274828460507503599167491 46912242690761255398751237)
    ·
      refine ⟨8796045504517735387265857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46912242690761255398751237 8796045504517735387265857)
      ·
        refine ⟨6597034128388301540449393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796045504517735387265857 6597034128388301540449393)
        ·
          refine ⟨4947775596291226155337045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597034128388301540449393 4947775596291226155337045)
          ·
            refine ⟨3623859079314862906741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4947775596291226155337045 3623859079314862906741)
            ·
              rfl

theorem cell22_857479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 12].length) (baseStart_857479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857479 prefixEnd_857479 := by exact prefixLift 857479
  have htrace : WordTrace (prefixWord ++ tailWord_857479) baseStart_857479 baseEnd_857479 := by
    simpa [prefixWord, tailWord_857479, baseEnd_857479] using wordTrace_append hprefix tailTrace_857479
  have hstable : (prefixWord ++ tailWord_857479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857479).length < 2 ^ (prefixWord ++ tailWord_857479).sum := by decide
  have hdescent : baseEnd_857479 < baseStart_857479 := by decide
  rcases family_descends (prefixWord ++ tailWord_857479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857483 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 2, 3]
def baseStart_857483 : Nat := 118140960795 + 857483 * 2 ^ 59
def prefixEnd_857483 : Nat := 4983230072969 + 3 ^ 40 * 857483 * 2
def baseEnd_857483 : Nat := 293533954706249218346009

theorem tailTrace_857483 : CollatzResearch.WordTrace tailWord_857483 prefixEnd_857483 293533954706249218346009 := by
  unfold tailWord_857483
  simp only [CollatzResearch.WordTrace]
  refine ⟨31274974352493012282313103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20849982901662008188208735 31274974352493012282313103)
  ·
    refine ⟨46912461528739518423469655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31274974352493012282313103 46912461528739518423469655)
    ·
      refine ⟨70368692293109277635204483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46912461528739518423469655 70368692293109277635204483)
      ·
        refine ⟨105553038439663916452806725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70368692293109277635204483 105553038439663916452806725)
        ·
          refine ⟨19791194707436984334901261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105553038439663916452806725 19791194707436984334901261)
          ·
            refine ⟨7421698015288869125587973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19791194707436984334901261 7421698015288869125587973)
            ·
              refine ⟨1391568377866662961047745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7421698015288869125587973 1391568377866662961047745)
              ·
                refine ⟨1043676283399997220785809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391568377866662961047745 1043676283399997220785809)
                ·
                  refine ⟨782757212549997915589357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043676283399997220785809 782757212549997915589357)
                  ·
                    refine ⟨293533954706249218346009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782757212549997915589357 293533954706249218346009)
                    ·
                      rfl

theorem cell22_857483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].length) (baseStart_857483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857483 prefixEnd_857483 := by exact prefixLift 857483
  have htrace : WordTrace (prefixWord ++ tailWord_857483) baseStart_857483 baseEnd_857483 := by
    simpa [prefixWord, tailWord_857483, baseEnd_857483] using wordTrace_append hprefix tailTrace_857483
  have hstable : (prefixWord ++ tailWord_857483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857483).length < 2 ^ (prefixWord ++ tailWord_857483).sum := by decide
  have hdescent : baseEnd_857483 < baseStart_857483 := by decide
  rcases family_descends (prefixWord ++ tailWord_857483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857500 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_857500 : Nat := 118140960795 + 857500 * 2 ^ 59
def prefixEnd_857500 : Nat := 4983230072969 + 3 ^ 40 * 857500 * 2
def baseEnd_857500 : Nat := 293539774153666840670957

theorem tailTrace_857500 : CollatzResearch.WordTrace tailWord_857500 prefixEnd_857500 293539774153666840670957 := by
  unfold tailWord_857500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15637797196715712092840977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20850396262287616123787969 15637797196715712092840977)
  ·
    refine ⟨11728347897536784069630733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15637797196715712092840977 11728347897536784069630733)
    ·
      refine ⟨4398130461576294026111525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11728347897536784069630733 4398130461576294026111525)
      ·
        refine ⟨824649461545555129895911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4398130461576294026111525 824649461545555129895911)
        ·
          refine ⟨1236974192318332694843867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824649461545555129895911 1236974192318332694843867)
          ·
            refine ⟨1855461288477499042265801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236974192318332694843867 1855461288477499042265801)
            ·
              refine ⟨1391595966358124281699351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855461288477499042265801 1391595966358124281699351)
              ·
                refine ⟨2087393949537186422549027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391595966358124281699351 2087393949537186422549027)
                ·
                  refine ⟨3131090924305779633823541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087393949537186422549027 3131090924305779633823541)
                  ·
                    refine ⟨293539774153666840670957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3131090924305779633823541 293539774153666840670957)
                    ·
                      rfl

theorem cell22_857500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_857500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857500 prefixEnd_857500 := by exact prefixLift 857500
  have htrace : WordTrace (prefixWord ++ tailWord_857500) baseStart_857500 baseEnd_857500 := by
    simpa [prefixWord, tailWord_857500, baseEnd_857500] using wordTrace_append hprefix tailTrace_857500
  have hstable : (prefixWord ++ tailWord_857500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857500).length < 2 ^ (prefixWord ++ tailWord_857500).sum := by decide
  have hdescent : baseEnd_857500 < baseStart_857500 := by decide
  rcases family_descends (prefixWord ++ tailWord_857500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857631 : List Nat := [1, 1, 2, 4, 1, 1, 4, 8]
def baseStart_857631 : Nat := 118140960795 + 857631 * 2 ^ 59
def prefixEnd_857631 : Nat := 4983230072969 + 3 ^ 40 * 857631 * 2
def baseEnd_857631 : Nat := 32620513125647351738395

theorem tailTrace_857631 : CollatzResearch.WordTrace tailWord_857631 prefixEnd_857631 32620513125647351738395 := by
  unfold tailWord_857631
  simp only [CollatzResearch.WordTrace]
  refine ⟨31280372355956833558700747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20853581570637889039133831 31280372355956833558700747)
  ·
    refine ⟨46920558533935250338051121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31280372355956833558700747 46920558533935250338051121)
    ·
      refine ⟨35190418900451437753538341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46920558533935250338051121 35190418900451437753538341)
      ·
        refine ⟨6598203543834644578788439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35190418900451437753538341 6598203543834644578788439)
        ·
          refine ⟨9897305315751966868182659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598203543834644578788439 9897305315751966868182659)
          ·
            refine ⟨14845957973627950302273989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9897305315751966868182659 14845957973627950302273989)
            ·
              refine ⟨2783617120055240681676373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14845957973627950302273989 2783617120055240681676373)
              ·
                refine ⟨32620513125647351738395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2783617120055240681676373 32620513125647351738395)
                ·
                  rfl

theorem cell22_857631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 8].length) (baseStart_857631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857631 prefixEnd_857631 := by exact prefixLift 857631
  have htrace : WordTrace (prefixWord ++ tailWord_857631) baseStart_857631 baseEnd_857631 := by
    simpa [prefixWord, tailWord_857631, baseEnd_857631] using wordTrace_append hprefix tailTrace_857631
  have hstable : (prefixWord ++ tailWord_857631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857631).length < 2 ^ (prefixWord ++ tailWord_857631).sum := by decide
  have hdescent : baseEnd_857631 < baseStart_857631 := by decide
  rcases family_descends (prefixWord ++ tailWord_857631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857633 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_857633 : Nat := 118140960795 + 857633 * 2 ^ 59
def prefixEnd_857633 : Nat := 4983230072969 + 3 ^ 40 * 857633 * 2
def baseEnd_857633 : Nat := 293585302771698827095549

theorem tailTrace_857633 : CollatzResearch.WordTrace tailWord_857633 prefixEnd_857633 293585302771698827095549 := by
  unfold tailWord_857633
  simp only [CollatzResearch.WordTrace]
  refine ⟨31280445301949587900273553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20853630201299725266849035 31280445301949587900273553)
  ·
    refine ⟨23460333976462190925205165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31280445301949587900273553 23460333976462190925205165)
    ·
      refine ⟨8797625241173321596951937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23460333976462190925205165 8797625241173321596951937)
      ·
        refine ⟨6598218930879991197713953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797625241173321596951937 6598218930879991197713953)
        ·
          refine ⟨4948664198159993398285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6598218930879991197713953 4948664198159993398285465)
          ·
            refine ⟨3711498148619995048714099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948664198159993398285465 3711498148619995048714099)
            ·
              refine ⟨5567247222929992573071149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711498148619995048714099 5567247222929992573071149)
              ·
                refine ⟨2087717708598747214901681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5567247222929992573071149 2087717708598747214901681)
                ·
                  refine ⟨1565788281449060411176261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087717708598747214901681 1565788281449060411176261)
                  ·
                    refine ⟨293585302771698827095549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565788281449060411176261 293585302771698827095549)
                    ·
                      rfl

theorem cell22_857633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_857633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857633 prefixEnd_857633 := by exact prefixLift 857633
  have htrace : WordTrace (prefixWord ++ tailWord_857633) baseStart_857633 baseEnd_857633 := by
    simpa [prefixWord, tailWord_857633, baseEnd_857633] using wordTrace_append hprefix tailTrace_857633
  have hstable : (prefixWord ++ tailWord_857633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857633).length < 2 ^ (prefixWord ++ tailWord_857633).sum := by decide
  have hdescent : baseEnd_857633 < baseStart_857633 := by decide
  rcases family_descends (prefixWord ++ tailWord_857633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857697 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_857697 : Nat := 118140960795 + 857697 * 2 ^ 59
def prefixEnd_857697 : Nat := 4983230072969 + 3 ^ 40 * 857697 * 2
def baseEnd_857697 : Nat := 293607211279623993495353

theorem tailTrace_857697 : CollatzResearch.WordTrace tailWord_857697 prefixEnd_857697 293607211279623993495353 := by
  unfold tailWord_857697
  simp only [CollatzResearch.WordTrace]
  refine ⟨31282779573717726830603345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20855186382478484553735563 31282779573717726830603345)
  ·
    refine ⟨23462084680288295122952509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31282779573717726830603345 23462084680288295122952509)
    ·
      refine ⟨8798281755108110671107191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23462084680288295122952509 8798281755108110671107191)
      ·
        refine ⟨13197422632662166006660787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798281755108110671107191 13197422632662166006660787)
        ·
          refine ⟨19796133948993249009991181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197422632662166006660787 19796133948993249009991181)
          ·
            refine ⟨7423550230872468378746693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19796133948993249009991181 7423550230872468378746693)
            ·
              refine ⟨1391915668288587821015005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7423550230872468378746693 1391915668288587821015005)
              ·
                refine ⟨521968375608220432880627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391915668288587821015005 521968375608220432880627)
                ·
                  refine ⟨782952563412330649320941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521968375608220432880627 782952563412330649320941)
                  ·
                    refine ⟨293607211279623993495353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782952563412330649320941 293607211279623993495353)
                    ·
                      rfl

theorem cell22_857697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_857697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857697 prefixEnd_857697 := by exact prefixLift 857697
  have htrace : WordTrace (prefixWord ++ tailWord_857697) baseStart_857697 baseEnd_857697 := by
    simpa [prefixWord, tailWord_857697, baseEnd_857697] using wordTrace_append hprefix tailTrace_857697
  have hstable : (prefixWord ++ tailWord_857697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857697).length < 2 ^ (prefixWord ++ tailWord_857697).sum := by decide
  have hdescent : baseEnd_857697 < baseStart_857697 := by decide
  rcases family_descends (prefixWord ++ tailWord_857697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857710 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_857710 : Nat := 118140960795 + 857710 * 2 ^ 59
def prefixEnd_857710 : Nat := 4983230072969 + 3 ^ 40 * 857710 * 2
def baseEnd_857710 : Nat := 97870553815098764306771

theorem tailTrace_857710 : CollatzResearch.WordTrace tailWord_857710 prefixEnd_857710 97870553815098764306771 := by
  unfold tailWord_857710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910406715333828756353323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20855502481780420033884389 3910406715333828756353323)
  ·
    refine ⟨5865610073000743134529985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910406715333828756353323 5865610073000743134529985)
    ·
      refine ⟨4399207554750557350897489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5865610073000743134529985 4399207554750557350897489)
      ·
        refine ⟨3299405666062918013173117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399207554750557350897489 3299405666062918013173117)
        ·
          refine ⟨1237277124773594254939919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3299405666062918013173117 1237277124773594254939919)
          ·
            refine ⟨1855915687160391382409879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237277124773594254939919 1855915687160391382409879)
            ·
              refine ⟨2783873530740587073614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855915687160391382409879 2783873530740587073614819)
              ·
                refine ⟨4175810296110880610422229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783873530740587073614819 4175810296110880610422229)
                ·
                  refine ⟨97870553815098764306771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4175810296110880610422229 97870553815098764306771)
                  ·
                    rfl

theorem cell22_857710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_857710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857710 prefixEnd_857710 := by exact prefixLift 857710
  have htrace : WordTrace (prefixWord ++ tailWord_857710) baseStart_857710 baseEnd_857710 := by
    simpa [prefixWord, tailWord_857710, baseEnd_857710] using wordTrace_append hprefix tailTrace_857710
  have hstable : (prefixWord ++ tailWord_857710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857710).length < 2 ^ (prefixWord ++ tailWord_857710).sum := by decide
  have hdescent : baseEnd_857710 < baseStart_857710 := by decide
  rcases family_descends (prefixWord ++ tailWord_857710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857740 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_857740 : Nat := 118140960795 + 857740 * 2 ^ 59
def prefixEnd_857740 : Nat := 4983230072969 + 3 ^ 40 * 857740 * 2
def baseEnd_857740 : Nat := 293621931058386214670221

theorem tailTrace_857740 : CollatzResearch.WordTrace tailWord_857740 prefixEnd_857740 293621931058386214670221 := by
  unfold tailWord_857740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642173956280972587209337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856231941707963449612449 15642173956280972587209337)
  ·
    refine ⟨11731630467210729440407003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15642173956280972587209337 11731630467210729440407003)
    ·
      refine ⟨17597445700816094160610505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731630467210729440407003 17597445700816094160610505)
      ·
        refine ⟨13198084275612070620457879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17597445700816094160610505 13198084275612070620457879)
        ·
          refine ⟨19797126413418105930686819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13198084275612070620457879 19797126413418105930686819)
          ·
            refine ⟨29695689620127158896030229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19797126413418105930686819 29695689620127158896030229)
            ·
              refine ⟨1391985450943460573251417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29695689620127158896030229 1391985450943460573251417)
              ·
                refine ⟨1043989088207595429938563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391985450943460573251417 1043989088207595429938563)
                ·
                  refine ⟨1565983632311393144907845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043989088207595429938563 1565983632311393144907845)
                  ·
                    refine ⟨293621931058386214670221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565983632311393144907845 293621931058386214670221)
                    ·
                      rfl

theorem cell22_857740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_857740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857740 prefixEnd_857740 := by exact prefixLift 857740
  have htrace : WordTrace (prefixWord ++ tailWord_857740) baseStart_857740 baseEnd_857740 := by
    simpa [prefixWord, tailWord_857740, baseEnd_857740] using wordTrace_append hprefix tailTrace_857740
  have hstable : (prefixWord ++ tailWord_857740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857740).length < 2 ^ (prefixWord ++ tailWord_857740).sum := by decide
  have hdescent : baseEnd_857740 < baseStart_857740 := by decide
  rcases family_descends (prefixWord ++ tailWord_857740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857748 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_857748 : Nat := 118140960795 + 857748 * 2 ^ 59
def prefixEnd_857748 : Nat := 4983230072969 + 3 ^ 40 * 857748 * 2
def baseEnd_857748 : Nat := 293624669621876860470197

theorem tailTrace_857748 : CollatzResearch.WordTrace tailWord_857748 prefixEnd_857748 293624669621876860470197 := by
  unfold tailWord_857748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15642319848266481270354949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20856426464355308360473265 15642319848266481270354949)
  ·
    refine ⟨2932934971549965238191553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15642319848266481270354949 2932934971549965238191553)
    ·
      refine ⟨2199701228662473928643665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2932934971549965238191553 2199701228662473928643665)
      ·
        refine ⟨1649775921496855446482749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199701228662473928643665 1649775921496855446482749)
        ·
          refine ⟨618665970561320792431031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1649775921496855446482749 618665970561320792431031)
          ·
            refine ⟨927998955841981188646547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618665970561320792431031 927998955841981188646547)
            ·
              refine ⟨1391998433762971782969821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927998955841981188646547 1391998433762971782969821)
              ·
                refine ⟨521999412661114418613683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391998433762971782969821 521999412661114418613683)
                ·
                  refine ⟨782999118991671627920525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521999412661114418613683 782999118991671627920525)
                  ·
                    refine ⟨293624669621876860470197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782999118991671627920525 293624669621876860470197)
                    ·
                      rfl

theorem cell22_857748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_857748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857748 prefixEnd_857748 := by exact prefixLift 857748
  have htrace : WordTrace (prefixWord ++ tailWord_857748) baseStart_857748 baseEnd_857748 := by
    simpa [prefixWord, tailWord_857748, baseEnd_857748] using wordTrace_append hprefix tailTrace_857748
  have hstable : (prefixWord ++ tailWord_857748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857748).length < 2 ^ (prefixWord ++ tailWord_857748).sum := by decide
  have hdescent : baseEnd_857748 < baseStart_857748 := by decide
  rcases family_descends (prefixWord ++ tailWord_857748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857783 : List Nat := [1, 1, 3, 1, 5, 1, 1, 9]
def baseStart_857783 : Nat := 118140960795 + 857783 * 2 ^ 59
def prefixEnd_857783 : Nat := 4983230072969 + 3 ^ 40 * 857783 * 2
def baseEnd_857783 : Nat := 32626294537460937316121

theorem tailTrace_857783 : CollatzResearch.WordTrace tailWord_857783 prefixEnd_857783 32626294537460937316121 := by
  unfold tailWord_857783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31285916251406163518234003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20857277500937442345489335 31285916251406163518234003)
  ·
    refine ⟨46928874377109245277351005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31285916251406163518234003 46928874377109245277351005)
    ·
      refine ⟨17598327891415966979006627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46928874377109245277351005 17598327891415966979006627)
      ·
        refine ⟨26397491837123950468509941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17598327891415966979006627 26397491837123950468509941)
        ·
          refine ⟨2474764859730370356422807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26397491837123950468509941 2474764859730370356422807)
          ·
            refine ⟨3712147289595555534634211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474764859730370356422807 3712147289595555534634211)
            ·
              refine ⟨5568220934393333301951317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712147289595555534634211 5568220934393333301951317)
              ·
                refine ⟨32626294537460937316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5568220934393333301951317 32626294537460937316121)
                ·
                  rfl

theorem cell22_857783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 9].length) (baseStart_857783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857783 prefixEnd_857783 := by exact prefixLift 857783
  have htrace : WordTrace (prefixWord ++ tailWord_857783) baseStart_857783 baseEnd_857783 := by
    simpa [prefixWord, tailWord_857783, baseEnd_857783] using wordTrace_append hprefix tailTrace_857783
  have hstable : (prefixWord ++ tailWord_857783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857783).length < 2 ^ (prefixWord ++ tailWord_857783).sum := by decide
  have hdescent : baseEnd_857783 < baseStart_857783 := by decide
  rcases family_descends (prefixWord ++ tailWord_857783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857802 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_857802 : Nat := 118140960795 + 857802 * 2 ^ 59
def prefixEnd_857802 : Nat := 4983230072969 + 3 ^ 40 * 857802 * 2
def baseEnd_857802 : Nat := 293643154925438719620031

theorem tailTrace_857802 : CollatzResearch.WordTrace tailWord_857802 prefixEnd_857802 293643154925438719620031 := by
  unfold tailWord_857802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7821652309584332440793915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20857739492224886508783773 7821652309584332440793915)
  ·
    refine ⟨11732478464376498661190873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7821652309584332440793915 11732478464376498661190873)
    ·
      refine ⟨8799358848282373995893155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11732478464376498661190873 8799358848282373995893155)
      ·
        refine ⟨13199038272423560993839733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8799358848282373995893155 13199038272423560993839733)
        ·
          refine ⟨1237409838039708843172475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13199038272423560993839733 1237409838039708843172475)
          ·
            refine ⟨1856114757059563264758713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237409838039708843172475 1856114757059563264758713)
            ·
              refine ⟨1392086067794672448569035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856114757059563264758713 1392086067794672448569035)
              ·
                refine ⟨2088129101692008672853553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392086067794672448569035 2088129101692008672853553)
                ·
                  refine ⟨1566096826269006504640165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088129101692008672853553 1566096826269006504640165)
                  ·
                    refine ⟨293643154925438719620031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566096826269006504640165 293643154925438719620031)
                    ·
                      rfl

theorem cell22_857802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_857802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857802 prefixEnd_857802 := by exact prefixLift 857802
  have htrace : WordTrace (prefixWord ++ tailWord_857802) baseStart_857802 baseEnd_857802 := by
    simpa [prefixWord, tailWord_857802, baseEnd_857802] using wordTrace_append hprefix tailTrace_857802
  have hstable : (prefixWord ++ tailWord_857802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857802).length < 2 ^ (prefixWord ++ tailWord_857802).sum := by decide
  have hdescent : baseEnd_857802 < baseStart_857802 := by decide
  rcases family_descends (prefixWord ++ tailWord_857802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857821 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_857821 : Nat := 118140960795 + 857821 * 2 ^ 59
def prefixEnd_857821 : Nat := 4983230072969 + 3 ^ 40 * 857821 * 2
def baseEnd_857821 : Nat := 293649659013729003394973

theorem tailTrace_857821 : CollatzResearch.WordTrace tailWord_857821 prefixEnd_857821 293649659013729003394973 := by
  unfold tailWord_857821
  simp only [CollatzResearch.WordTrace]
  refine ⟨31287302225268496008117317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20858201483512330672078211 31287302225268496008117317)
  ·
    refine ⟨5866369167237843001521997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31287302225268496008117317 5866369167237843001521997)
    ·
      refine ⟨2199888437714191125570749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5866369167237843001521997 2199888437714191125570749)
      ·
        refine ⟨824958164142821672089031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2199888437714191125570749 824958164142821672089031)
        ·
          refine ⟨1237437246214232508133547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824958164142821672089031 1237437246214232508133547)
          ·
            refine ⟨1856155869321348762200321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237437246214232508133547 1856155869321348762200321)
            ·
              refine ⟨1392116901991011571650241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856155869321348762200321 1392116901991011571650241)
              ·
                refine ⟨1044087676493258678737681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392116901991011571650241 1044087676493258678737681)
                ·
                  refine ⟨783065757369944009053261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044087676493258678737681 783065757369944009053261)
                  ·
                    refine ⟨293649659013729003394973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783065757369944009053261 293649659013729003394973)
                    ·
                      rfl

theorem cell22_857821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_857821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857821 prefixEnd_857821 := by exact prefixLift 857821
  have htrace : WordTrace (prefixWord ++ tailWord_857821) baseStart_857821 baseEnd_857821 := by
    simpa [prefixWord, tailWord_857821, baseEnd_857821] using wordTrace_append hprefix tailTrace_857821
  have hstable : (prefixWord ++ tailWord_857821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857821).length < 2 ^ (prefixWord ++ tailWord_857821).sum := by decide
  have hdescent : baseEnd_857821 < baseStart_857821 := by decide
  rcases family_descends (prefixWord ++ tailWord_857821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857843 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_857843 : Nat := 118140960795 + 857843 * 2 ^ 59
def prefixEnd_857843 : Nat := 4983230072969 + 3 ^ 40 * 857843 * 2
def baseEnd_857843 : Nat := 293657190063328279344905

theorem tailTrace_857843 : CollatzResearch.WordTrace tailWord_857843 prefixEnd_857843 293657190063328279344905 := by
  unfold tailWord_857843
  simp only [CollatzResearch.WordTrace]
  refine ⟨31288104631188793765418183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20858736420792529176945455 31288104631188793765418183)
  ·
    refine ⟨46932156946783190648127275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31288104631188793765418183 46932156946783190648127275)
    ·
      refine ⟨70398235420174785972190913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46932156946783190648127275 70398235420174785972190913)
      ·
        refine ⟨52798676565131089479143185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70398235420174785972190913 52798676565131089479143185)
        ·
          refine ⟨39599007423848317109357389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52798676565131089479143185 39599007423848317109357389)
          ·
            refine ⟨14849627783943118916009021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39599007423848317109357389 14849627783943118916009021)
            ·
              refine ⟨5568610418978669593503383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14849627783943118916009021 5568610418978669593503383)
              ·
                refine ⟨8352915628468004390255075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568610418978669593503383 8352915628468004390255075)
                ·
                  refine ⟨12529373442702006585382613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8352915628468004390255075 12529373442702006585382613)
                  ·
                    refine ⟨293657190063328279344905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12529373442702006585382613 293657190063328279344905)
                    ·
                      rfl

theorem cell22_857843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_857843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857843 prefixEnd_857843 := by exact prefixLift 857843
  have htrace : WordTrace (prefixWord ++ tailWord_857843) baseStart_857843 baseEnd_857843 := by
    simpa [prefixWord, tailWord_857843, baseEnd_857843] using wordTrace_append hprefix tailTrace_857843
  have hstable : (prefixWord ++ tailWord_857843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857843).length < 2 ^ (prefixWord ++ tailWord_857843).sum := by decide
  have hdescent : baseEnd_857843 < baseStart_857843 := by decide
  rcases family_descends (prefixWord ++ tailWord_857843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857873 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 10]
def baseStart_857873 : Nat := 118140960795 + 857873 * 2 ^ 59
def prefixEnd_857873 : Nat := 4983230072969 + 3 ^ 40 * 857873 * 2
def baseEnd_857873 : Nat := 97889153225472733698271

theorem tailTrace_857873 : CollatzResearch.WordTrace tailWord_857873 prefixEnd_857873 97889153225472733698271 := by
  unfold tailWord_857873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289198821080108889010273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20859465880720072592673515 31289198821080108889010273)
  ·
    refine ⟨23466899115810081666757705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31289198821080108889010273 23466899115810081666757705)
    ·
      refine ⟨17600174336857561250068279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23466899115810081666757705 17600174336857561250068279)
      ·
        refine ⟨26400261505286341875102419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17600174336857561250068279 26400261505286341875102419)
        ·
          refine ⟨39600392257929512812653629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26400261505286341875102419 39600392257929512812653629)
          ·
            refine ⟨14850147096723567304745111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39600392257929512812653629 14850147096723567304745111)
            ·
              refine ⟨22275220645085350957117667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14850147096723567304745111 22275220645085350957117667)
              ·
                refine ⟨33412830967628026435676501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22275220645085350957117667 33412830967628026435676501)
                ·
                  refine ⟨97889153225472733698271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 33412830967628026435676501 97889153225472733698271)
                  ·
                    rfl

theorem cell22_857873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_857873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857873 prefixEnd_857873 := by exact prefixLift 857873
  have htrace : WordTrace (prefixWord ++ tailWord_857873) baseStart_857873 baseEnd_857873 := by
    simpa [prefixWord, tailWord_857873, baseEnd_857873] using wordTrace_append hprefix tailTrace_857873
  have hstable : (prefixWord ++ tailWord_857873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857873).length < 2 ^ (prefixWord ++ tailWord_857873).sum := by decide
  have hdescent : baseEnd_857873 < baseStart_857873 := by decide
  rcases family_descends (prefixWord ++ tailWord_857873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857909 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_857909 : Nat := 118140960795 + 857909 * 2 ^ 59
def prefixEnd_857909 : Nat := 4983230072969 + 3 ^ 40 * 857909 * 2
def baseEnd_857909 : Nat := 293679783212126107194703

theorem tailTrace_857909 : CollatzResearch.WordTrace tailWord_857909 prefixEnd_857909 293679783212126107194703 := by
  unfold tailWord_857909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31290511848949687037320781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20860341232633124691547187 31290511848949687037320781)
  ·
    refine ⟨11733941943356132638995293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31290511848949687037320781 11733941943356132638995293)
    ·
      refine ⟨4400228228758549739623235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11733941943356132638995293 4400228228758549739623235)
      ·
        refine ⟨6600342343137824609434853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4400228228758549739623235 6600342343137824609434853)
        ·
          refine ⟨1237564189338342114269035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6600342343137824609434853 1237564189338342114269035)
          ·
            refine ⟨1856346284007513171403553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237564189338342114269035 1856346284007513171403553)
            ·
              refine ⟨1392259713005634878552665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1856346284007513171403553 1392259713005634878552665)
              ·
                refine ⟨1044194784754226158914499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392259713005634878552665 1044194784754226158914499)
                ·
                  refine ⟨1566292177131339238371749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044194784754226158914499 1566292177131339238371749)
                  ·
                    refine ⟨293679783212126107194703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566292177131339238371749 293679783212126107194703)
                    ·
                      rfl

theorem cell22_857909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_857909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857909 prefixEnd_857909 := by exact prefixLift 857909
  have htrace : WordTrace (prefixWord ++ tailWord_857909) baseStart_857909 baseEnd_857909 := by
    simpa [prefixWord, tailWord_857909, baseEnd_857909] using wordTrace_append hprefix tailTrace_857909
  have hstable : (prefixWord ++ tailWord_857909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857909).length < 2 ^ (prefixWord ++ tailWord_857909).sum := by decide
  have hdescent : baseEnd_857909 < baseStart_857909 := by decide
  rcases family_descends (prefixWord ++ tailWord_857909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857926 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_857926 : Nat := 118140960795 + 857926 * 2 ^ 59
def prefixEnd_857926 : Nat := 4983230072969 + 3 ^ 40 * 857926 * 2
def baseEnd_857926 : Nat := 293685602659543729519651

theorem tailTrace_857926 : CollatzResearch.WordTrace tailWord_857926 prefixEnd_857926 293685602659543729519651 := by
  unfold tailWord_857926
  simp only [CollatzResearch.WordTrace]
  refine ⟨977847871559003091896551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20860754593258732627126421 977847871559003091896551)
  ·
    refine ⟨1466771807338504637844827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977847871559003091896551 1466771807338504637844827)
    ·
      refine ⟨2200157711007756956767241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466771807338504637844827 2200157711007756956767241)
      ·
        refine ⟨1650118283255817717575431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200157711007756956767241 1650118283255817717575431)
        ·
          refine ⟨2475177424883726576363147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650118283255817717575431 2475177424883726576363147)
          ·
            refine ⟨3712766137325589864544721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475177424883726576363147 3712766137325589864544721)
            ·
              refine ⟨2784574602994192398408541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3712766137325589864544721 2784574602994192398408541)
              ·
                refine ⟨1044215476122822149403203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2784574602994192398408541 1044215476122822149403203)
                ·
                  refine ⟨1566323214184233224104805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044215476122822149403203 1566323214184233224104805)
                  ·
                    refine ⟨293685602659543729519651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566323214184233224104805 293685602659543729519651)
                    ·
                      rfl

theorem cell22_857926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_857926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857926 prefixEnd_857926 := by exact prefixLift 857926
  have htrace : WordTrace (prefixWord ++ tailWord_857926) baseStart_857926 baseEnd_857926 := by
    simpa [prefixWord, tailWord_857926, baseEnd_857926] using wordTrace_append hprefix tailTrace_857926
  have hstable : (prefixWord ++ tailWord_857926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857926).length < 2 ^ (prefixWord ++ tailWord_857926).sum := by decide
  have hdescent : baseEnd_857926 < baseStart_857926 := by decide
  rcases family_descends (prefixWord ++ tailWord_857926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857937 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_857937 : Nat := 118140960795 + 857937 * 2 ^ 59
def prefixEnd_857937 : Nat := 4983230072969 + 3 ^ 40 * 857937 * 2
def baseEnd_857937 : Nat := 293689368184343367494617

theorem tailTrace_857937 : CollatzResearch.WordTrace tailWord_857937 prefixEnd_857937 293689368184343367494617 := by
  unfold tailWord_857937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291533092848247819340065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20861022061898831879560043 31291533092848247819340065)
  ·
    refine ⟨23468649819636185864505049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31291533092848247819340065 23468649819636185864505049)
    ·
      refine ⟨17601487364727139398378787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23468649819636185864505049 17601487364727139398378787)
      ·
        refine ⟨26402231047090709097568181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17601487364727139398378787 26402231047090709097568181)
        ·
          refine ⟨2475209160664753977897017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26402231047090709097568181 2475209160664753977897017)
          ·
            refine ⟨1856406870498565483422763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2475209160664753977897017 1856406870498565483422763)
            ·
              refine ⟨2784610305747848225134145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856406870498565483422763 2784610305747848225134145)
              ·
                refine ⟨2088457729310886168850609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784610305747848225134145 2088457729310886168850609)
                ·
                  refine ⟨1566343296983164626637957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088457729310886168850609 1566343296983164626637957)
                  ·
                    refine ⟨293689368184343367494617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566343296983164626637957 293689368184343367494617)
                    ·
                      rfl

theorem cell22_857937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_857937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857937 prefixEnd_857937 := by exact prefixLift 857937
  have htrace : WordTrace (prefixWord ++ tailWord_857937) baseStart_857937 baseEnd_857937 := by
    simpa [prefixWord, tailWord_857937, baseEnd_857937] using wordTrace_append hprefix tailTrace_857937
  have hstable : (prefixWord ++ tailWord_857937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857937).length < 2 ^ (prefixWord ++ tailWord_857937).sum := by decide
  have hdescent : baseEnd_857937 < baseStart_857937 := by decide
  rcases family_descends (prefixWord ++ tailWord_857937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857984 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_857984 : Nat := 118140960795 + 857984 * 2 ^ 59
def prefixEnd_857984 : Nat := 4983230072969 + 3 ^ 40 * 857984 * 2
def baseEnd_857984 : Nat := 293705457244850911569473

theorem tailTrace_857984 : CollatzResearch.WordTrace tailWord_857984 prefixEnd_857984 293705457244850911569473 := by
  unfold tailWord_857984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646623661838987423150503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20862164882451983230867337 15646623661838987423150503)
  ·
    refine ⟨23469935492758481134725755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15646623661838987423150503 23469935492758481134725755)
    ·
      refine ⟨35204903239137721702088633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23469935492758481134725755 35204903239137721702088633)
      ·
        refine ⟨26403677429353291276566475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35204903239137721702088633 26403677429353291276566475)
        ·
          refine ⟨39605516144029936914849713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26403677429353291276566475 39605516144029936914849713)
          ·
            refine ⟨29704137108022452686137285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39605516144029936914849713 29704137108022452686137285)
            ·
              refine ⟨5569525707754209878650741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29704137108022452686137285 5569525707754209878650741)
              ·
                refine ⟨522143035101957176123507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5569525707754209878650741 522143035101957176123507)
                ·
                  refine ⟨783214552652935764185261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522143035101957176123507 783214552652935764185261)
                  ·
                    refine ⟨293705457244850911569473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783214552652935764185261 293705457244850911569473)
                    ·
                      rfl

theorem cell22_857984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_857984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857984 prefixEnd_857984 := by exact prefixLift 857984
  have htrace : WordTrace (prefixWord ++ tailWord_857984) baseStart_857984 baseEnd_857984 := by
    simpa [prefixWord, tailWord_857984, baseEnd_857984] using wordTrace_append hprefix tailTrace_857984
  have hstable : (prefixWord ++ tailWord_857984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857984).length < 2 ^ (prefixWord ++ tailWord_857984).sum := by decide
  have hdescent : baseEnd_857984 < baseStart_857984 := by decide
  rcases family_descends (prefixWord ++ tailWord_857984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857995 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_857995 : Nat := 118140960795 + 857995 * 2 ^ 59
def prefixEnd_857995 : Nat := 4983230072969 + 3 ^ 40 * 857995 * 2
def baseEnd_857995 : Nat := 293709222769650549544439

theorem tailTrace_857995 : CollatzResearch.WordTrace tailWord_857995 prefixEnd_857995 293709222769650549544439 := by
  unfold tailWord_857995
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293648526638123724951439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20862432351092082483300959 31293648526638123724951439)
  ·
    refine ⟨46940472789957185587427159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31293648526638123724951439 46940472789957185587427159)
    ·
      refine ⟨70410709184935778381140739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46940472789957185587427159 70410709184935778381140739)
      ·
        refine ⟨105616063777403667571711109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70410709184935778381140739 105616063777403667571711109)
        ·
          refine ⟨19803011958263187669695833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105616063777403667571711109 19803011958263187669695833)
          ·
            refine ⟨14852258968697390752271875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19803011958263187669695833 14852258968697390752271875)
            ·
              refine ⟨22278388453046086128407813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14852258968697390752271875 22278388453046086128407813)
              ·
                refine ⟨4177197834946141149076465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22278388453046086128407813 4177197834946141149076465)
                ·
                  refine ⟨3132898376209605861807349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177197834946141149076465 3132898376209605861807349)
                  ·
                    refine ⟨293709222769650549544439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3132898376209605861807349 293709222769650549544439)
                    ·
                      rfl

theorem cell22_857995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_857995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_857995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_857995 prefixEnd_857995 := by exact prefixLift 857995
  have htrace : WordTrace (prefixWord ++ tailWord_857995) baseStart_857995 baseEnd_857995 := by
    simpa [prefixWord, tailWord_857995, baseEnd_857995] using wordTrace_append hprefix tailTrace_857995
  have hstable : (prefixWord ++ tailWord_857995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857995).length < 2 ^ (prefixWord ++ tailWord_857995).sum := by decide
  have hdescent : baseEnd_857995 < baseStart_857995 := by decide
  rcases family_descends (prefixWord ++ tailWord_857995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858001 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_858001 : Nat := 118140960795 + 858001 * 2 ^ 59
def prefixEnd_858001 : Nat := 4983230072969 + 3 ^ 40 * 858001 * 2
def baseEnd_858001 : Nat := 293711276692268533894421

theorem tailTrace_858001 : CollatzResearch.WordTrace tailWord_858001 prefixEnd_858001 293711276692268533894421 := by
  unfold tailWord_858001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293867364616386749669857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20862578243077591166446571 31293867364616386749669857)
  ·
    refine ⟨23470400523462290062252393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31293867364616386749669857 23470400523462290062252393)
    ·
      refine ⟨17602800392596717546689295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23470400523462290062252393 17602800392596717546689295)
      ·
        refine ⟨26404200588895076320033943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17602800392596717546689295 26404200588895076320033943)
        ·
          refine ⟨39606300883342614480050915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26404200588895076320033943 39606300883342614480050915)
          ·
            refine ⟨59409451325013921720076373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39606300883342614480050915 59409451325013921720076373)
            ·
              refine ⟨696204507715006895157145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 59409451325013921720076373 696204507715006895157145)
              ·
                refine ⟨522153380786255171367859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696204507715006895157145 522153380786255171367859)
                ·
                  refine ⟨783230071179382757051789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522153380786255171367859 783230071179382757051789)
                  ·
                    refine ⟨293711276692268533894421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783230071179382757051789 293711276692268533894421)
                    ·
                      rfl

theorem cell22_858001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_858001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858001 prefixEnd_858001 := by exact prefixLift 858001
  have htrace : WordTrace (prefixWord ++ tailWord_858001) baseStart_858001 baseEnd_858001 := by
    simpa [prefixWord, tailWord_858001, baseEnd_858001] using wordTrace_append hprefix tailTrace_858001
  have hstable : (prefixWord ++ tailWord_858001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858001).length < 2 ^ (prefixWord ++ tailWord_858001).sum := by decide
  have hdescent : baseEnd_858001 < baseStart_858001 := by decide
  rcases family_descends (prefixWord ++ tailWord_858001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858012 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_858012 : Nat := 118140960795 + 858012 * 2 ^ 59
def prefixEnd_858012 : Nat := 4983230072969 + 3 ^ 40 * 858012 * 2
def baseEnd_858012 : Nat := 293715042217068171869387

theorem tailTrace_858012 : CollatzResearch.WordTrace tailWord_858012 prefixEnd_858012 293715042217068171869387 := by
  unfold tailWord_858012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647134283788267814160145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20862845711717690418880193 15647134283788267814160145)
  ·
    refine ⟨11735350712841200860620109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15647134283788267814160145 11735350712841200860620109)
    ·
      refine ⟨4400756517315450322732541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11735350712841200860620109 4400756517315450322732541)
      ·
        refine ⟨1650283693993293871024703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4400756517315450322732541 1650283693993293871024703)
        ·
          refine ⟨2475425540989940806537055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650283693993293871024703 2475425540989940806537055)
          ·
            refine ⟨3713138311484911209805583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475425540989940806537055 3713138311484911209805583)
            ·
              refine ⟨5569707467227366814708375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713138311484911209805583 5569707467227366814708375)
              ·
                refine ⟨8354561200841050222062563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5569707467227366814708375 8354561200841050222062563)
                ·
                  refine ⟨12531841801261575333093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8354561200841050222062563 12531841801261575333093845)
                  ·
                    refine ⟨293715042217068171869387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12531841801261575333093845 293715042217068171869387)
                    ·
                      rfl

theorem cell22_858012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_858012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858012 prefixEnd_858012 := by exact prefixLift 858012
  have htrace : WordTrace (prefixWord ++ tailWord_858012) baseStart_858012 baseEnd_858012 := by
    simpa [prefixWord, tailWord_858012, baseEnd_858012] using wordTrace_append hprefix tailTrace_858012
  have hstable : (prefixWord ++ tailWord_858012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858012).length < 2 ^ (prefixWord ++ tailWord_858012).sum := by decide
  have hdescent : baseEnd_858012 < baseStart_858012 := by decide
  rcases family_descends (prefixWord ++ tailWord_858012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858057 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_858057 : Nat := 118140960795 + 858057 * 2 ^ 59
def prefixEnd_858057 : Nat := 4983230072969 + 3 ^ 40 * 858057 * 2
def baseEnd_858057 : Nat := 293730446636703054494249

theorem tailTrace_858057 : CollatzResearch.WordTrace tailWord_858057 prefixEnd_858057 293730446636703054494249 := by
  unfold tailWord_858057
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295909852413508313708425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20863939901609005542472283 31295909852413508313708425)
  ·
    refine ⟨23471932389310131235281319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31295909852413508313708425 23471932389310131235281319)
    ·
      refine ⟨35207898583965196852921979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23471932389310131235281319 35207898583965196852921979)
      ·
        refine ⟨52811847875947795279382969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35207898583965196852921979 52811847875947795279382969)
        ·
          refine ⟨39608885906960846459537227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52811847875947795279382969 39608885906960846459537227)
          ·
            refine ⟨59413328860441269689305841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39608885906960846459537227 59413328860441269689305841)
            ·
              refine ⟨44559996645330952266979381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59413328860441269689305841 44559996645330952266979381)
              ·
                refine ⟨4177499685499776775029317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44559996645330952266979381 4177499685499776775029317)
                ·
                  refine ⟨783281191031208145317997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4177499685499776775029317 783281191031208145317997)
                  ·
                    refine ⟨293730446636703054494249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783281191031208145317997 293730446636703054494249)
                    ·
                      rfl

theorem cell22_858057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_858057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858057 prefixEnd_858057 := by exact prefixLift 858057
  have htrace : WordTrace (prefixWord ++ tailWord_858057) baseStart_858057 baseEnd_858057 := by
    simpa [prefixWord, tailWord_858057, baseEnd_858057] using wordTrace_append hprefix tailTrace_858057
  have hstable : (prefixWord ++ tailWord_858057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858057).length < 2 ^ (prefixWord ++ tailWord_858057).sum := by decide
  have hdescent : baseEnd_858057 < baseStart_858057 := by decide
  rcases family_descends (prefixWord ++ tailWord_858057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858166 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_858166 : Nat := 118140960795 + 858166 * 2 ^ 59
def prefixEnd_858166 : Nat := 4983230072969 + 3 ^ 40 * 858166 * 2
def baseEnd_858166 : Nat := 97922586521421034506305

theorem tailTrace_858166 : CollatzResearch.WordTrace tailWord_858166 prefixEnd_858166 97922586521421034506305 := by
  unfold tailWord_858166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956242838063663745589147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20866590272679079952950901 1956242838063663745589147)
  ·
    refine ⟨2934364257095495618383721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956242838063663745589147 2934364257095495618383721)
    ·
      refine ⟨2200773192821621713787791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2934364257095495618383721 2200773192821621713787791)
      ·
        refine ⟨3301159789232432570681687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200773192821621713787791 3301159789232432570681687)
        ·
          refine ⟨4951739683848648856022531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301159789232432570681687 4951739683848648856022531)
          ·
            refine ⟨7427609525772973284033797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951739683848648856022531 7427609525772973284033797)
            ·
              refine ⟨1392676786082432490756337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7427609525772973284033797 1392676786082432490756337)
              ·
                refine ⟨1044507589561824368067253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392676786082432490756337 1044507589561824368067253)
                ·
                  refine ⟨97922586521421034506305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1044507589561824368067253 97922586521421034506305)
                  ·
                    rfl

theorem cell22_858166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_858166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858166 prefixEnd_858166 := by exact prefixLift 858166
  have htrace : WordTrace (prefixWord ++ tailWord_858166) baseStart_858166 baseEnd_858166 := by
    simpa [prefixWord, tailWord_858166, baseEnd_858166] using wordTrace_append hprefix tailTrace_858166
  have hstable : (prefixWord ++ tailWord_858166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858166).length < 2 ^ (prefixWord ++ tailWord_858166).sum := by decide
  have hdescent : baseEnd_858166 < baseStart_858166 := by decide
  rcases family_descends (prefixWord ++ tailWord_858166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858209 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_858209 : Nat := 118140960795 + 858209 * 2 ^ 59
def prefixEnd_858209 : Nat := 4983230072969 + 3 ^ 40 * 858209 * 2
def baseEnd_858209 : Nat := 293782479343025324693783

theorem tailTrace_858209 : CollatzResearch.WordTrace tailWord_858209 prefixEnd_858209 293782479343025324693783 := by
  unfold tailWord_858209
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301453747862838273241681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20867635831908558848827787 31301453747862838273241681)
  ·
    refine ⟨23476090310897128704931261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31301453747862838273241681 23476090310897128704931261)
    ·
      refine ⟨8803533866586423264349223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23476090310897128704931261 8803533866586423264349223)
      ·
        refine ⟨13205300799879634896523835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803533866586423264349223 13205300799879634896523835)
        ·
          refine ⟨19807951199819452344785753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205300799879634896523835 19807951199819452344785753)
          ·
            refine ⟨14855963399864589258589315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19807951199819452344785753 14855963399864589258589315)
            ·
              refine ⟨22283945099796883887883973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14855963399864589258589315 22283945099796883887883973)
              ·
                refine ⟨4178239706211915728978245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22283945099796883887883973 4178239706211915728978245)
                ·
                  refine ⟨783419944914734199183421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4178239706211915728978245 783419944914734199183421)
                  ·
                    refine ⟨293782479343025324693783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783419944914734199183421 293782479343025324693783)
                    ·
                      rfl

theorem cell22_858209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_858209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858209 prefixEnd_858209 := by exact prefixLift 858209
  have htrace : WordTrace (prefixWord ++ tailWord_858209) baseStart_858209 baseEnd_858209 := by
    simpa [prefixWord, tailWord_858209, baseEnd_858209] using wordTrace_append hprefix tailTrace_858209
  have hstable : (prefixWord ++ tailWord_858209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858209).length < 2 ^ (prefixWord ++ tailWord_858209).sum := by decide
  have hdescent : baseEnd_858209 < baseStart_858209 := by decide
  rcases family_descends (prefixWord ++ tailWord_858209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858213 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_858213 : Nat := 118140960795 + 858213 * 2 ^ 59
def prefixEnd_858213 : Nat := 4983230072969 + 3 ^ 40 * 858213 * 2
def baseEnd_858213 : Nat := 293783848624770647593771

theorem tailTrace_858213 : CollatzResearch.WordTrace tailWord_858213 prefixEnd_858213 293783848624770647593771 := by
  unfold tailWord_858213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301599639848346956387293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20867733093232231304258195 31301599639848346956387293)
  ·
    refine ⟨11738099864943130108645235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31301599639848346956387293 11738099864943130108645235)
    ·
      refine ⟨17607149797414695162967853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738099864943130108645235 17607149797414695162967853)
      ·
        refine ⟨6602681174030510686112945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17607149797414695162967853 6602681174030510686112945)
        ·
          refine ⟨4952010880522883014584709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602681174030510686112945 4952010880522883014584709)
          ·
            refine ⟨928502040098040565234633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4952010880522883014584709 928502040098040565234633)
            ·
              refine ⟨696376530073530423925975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928502040098040565234633 696376530073530423925975)
              ·
                refine ⟨1044564795110295635888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696376530073530423925975 1044564795110295635888963)
                ·
                  refine ⟨1566847192665443453833445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044564795110295635888963 1566847192665443453833445)
                  ·
                    refine ⟨293783848624770647593771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1566847192665443453833445 293783848624770647593771)
                    ·
                      rfl

theorem cell22_858213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_858213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858213 prefixEnd_858213 := by exact prefixLift 858213
  have htrace : WordTrace (prefixWord ++ tailWord_858213) baseStart_858213 baseEnd_858213 := by
    simpa [prefixWord, tailWord_858213, baseEnd_858213] using wordTrace_append hprefix tailTrace_858213
  have hstable : (prefixWord ++ tailWord_858213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858213).length < 2 ^ (prefixWord ++ tailWord_858213).sum := by decide
  have hdescent : baseEnd_858213 < baseStart_858213 := by decide
  rcases family_descends (prefixWord ++ tailWord_858213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858226 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_858226 : Nat := 118140960795 + 858226 * 2 ^ 59
def prefixEnd_858226 : Nat := 4983230072969 + 3 ^ 40 * 858226 * 2
def baseEnd_858226 : Nat := 293788298790442947018731

theorem tailTrace_858226 : CollatzResearch.WordTrace tailWord_858226 prefixEnd_858226 293788298790442947018731 := by
  unfold tailWord_858226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825518447200312544152633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20868049192534166784407021 7825518447200312544152633)
  ·
    refine ⟨5869138835400234408114475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7825518447200312544152633 5869138835400234408114475)
    ·
      refine ⟨8803708253100351612171713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869138835400234408114475 8803708253100351612171713)
      ·
        refine ⟨6602781189825263709128785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8803708253100351612171713 6602781189825263709128785)
        ·
          refine ⟨4952085892368947781846589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602781189825263709128785 4952085892368947781846589)
          ·
            refine ⟨1857032209638355418192471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4952085892368947781846589 1857032209638355418192471)
            ·
              refine ⟨2785548314457533127288707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857032209638355418192471 2785548314457533127288707)
              ·
                refine ⟨4178322471686299690933061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785548314457533127288707 4178322471686299690933061)
                ·
                  refine ⟨783435463441181192049949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4178322471686299690933061 783435463441181192049949)
                  ·
                    refine ⟨293788298790442947018731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783435463441181192049949 293788298790442947018731)
                    ·
                      rfl

theorem cell22_858226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_858226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858226 prefixEnd_858226 := by exact prefixLift 858226
  have htrace : WordTrace (prefixWord ++ tailWord_858226) baseStart_858226 baseEnd_858226 := by
    simpa [prefixWord, tailWord_858226, baseEnd_858226] using wordTrace_append hprefix tailTrace_858226
  have hstable : (prefixWord ++ tailWord_858226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858226).length < 2 ^ (prefixWord ++ tailWord_858226).sum := by decide
  have hdescent : baseEnd_858226 < baseStart_858226 := by decide
  rcases family_descends (prefixWord ++ tailWord_858226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858243 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 2, 3]
def baseStart_858243 : Nat := 118140960795 + 858243 * 2 ^ 59
def prefixEnd_858243 : Nat := 4983230072969 + 3 ^ 40 * 858243 * 2
def baseEnd_858243 : Nat := 293794118237860569343679

theorem tailTrace_858243 : CollatzResearch.WordTrace tailWord_858243 prefixEnd_858243 293794118237860569343679 := by
  unfold tailWord_858243
  simp only [CollatzResearch.WordTrace]
  refine ⟨31302693829739662079979383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20868462553159774719986255 31302693829739662079979383)
  ·
    refine ⟨46954040744609493119969075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31302693829739662079979383 46954040744609493119969075)
    ·
      refine ⟨70431061116914239679953613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46954040744609493119969075 70431061116914239679953613)
      ·
        refine ⟨26411647918842839879982605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70431061116914239679953613 26411647918842839879982605)
        ·
          refine ⟨9904367969566064954993477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26411647918842839879982605 9904367969566064954993477)
          ·
            refine ⟨1857068994293637179061277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9904367969566064954993477 1857068994293637179061277)
            ·
              refine ⟨696400872860113942147979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1857068994293637179061277 696400872860113942147979)
              ·
                refine ⟨1044601309290170913221969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696400872860113942147979 1044601309290170913221969)
                ·
                  refine ⟨783450981967628184916477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044601309290170913221969 783450981967628184916477)
                  ·
                    refine ⟨293794118237860569343679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783450981967628184916477 293794118237860569343679)
                    ·
                      rfl

theorem cell22_858243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 3].length) (baseStart_858243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858243 prefixEnd_858243 := by exact prefixLift 858243
  have htrace : WordTrace (prefixWord ++ tailWord_858243) baseStart_858243 baseEnd_858243 := by
    simpa [prefixWord, tailWord_858243, baseEnd_858243] using wordTrace_append hprefix tailTrace_858243
  have hstable : (prefixWord ++ tailWord_858243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858243).length < 2 ^ (prefixWord ++ tailWord_858243).sum := by decide
  have hdescent : baseEnd_858243 < baseStart_858243 := by decide
  rcases family_descends (prefixWord ++ tailWord_858243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858267 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 9]
def baseStart_858267 : Nat := 118140960795 + 858267 * 2 ^ 59
def prefixEnd_858267 : Nat := 4983230072969 + 3 ^ 40 * 858267 * 2
def baseEnd_858267 : Nat := 97934111309444168914535

theorem tailTrace_858267 : CollatzResearch.WordTrace tailWord_858267 prefixEnd_858267 97934111309444168914535 := by
  unfold tailWord_858267
  simp only [CollatzResearch.WordTrace]
  refine ⟨31303569181652714178853055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20869046121101809452568703 31303569181652714178853055)
  ·
    refine ⟨46955353772479071268279583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31303569181652714178853055 46955353772479071268279583)
    ·
      refine ⟨70433030658718606902419375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46955353772479071268279583 70433030658718606902419375)
      ·
        refine ⟨105649545988077910353629063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70433030658718606902419375 105649545988077910353629063)
        ·
          refine ⟨158474318982116865530443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105649545988077910353629063 158474318982116865530443595)
          ·
            refine ⟨237711478473175298295665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158474318982116865530443595 237711478473175298295665393)
            ·
              refine ⟨178283608854881473721749045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237711478473175298295665393 178283608854881473721749045)
              ·
                refine ⟨16714088330145138161413973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178283608854881473721749045 16714088330145138161413973)
                ·
                  refine ⟨97934111309444168914535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16714088330145138161413973 97934111309444168914535)
                  ·
                    rfl

theorem cell22_858267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_858267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858267 prefixEnd_858267 := by exact prefixLift 858267
  have htrace : WordTrace (prefixWord ++ tailWord_858267) baseStart_858267 baseEnd_858267 := by
    simpa [prefixWord, tailWord_858267, baseEnd_858267] using wordTrace_append hprefix tailTrace_858267
  have hstable : (prefixWord ++ tailWord_858267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858267).length < 2 ^ (prefixWord ++ tailWord_858267).sum := by decide
  have hdescent : baseEnd_858267 < baseStart_858267 := by decide
  rcases family_descends (prefixWord ++ tailWord_858267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858339 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 1, 3]
def baseStart_858339 : Nat := 118140960795 + 858339 * 2 ^ 59
def prefixEnd_858339 : Nat := 4983230072969 + 3 ^ 40 * 858339 * 2
def baseEnd_858339 : Nat := 293826980999748318943385

theorem tailTrace_858339 : CollatzResearch.WordTrace tailWord_858339 prefixEnd_858339 293826980999748318943385 := by
  unfold tailWord_858339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306195237391870475474071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20870796824927913650316047 31306195237391870475474071)
  ·
    refine ⟨46959292856087805713211107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31306195237391870475474071 46959292856087805713211107)
    ·
      refine ⟨70438939284131708569816661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46959292856087805713211107 70438939284131708569816661)
      ·
        refine ⟨825456319735918459802539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 70438939284131708569816661 825456319735918459802539)
        ·
          refine ⟨1238184479603877689703809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825456319735918459802539 1238184479603877689703809)
          ·
            refine ⟨928638359702908267277857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238184479603877689703809 928638359702908267277857)
            ·
              refine ⟨696478769777181200458393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928638359702908267277857 696478769777181200458393)
              ·
                refine ⟨522359077332885900343795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696478769777181200458393 522359077332885900343795)
                ·
                  refine ⟨783538615999328850515693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522359077332885900343795 783538615999328850515693)
                  ·
                    refine ⟨293826980999748318943385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783538615999328850515693 293826980999748318943385)
                    ·
                      rfl

theorem cell22_858339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 3].length) (baseStart_858339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858339 prefixEnd_858339 := by exact prefixLift 858339
  have htrace : WordTrace (prefixWord ++ tailWord_858339) baseStart_858339 baseEnd_858339 := by
    simpa [prefixWord, tailWord_858339, baseEnd_858339] using wordTrace_append hprefix tailTrace_858339
  have hstable : (prefixWord ++ tailWord_858339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858339).length < 2 ^ (prefixWord ++ tailWord_858339).sum := by decide
  have hdescent : baseEnd_858339 < baseStart_858339 := by decide
  rcases family_descends (prefixWord ++ tailWord_858339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858376 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_858376 : Nat := 118140960795 + 858376 * 2 ^ 59
def prefixEnd_858376 : Nat := 4983230072969 + 3 ^ 40 * 858376 * 2
def baseEnd_858376 : Nat := 293839646855892555768271

theorem tailTrace_858376 : CollatzResearch.WordTrace tailWord_858376 prefixEnd_858376 293839646855892555768271 := by
  unfold tailWord_858376
  simp only [CollatzResearch.WordTrace]
  refine ⟨15653772369128912897285491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20871696492171883863047321 15653772369128912897285491)
  ·
    refine ⟨23480658553693369345928237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15653772369128912897285491 23480658553693369345928237)
    ·
      refine ⟨8805246957635013504723089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23480658553693369345928237 8805246957635013504723089)
      ·
        refine ⟨6603935218226260128542317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8805246957635013504723089 6603935218226260128542317)
        ·
          refine ⟨2476475706834847548203369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6603935218226260128542317 2476475706834847548203369)
          ·
            refine ⟨1857356780126135661152527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2476475706834847548203369 1857356780126135661152527)
            ·
              refine ⟨2786035170189203491728791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857356780126135661152527 2786035170189203491728791)
              ·
                refine ⟨4179052755283805237593187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786035170189203491728791 4179052755283805237593187)
                ·
                  refine ⟨6268579132925707856389781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179052755283805237593187 6268579132925707856389781)
                  ·
                    refine ⟨293839646855892555768271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6268579132925707856389781 293839646855892555768271)
                    ·
                      rfl

theorem cell22_858376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_858376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858376 prefixEnd_858376 := by exact prefixLift 858376
  have htrace : WordTrace (prefixWord ++ tailWord_858376) baseStart_858376 baseEnd_858376 := by
    simpa [prefixWord, tailWord_858376, baseEnd_858376] using wordTrace_append hprefix tailTrace_858376
  have hstable : (prefixWord ++ tailWord_858376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858376).length < 2 ^ (prefixWord ++ tailWord_858376).sum := by decide
  have hdescent : baseEnd_858376 < baseStart_858376 := by decide
  rcases family_descends (prefixWord ++ tailWord_858376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858440 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_858440 : Nat := 118140960795 + 858440 * 2 ^ 59
def prefixEnd_858440 : Nat := 4983230072969 + 3 ^ 40 * 858440 * 2
def baseEnd_858440 : Nat := 293861555363817722168075

theorem tailTrace_858440 : CollatzResearch.WordTrace tailWord_858440 prefixEnd_858440 293861555363817722168075 := by
  unfold tailWord_858440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654939505012982362450387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20873252673350643149933849 15654939505012982362450387)
  ·
    refine ⟨23482409257519473543675581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15654939505012982362450387 23482409257519473543675581)
    ·
      refine ⟨8805903471569802578878343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23482409257519473543675581 8805903471569802578878343)
      ·
        refine ⟨13208855207354703868317515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8805903471569802578878343 13208855207354703868317515)
        ·
          refine ⟨19813282811032055802476273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208855207354703868317515 19813282811032055802476273)
          ·
            refine ⟨14859962108274041851857205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19813282811032055802476273 14859962108274041851857205)
            ·
              refine ⟨1393121447650691423611613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14859962108274041851857205 1393121447650691423611613)
              ·
                refine ⟨522420542869009283854355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393121447650691423611613 522420542869009283854355)
                ·
                  refine ⟨783630814303513925781533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522420542869009283854355 783630814303513925781533)
                  ·
                    refine ⟨293861555363817722168075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783630814303513925781533 293861555363817722168075)
                    ·
                      rfl

theorem cell22_858440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_858440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858440 prefixEnd_858440 := by exact prefixLift 858440
  have htrace : WordTrace (prefixWord ++ tailWord_858440) baseStart_858440 baseEnd_858440 := by
    simpa [prefixWord, tailWord_858440, baseEnd_858440] using wordTrace_append hprefix tailTrace_858440
  have hstable : (prefixWord ++ tailWord_858440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858440).length < 2 ^ (prefixWord ++ tailWord_858440).sum := by decide
  have hdescent : baseEnd_858440 < baseStart_858440 := by decide
  rcases family_descends (prefixWord ++ tailWord_858440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858500 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_858500 : Nat := 118140960795 + 858500 * 2 ^ 59
def prefixEnd_858500 : Nat := 4983230072969 + 3 ^ 40 * 858500 * 2
def baseEnd_858500 : Nat := 293882094589997565667891

theorem tailTrace_858500 : CollatzResearch.WordTrace tailWord_858500 prefixEnd_858500 293882094589997565667891 := by
  unfold tailWord_858500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656033694904297486042477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20874711593205729981389969 15656033694904297486042477)
  ·
    refine ⟨5871012635589111557265929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15656033694904297486042477 5871012635589111557265929)
    ·
      refine ⟨4403259476691833667949447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5871012635589111557265929 4403259476691833667949447)
      ·
        refine ⟨6604889215037750501924171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403259476691833667949447 6604889215037750501924171)
        ·
          refine ⟨9907333822556625752886257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604889215037750501924171 9907333822556625752886257)
          ·
            refine ⟨7430500366917469314664693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907333822556625752886257 7430500366917469314664693)
            ·
              refine ⟨696609409398512748249815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7430500366917469314664693 696609409398512748249815)
              ·
                refine ⟨1044914114097769122374723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696609409398512748249815 1044914114097769122374723)
                ·
                  refine ⟨1567371171146653683562085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044914114097769122374723 1567371171146653683562085)
                  ·
                    refine ⟨293882094589997565667891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567371171146653683562085 293882094589997565667891)
                    ·
                      rfl

theorem cell22_858500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_858500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858500 prefixEnd_858500 := by exact prefixLift 858500
  have htrace : WordTrace (prefixWord ++ tailWord_858500) baseStart_858500 baseEnd_858500 := by
    simpa [prefixWord, tailWord_858500, baseEnd_858500] using wordTrace_append hprefix tailTrace_858500
  have hstable : (prefixWord ++ tailWord_858500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858500).length < 2 ^ (prefixWord ++ tailWord_858500).sum := by decide
  have hdescent : baseEnd_858500 < baseStart_858500 := by decide
  rcases family_descends (prefixWord ++ tailWord_858500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858530 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_858530 : Nat := 118140960795 + 858530 * 2 ^ 59
def prefixEnd_858530 : Nat := 4983230072969 + 3 ^ 40 * 858530 * 2
def baseEnd_858530 : Nat := 293892364203087487417799

theorem tailTrace_858530 : CollatzResearch.WordTrace tailWord_858530 prefixEnd_858530 293892364203087487417799 := by
  unfold tailWord_858530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828290394924977523919261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20875441053133273397118029 7828290394924977523919261)
  ·
    refine ⟨2935608898096866571469723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7828290394924977523919261 2935608898096866571469723)
    ·
      refine ⟨4403413347145299857204585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2935608898096866571469723 4403413347145299857204585)
      ·
        refine ⟨3302560010358974892903439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4403413347145299857204585 3302560010358974892903439)
        ·
          refine ⟨4953840015538462339355159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302560010358974892903439 4953840015538462339355159)
          ·
            refine ⟨7430760023307693509032739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953840015538462339355159 7430760023307693509032739)
            ·
              refine ⟨11146140034961540263549109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430760023307693509032739 11146140034961540263549109)
              ·
                refine ⟨1044950628277644399707729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11146140034961540263549109 1044950628277644399707729)
                ·
                  refine ⟨783712971208233299780797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044950628277644399707729 783712971208233299780797)
                  ·
                    refine ⟨293892364203087487417799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783712971208233299780797 293892364203087487417799)
                    ·
                      rfl

theorem cell22_858530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_858530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858530 prefixEnd_858530 := by exact prefixLift 858530
  have htrace : WordTrace (prefixWord ++ tailWord_858530) baseStart_858530 baseEnd_858530 := by
    simpa [prefixWord, tailWord_858530, baseEnd_858530] using wordTrace_append hprefix tailTrace_858530
  have hstable : (prefixWord ++ tailWord_858530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858530).length < 2 ^ (prefixWord ++ tailWord_858530).sum := by decide
  have hdescent : baseEnd_858530 < baseStart_858530 := by decide
  rcases family_descends (prefixWord ++ tailWord_858530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858545 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_858545 : Nat := 118140960795 + 858545 * 2 ^ 59
def prefixEnd_858545 : Nat := 4983230072969 + 3 ^ 40 * 858545 * 2
def baseEnd_858545 : Nat := 293897499009632448292753

theorem tailTrace_858545 : CollatzResearch.WordTrace tailWord_858545 prefixEnd_858545 293897499009632448292753 := by
  unfold tailWord_858545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313708674645567657473089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20875805783097045104982059 31313708674645567657473089)
  ·
    refine ⟨23485281505984175743104817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31313708674645567657473089 23485281505984175743104817)
    ·
      refine ⟨17613961129488131807328613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23485281505984175743104817 17613961129488131807328613)
      ·
        refine ⟨3302617711779024713874115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17613961129488131807328613 3302617711779024713874115)
        ·
          refine ⟨4953926567668537070811173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302617711779024713874115 4953926567668537070811173)
          ·
            refine ⟨928861231437850700777095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4953926567668537070811173 928861231437850700777095)
            ·
              refine ⟨1393291847156776051165643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928861231437850700777095 1393291847156776051165643)
              ·
                refine ⟨2089937770735164076748465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393291847156776051165643 2089937770735164076748465)
                ·
                  refine ⟨1567453328051373057561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2089937770735164076748465 1567453328051373057561349)
                  ·
                    refine ⟨293897499009632448292753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567453328051373057561349 293897499009632448292753)
                    ·
                      rfl

theorem cell22_858545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_858545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858545 prefixEnd_858545 := by exact prefixLift 858545
  have htrace : WordTrace (prefixWord ++ tailWord_858545) baseStart_858545 baseEnd_858545 := by
    simpa [prefixWord, tailWord_858545, baseEnd_858545] using wordTrace_append hprefix tailTrace_858545
  have hstable : (prefixWord ++ tailWord_858545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858545).length < 2 ^ (prefixWord ++ tailWord_858545).sum := by decide
  have hdescent : baseEnd_858545 < baseStart_858545 := by decide
  rcases family_descends (prefixWord ++ tailWord_858545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858564 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_858564 : Nat := 118140960795 + 858564 * 2 ^ 59
def prefixEnd_858564 : Nat := 4983230072969 + 3 ^ 40 * 858564 * 2
def baseEnd_858564 : Nat := 293904003097922732067695

theorem tailTrace_858564 : CollatzResearch.WordTrace tailWord_858564 prefixEnd_858564 293904003097922732067695 := by
  unfold tailWord_858564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657200830788366951207373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20876267774384489268276497 15657200830788366951207373)
  ·
    refine ⟨5871450311545637606702765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15657200830788366951207373 5871450311545637606702765)
    ·
      refine ⟨2201793866829614102513537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5871450311545637606702765 2201793866829614102513537)
      ·
        refine ⟨1651345400122210576885153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201793866829614102513537 1651345400122210576885153)
        ·
          refine ⟨1238509050091657932663865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651345400122210576885153 1238509050091657932663865)
          ·
            refine ⟨928881787568743449497899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238509050091657932663865 928881787568743449497899)
            ·
              refine ⟨1393322681353115174246849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928881787568743449497899 1393322681353115174246849)
              ·
                refine ⟨1044992011014836380685137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393322681353115174246849 1044992011014836380685137)
                ·
                  refine ⟨783744008261127285513853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044992011014836380685137 783744008261127285513853)
                  ·
                    refine ⟨293904003097922732067695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783744008261127285513853 293904003097922732067695)
                    ·
                      rfl

theorem cell22_858564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_858564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858564 prefixEnd_858564 := by exact prefixLift 858564
  have htrace : WordTrace (prefixWord ++ tailWord_858564) baseStart_858564 baseEnd_858564 := by
    simpa [prefixWord, tailWord_858564, baseEnd_858564] using wordTrace_append hprefix tailTrace_858564
  have hstable : (prefixWord ++ tailWord_858564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858564).length < 2 ^ (prefixWord ++ tailWord_858564).sum := by decide
  have hdescent : baseEnd_858564 < baseStart_858564 := by decide
  rcases family_descends (prefixWord ++ tailWord_858564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858594 : List Nat := [3, 3, 3, 2, 1, 2, 2, 6]
def baseStart_858594 : Nat := 118140960795 + 858594 * 2 ^ 59
def prefixEnd_858594 : Nat := 4983230072969 + 3 ^ 40 * 858594 * 2
def baseEnd_858594 : Nat := 32657141412334739313067

theorem tailTrace_858594 : CollatzResearch.WordTrace tailWord_858594 prefixEnd_858594 32657141412334739313067 := by
  unfold tailWord_858594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828873962867012256501709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20876997234312032684004557 7828873962867012256501709)
  ·
    refine ⟨2935827736075129596188141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7828873962867012256501709 2935827736075129596188141)
    ·
      refine ⟨1100935401028173598570553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2935827736075129596188141 1100935401028173598570553)
      ·
        refine ⟨825701550771130198927915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100935401028173598570553 825701550771130198927915)
        ·
          refine ⟨1238552326156695298391873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825701550771130198927915 1238552326156695298391873)
          ·
            refine ⟨928914244617521473793905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238552326156695298391873 928914244617521473793905)
            ·
              refine ⟨696685683463141105345429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928914244617521473793905 696685683463141105345429)
              ·
                refine ⟨32657141412334739313067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 696685683463141105345429 32657141412334739313067)
                ·
                  rfl

theorem cell22_858594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_858594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858594 prefixEnd_858594 := by exact prefixLift 858594
  have htrace : WordTrace (prefixWord ++ tailWord_858594) baseStart_858594 baseEnd_858594 := by
    simpa [prefixWord, tailWord_858594, baseEnd_858594] using wordTrace_append hprefix tailTrace_858594
  have hstable : (prefixWord ++ tailWord_858594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858594).length < 2 ^ (prefixWord ++ tailWord_858594).sum := by decide
  have hdescent : baseEnd_858594 < baseStart_858594 := by decide
  rcases family_descends (prefixWord ++ tailWord_858594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858626 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_858626 : Nat := 118140960795 + 858626 * 2 ^ 59
def prefixEnd_858626 : Nat := 4983230072969 + 3 ^ 40 * 858626 * 2
def baseEnd_858626 : Nat := 293925226964975237017505

theorem tailTrace_858626 : CollatzResearch.WordTrace tailWord_858626 prefixEnd_858626 293925226964975237017505 := by
  unfold tailWord_858626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829165746838029622792933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20877775324901412327447821 7829165746838029622792933)
  ·
    refine ⟨1467968577532130554273675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7829165746838029622792933 1467968577532130554273675)
    ·
      refine ⟨2201952866298195831410513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467968577532130554273675 2201952866298195831410513)
      ·
        refine ⟨1651464649723646873557885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201952866298195831410513 1651464649723646873557885)
        ·
          refine ⟨619299243646367577584207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1651464649723646873557885 619299243646367577584207)
          ·
            refine ⟨928948865469551366376311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619299243646367577584207 928948865469551366376311)
            ·
              refine ⟨1393423298204327049564467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928948865469551366376311 1393423298204327049564467)
              ·
                refine ⟨2090134947306490574346701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393423298204327049564467 2090134947306490574346701)
                ·
                  refine ⟨783800605239933965380013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2090134947306490574346701 783800605239933965380013)
                  ·
                    refine ⟨293925226964975237017505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783800605239933965380013 293925226964975237017505)
                    ·
                      rfl

theorem cell22_858626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_858626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858626 prefixEnd_858626 := by exact prefixLift 858626
  have htrace : WordTrace (prefixWord ++ tailWord_858626) baseStart_858626 baseEnd_858626 := by
    simpa [prefixWord, tailWord_858626, baseEnd_858626] using wordTrace_append hprefix tailTrace_858626
  have hstable : (prefixWord ++ tailWord_858626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858626).length < 2 ^ (prefixWord ++ tailWord_858626).sum := by decide
  have hdescent : baseEnd_858626 < baseStart_858626 := by decide
  rcases family_descends (prefixWord ++ tailWord_858626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858652 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_858652 : Nat := 118140960795 + 858652 * 2 ^ 59
def prefixEnd_858652 : Nat := 4983230072969 + 3 ^ 40 * 858652 * 2
def baseEnd_858652 : Nat := 293934127296319835867425

theorem tailTrace_858652 : CollatzResearch.WordTrace tailWord_858652 prefixEnd_858652 293934127296319835867425 := by
  unfold tailWord_858652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15658805642628962465809105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20878407523505283287745473 15658805642628962465809105)
  ·
    refine ⟨11744104231971721849356829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15658805642628962465809105 11744104231971721849356829)
    ·
      refine ⟨4404039086989395693508811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11744104231971721849356829 4404039086989395693508811)
      ·
        refine ⟨6606058630484093540263217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404039086989395693508811 6606058630484093540263217)
        ·
          refine ⟨4954543972863070155197413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606058630484093540263217 4954543972863070155197413)
          ·
            refine ⟨928976994911825654099515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4954543972863070155197413 928976994911825654099515)
            ·
              refine ⟨1393465492367738481149273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928976994911825654099515 1393465492367738481149273)
              ·
                refine ⟨1045099119275803860861955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393465492367738481149273 1045099119275803860861955)
                ·
                  refine ⟨1567648678913705791292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045099119275803860861955 1567648678913705791292933)
                  ·
                    refine ⟨293934127296319835867425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1567648678913705791292933 293934127296319835867425)
                    ·
                      rfl

theorem cell22_858652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_858652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858652 prefixEnd_858652 := by exact prefixLift 858652
  have htrace : WordTrace (prefixWord ++ tailWord_858652) baseStart_858652 baseEnd_858652 := by
    simpa [prefixWord, tailWord_858652, baseEnd_858652] using wordTrace_append hprefix tailTrace_858652
  have hstable : (prefixWord ++ tailWord_858652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858652).length < 2 ^ (prefixWord ++ tailWord_858652).sum := by decide
  have hdescent : baseEnd_858652 < baseStart_858652 := by decide
  rcases family_descends (prefixWord ++ tailWord_858652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858682 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_858682 : Nat := 118140960795 + 858682 * 2 ^ 59
def prefixEnd_858682 : Nat := 4983230072969 + 3 ^ 40 * 858682 * 2
def baseEnd_858682 : Nat := 293944396909409757617333

theorem tailTrace_858682 : CollatzResearch.WordTrace tailWord_858682 prefixEnd_858682 293944396909409757617333 := by
  unfold tailWord_858682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7829676368787310013802575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20879136983432826703473533 7829676368787310013802575)
  ·
    refine ⟨11744514553180965020703863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7829676368787310013802575 11744514553180965020703863)
    ·
      refine ⟨17616771829771447531055795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11744514553180965020703863 17616771829771447531055795)
      ·
        refine ⟨26425157744657171296583693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616771829771447531055795 26425157744657171296583693)
        ·
          refine ⟨9909434154246439236218885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26425157744657171296583693 9909434154246439236218885)
          ·
            refine ⟨1858018903921207356791041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9909434154246439236218885 1858018903921207356791041)
            ·
              refine ⟨1393514177940905517593281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858018903921207356791041 1393514177940905517593281)
              ·
                refine ⟨1045135633455679138194961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393514177940905517593281 1045135633455679138194961)
                ·
                  refine ⟨783851725091759353646221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045135633455679138194961 783851725091759353646221)
                  ·
                    refine ⟨293944396909409757617333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783851725091759353646221 293944396909409757617333)
                    ·
                      rfl

theorem cell22_858682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_858682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858682 prefixEnd_858682 := by exact prefixLift 858682
  have htrace : WordTrace (prefixWord ++ tailWord_858682) baseStart_858682 baseEnd_858682 := by
    simpa [prefixWord, tailWord_858682, baseEnd_858682] using wordTrace_append hprefix tailTrace_858682
  have hstable : (prefixWord ++ tailWord_858682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858682).length < 2 ^ (prefixWord ++ tailWord_858682).sum := by decide
  have hdescent : baseEnd_858682 < baseStart_858682 := by decide
  rcases family_descends (prefixWord ++ tailWord_858682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858684 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_858684 : Nat := 118140960795 + 858684 * 2 ^ 59
def prefixEnd_858684 : Nat := 4983230072969 + 3 ^ 40 * 858684 * 2
def baseEnd_858684 : Nat := 97981693850094139689109

theorem tailTrace_858684 : CollatzResearch.WordTrace tailWord_858684 prefixEnd_858684 97981693850094139689109 := by
  unfold tailWord_858684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15659389210570997198391553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20879185614094662931188737 15659389210570997198391553)
  ·
    refine ⟨11744541907928247898793665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15659389210570997198391553 11744541907928247898793665)
    ·
      refine ⟨8808406430946185924095249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11744541907928247898793665 8808406430946185924095249)
      ·
        refine ⟨6606304823209639443071437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8808406430946185924095249 6606304823209639443071437)
        ·
          refine ⟨2477364308703614791151789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6606304823209639443071437 2477364308703614791151789)
          ·
            refine ⟨929011615763855546681921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477364308703614791151789 929011615763855546681921)
            ·
              refine ⟨696758711822891660011441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929011615763855546681921 696758711822891660011441)
              ·
                refine ⟨522569033867168745008581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696758711822891660011441 522569033867168745008581)
                ·
                  refine ⟨97981693850094139689109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522569033867168745008581 97981693850094139689109)
                  ·
                    rfl

theorem cell22_858684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_858684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858684 prefixEnd_858684 := by exact prefixLift 858684
  have htrace : WordTrace (prefixWord ++ tailWord_858684) baseStart_858684 baseEnd_858684 := by
    simpa [prefixWord, tailWord_858684, baseEnd_858684] using wordTrace_append hprefix tailTrace_858684
  have hstable : (prefixWord ++ tailWord_858684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858684).length < 2 ^ (prefixWord ++ tailWord_858684).sum := by decide
  have hdescent : baseEnd_858684 < baseStart_858684 := by decide
  rcases family_descends (prefixWord ++ tailWord_858684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858695 : List Nat := [1, 1, 4, 1, 4, 3, 1, 7]
def baseStart_858695 : Nat := 118140960795 + 858695 * 2 ^ 59
def prefixEnd_858695 : Nat := 4983230072969 + 3 ^ 40 * 858695 * 2
def baseEnd_858695 : Nat := 32660983008342450782477

theorem tailTrace_858695 : CollatzResearch.WordTrace tailWord_858695 prefixEnd_858695 32660983008342450782477 := by
  unfold tailWord_858695
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319179624102143275433539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20879453082734762183622359 31319179624102143275433539)
  ·
    refine ⟨46978769436153214913150309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31319179624102143275433539 46978769436153214913150309)
    ·
      refine ⟨8808519269278727796215683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46978769436153214913150309 8808519269278727796215683)
      ·
        refine ⟨13212778903918091694323525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808519269278727796215683 13212778903918091694323525)
        ·
          refine ⟨2477396044484642192685661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13212778903918091694323525 2477396044484642192685661)
          ·
            refine ⟨929023516681740822257123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477396044484642192685661 929023516681740822257123)
            ·
              refine ⟨1393535275022611233385685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929023516681740822257123 1393535275022611233385685)
              ·
                refine ⟨32660983008342450782477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1393535275022611233385685 32660983008342450782477)
                ·
                  rfl

theorem cell22_858695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 7].length) (baseStart_858695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858695 prefixEnd_858695 := by exact prefixLift 858695
  have htrace : WordTrace (prefixWord ++ tailWord_858695) baseStart_858695 baseEnd_858695 := by
    simpa [prefixWord, tailWord_858695, baseEnd_858695] using wordTrace_append hprefix tailTrace_858695
  have hstable : (prefixWord ++ tailWord_858695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858695).length < 2 ^ (prefixWord ++ tailWord_858695).sum := by decide
  have hdescent : baseEnd_858695 < baseStart_858695 := by decide
  rcases family_descends (prefixWord ++ tailWord_858695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858718 : List Nat := [4, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_858718 : Nat := 118140960795 + 858718 * 2 ^ 59
def prefixEnd_858718 : Nat := 4983230072969 + 3 ^ 40 * 858718 * 2
def baseEnd_858718 : Nat := 97985573481705887905741

theorem tailTrace_858718 : CollatzResearch.WordTrace tailWord_858718 prefixEnd_858718 97985573481705887905741 := by
  unfold tailWord_858718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915002312877352275440101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20880012335345878802347205 3915002312877352275440101)
  ·
    refine ⟨734062933664503551645019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3915002312877352275440101 734062933664503551645019)
    ·
      refine ⟨1101094400496755327467529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 734062933664503551645019 1101094400496755327467529)
      ·
        refine ⟨825820800372566495600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101094400496755327467529 825820800372566495600647)
        ·
          refine ⟨1238731200558849743400971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825820800372566495600647 1238731200558849743400971)
          ·
            refine ⟨1858096800838274615101457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238731200558849743400971 1858096800838274615101457)
            ·
              refine ⟨1393572600628705961326093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858096800838274615101457 1393572600628705961326093)
              ·
                refine ⟨522589725235764735497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393572600628705961326093 522589725235764735497285)
                ·
                  refine ⟨97985573481705887905741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522589725235764735497285 97985573481705887905741)
                  ·
                    rfl

theorem cell22_858718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_858718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858718 prefixEnd_858718 := by exact prefixLift 858718
  have htrace : WordTrace (prefixWord ++ tailWord_858718) baseStart_858718 baseEnd_858718 := by
    simpa [prefixWord, tailWord_858718, baseEnd_858718] using wordTrace_append hprefix tailTrace_858718
  have hstable : (prefixWord ++ tailWord_858718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858718).length < 2 ^ (prefixWord ++ tailWord_858718).sum := by decide
  have hdescent : baseEnd_858718 < baseStart_858718 := by decide
  rcases family_descends (prefixWord ++ tailWord_858718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858723 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 7]
def baseStart_858723 : Nat := 118140960795 + 858723 * 2 ^ 59
def prefixEnd_858723 : Nat := 4983230072969 + 3 ^ 40 * 858723 * 2
def baseEnd_858723 : Nat := 97986144015766439114069

theorem tailTrace_858723 : CollatzResearch.WordTrace tailWord_858723 prefixEnd_858723 97986144015766439114069 := by
  unfold tailWord_858723
  simp only [CollatzResearch.WordTrace]
  refine ⟨31320200868000704057452823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20880133912000469371635215 31320200868000704057452823)
  ·
    refine ⟨46980301302001056086179235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31320200868000704057452823 46980301302001056086179235)
    ·
      refine ⟨70470451953001584129268853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46980301302001056086179235 70470451953001584129268853)
      ·
        refine ⟨6606604870593898512118955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70470451953001584129268853 6606604870593898512118955)
        ·
          refine ⟨9909907305890847768178433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606604870593898512118955 9909907305890847768178433)
          ·
            refine ⟨7432430479418135826133825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9909907305890847768178433 7432430479418135826133825)
            ·
              refine ⟨5574322859563601869600369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432430479418135826133825 5574322859563601869600369)
              ·
                refine ⟨4180742144672701402200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5574322859563601869600369 4180742144672701402200277)
                ·
                  refine ⟨97986144015766439114069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4180742144672701402200277 97986144015766439114069)
                  ·
                    rfl

theorem cell22_858723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_858723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858723 prefixEnd_858723 := by exact prefixLift 858723
  have htrace : WordTrace (prefixWord ++ tailWord_858723) baseStart_858723 baseEnd_858723 := by
    simpa [prefixWord, tailWord_858723, baseEnd_858723] using wordTrace_append hprefix tailTrace_858723
  have hstable : (prefixWord ++ tailWord_858723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858723).length < 2 ^ (prefixWord ++ tailWord_858723).sum := by decide
  have hdescent : baseEnd_858723 < baseStart_858723 := by decide
  rcases family_descends (prefixWord ++ tailWord_858723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858757 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 5]
def baseStart_858757 : Nat := 118140960795 + 858757 * 2 ^ 59
def prefixEnd_858757 : Nat := 4983230072969 + 3 ^ 40 * 858757 * 2
def baseEnd_858757 : Nat := 97990023647378187330701

theorem tailTrace_858757 : CollatzResearch.WordTrace tailWord_858757 prefixEnd_858757 97990023647378187330701 := by
  unfold tailWord_858757
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321440949877527864190525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20880960633251685242793683 31321440949877527864190525)
  ·
    refine ⟨11745540356204072949071447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31321440949877527864190525 11745540356204072949071447)
    ·
      refine ⟨17618310534306109423607171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745540356204072949071447 17618310534306109423607171)
      ·
        refine ⟨26427465801459164135410757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17618310534306109423607171 26427465801459164135410757)
        ·
          refine ⟨4955149837773593275389517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26427465801459164135410757 4955149837773593275389517)
          ·
            refine ⟨1858181189165097478271069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4955149837773593275389517 1858181189165097478271069)
            ·
              refine ⟨696817945936911554351651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1858181189165097478271069 696817945936911554351651)
              ·
                refine ⟨1045226918905367331527477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696817945936911554351651 1045226918905367331527477)
                ·
                  refine ⟨97990023647378187330701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045226918905367331527477 97990023647378187330701)
                  ·
                    rfl

theorem cell22_858757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_858757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858757 prefixEnd_858757 := by exact prefixLift 858757
  have htrace : WordTrace (prefixWord ++ tailWord_858757) baseStart_858757 baseEnd_858757 := by
    simpa [prefixWord, tailWord_858757, baseEnd_858757] using wordTrace_append hprefix tailTrace_858757
  have hstable : (prefixWord ++ tailWord_858757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858757).length < 2 ^ (prefixWord ++ tailWord_858757).sum := by decide
  have hdescent : baseEnd_858757 < baseStart_858757 := by decide
  rcases family_descends (prefixWord ++ tailWord_858757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858778 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_858778 : Nat := 118140960795 + 858778 * 2 ^ 59
def prefixEnd_858778 : Nat := 4983230072969 + 3 ^ 40 * 858778 * 2
def baseEnd_858778 : Nat := 293977259671297507217039

theorem tailTrace_858778 : CollatzResearch.WordTrace tailWord_858778 prefixEnd_858778 293977259671297507217039 := by
  unfold tailWord_858778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830551720700362112676247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20881471255200965633803325 7830551720700362112676247)
  ·
    refine ⟨11745827581050543169014371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830551720700362112676247 11745827581050543169014371)
    ·
      refine ⟨17618741371575814753521557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745827581050543169014371 17618741371575814753521557)
      ·
        refine ⟨825878501792616316571323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17618741371575814753521557 825878501792616316571323)
        ·
          refine ⟨1238817752688924474856985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825878501792616316571323 1238817752688924474856985)
          ·
            refine ⟨929113314516693356142739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238817752688924474856985 929113314516693356142739)
            ·
              refine ⟨1393669971775040034214109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929113314516693356142739 1393669971775040034214109)
              ·
                refine ⟨522626239415640012830291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1393669971775040034214109 522626239415640012830291)
                ·
                  refine ⟨783939359123460019245437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522626239415640012830291 783939359123460019245437)
                  ·
                    refine ⟨293977259671297507217039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 783939359123460019245437 293977259671297507217039)
                    ·
                      rfl

theorem cell22_858778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_858778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858778 prefixEnd_858778 := by exact prefixLift 858778
  have htrace : WordTrace (prefixWord ++ tailWord_858778) baseStart_858778 baseEnd_858778 := by
    simpa [prefixWord, tailWord_858778, baseEnd_858778] using wordTrace_append hprefix tailTrace_858778
  have hstable : (prefixWord ++ tailWord_858778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858778).length < 2 ^ (prefixWord ++ tailWord_858778).sum := by decide
  have hdescent : baseEnd_858778 < baseStart_858778 := by decide
  rcases family_descends (prefixWord ++ tailWord_858778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858830 : List Nat := [4, 1, 1, 1, 3, 2, 2, 8]
def baseStart_858830 : Nat := 118140960795 + 858830 * 2 ^ 59
def prefixEnd_858830 : Nat := 4983230072969 + 3 ^ 40 * 858830 * 2
def baseEnd_858830 : Nat := 32666117814887411657431

theorem tailTrace_858830 : CollatzResearch.WordTrace tailWord_858830 prefixEnd_858830 32666117814887411657431 := by
  unfold tailWord_858830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915512934826632666449743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20882735652408707554398629 3915512934826632666449743)
  ·
    refine ⟨5873269402239948999674615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915512934826632666449743 5873269402239948999674615)
    ·
      refine ⟨8809904103359923499511923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873269402239948999674615 8809904103359923499511923)
      ·
        refine ⟨13214856155039885249267885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809904103359923499511923 13214856155039885249267885)
        ·
          refine ⟨4955571058139956968475457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13214856155039885249267885 4955571058139956968475457)
          ·
            refine ⟨3716678293604967726356593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955571058139956968475457 3716678293604967726356593)
            ·
              refine ⟨2787508720203725794767445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716678293604967726356593 2787508720203725794767445)
              ·
                refine ⟨32666117814887411657431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2787508720203725794767445 32666117814887411657431)
                ·
                  rfl

theorem cell22_858830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_858830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858830 prefixEnd_858830 := by exact prefixLift 858830
  have htrace : WordTrace (prefixWord ++ tailWord_858830) baseStart_858830 baseEnd_858830 := by
    simpa [prefixWord, tailWord_858830, baseEnd_858830] using wordTrace_append hprefix tailTrace_858830
  have hstable : (prefixWord ++ tailWord_858830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858830).length < 2 ^ (prefixWord ++ tailWord_858830).sum := by decide
  have hdescent : baseEnd_858830 < baseStart_858830 := by decide
  rcases family_descends (prefixWord ++ tailWord_858830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858890 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_858890 : Nat := 118140960795 + 858890 * 2 ^ 59
def prefixEnd_858890 : Nat := 4983230072969 + 3 ^ 40 * 858890 * 2
def baseEnd_858890 : Nat := 294015599560166548416695

theorem tailTrace_858890 : CollatzResearch.WordTrace tailWord_858890 prefixEnd_858890 294015599560166548416695 := by
  unfold tailWord_858890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831572964598922894695531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20884194572263794385854749 7831572964598922894695531)
  ·
    refine ⟨11747359446898384342043297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831572964598922894695531 11747359446898384342043297)
    ·
      refine ⟨8810519585173788256532473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11747359446898384342043297 8810519585173788256532473)
      ·
        refine ⟨6607889688880341192399355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8810519585173788256532473 6607889688880341192399355)
        ·
          refine ⟨9911834533320511788599033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607889688880341192399355 9911834533320511788599033)
          ·
            refine ⟨7433875899990383841449275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9911834533320511788599033 7433875899990383841449275)
            ·
              refine ⟨11150813849985575762173913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433875899990383841449275 11150813849985575762173913)
              ·
                refine ⟨8363110387489181821630435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11150813849985575762173913 8363110387489181821630435)
                ·
                  refine ⟨12544665581233772732445653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8363110387489181821630435 12544665581233772732445653)
                  ·
                    refine ⟨294015599560166548416695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12544665581233772732445653 294015599560166548416695)
                    ·
                      rfl

theorem cell22_858890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_858890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858890 prefixEnd_858890 := by exact prefixLift 858890
  have htrace : WordTrace (prefixWord ++ tailWord_858890) baseStart_858890 baseEnd_858890 := by
    simpa [prefixWord, tailWord_858890, baseEnd_858890] using wordTrace_append hprefix tailTrace_858890
  have hstable : (prefixWord ++ tailWord_858890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858890).length < 2 ^ (prefixWord ++ tailWord_858890).sum := by decide
  have hdescent : baseEnd_858890 < baseStart_858890 := by decide
  rcases family_descends (prefixWord ++ tailWord_858890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858905 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_858905 : Nat := 118140960795 + 858905 * 2 ^ 59
def prefixEnd_858905 : Nat := 4983230072969 + 3 ^ 40 * 858905 * 2
def baseEnd_858905 : Nat := 294020734366711509291649

theorem tailTrace_858905 : CollatzResearch.WordTrace tailWord_858905 prefixEnd_858905 294020734366711509291649 := by
  unfold tailWord_858905
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326838953341349140578169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884559302227566093718779 31326838953341349140578169)
  ·
    refine ⟨23495129215006011855433627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31326838953341349140578169 23495129215006011855433627)
    ·
      refine ⟨35242693822509017783150441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23495129215006011855433627 35242693822509017783150441)
      ·
        refine ⟨26432020366881763337362831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35242693822509017783150441 26432020366881763337362831)
        ·
          refine ⟨39648030550322645006044247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432020366881763337362831 39648030550322645006044247)
          ·
            refine ⟨59472045825483967509066371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39648030550322645006044247 59472045825483967509066371)
            ·
              refine ⟨89208068738225951263599557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59472045825483967509066371 89208068738225951263599557)
              ·
                refine ⟨16726512888417365861924917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89208068738225951263599557 16726512888417365861924917)
                ·
                  refine ⟨1568110583289128049555461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16726512888417365861924917 1568110583289128049555461)
                  ·
                    refine ⟨294020734366711509291649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1568110583289128049555461 294020734366711509291649)
                    ·
                      rfl

theorem cell22_858905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_858905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858905 prefixEnd_858905 := by exact prefixLift 858905
  have htrace : WordTrace (prefixWord ++ tailWord_858905) baseStart_858905 baseEnd_858905 := by
    simpa [prefixWord, tailWord_858905, baseEnd_858905] using wordTrace_append hprefix tailTrace_858905
  have hstable : (prefixWord ++ tailWord_858905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858905).length < 2 ^ (prefixWord ++ tailWord_858905).sum := by decide
  have hdescent : baseEnd_858905 < baseStart_858905 := by decide
  rcases family_descends (prefixWord ++ tailWord_858905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858909 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 7]
def baseStart_858909 : Nat := 118140960795 + 858909 * 2 ^ 59
def prefixEnd_858909 : Nat := 4983230072969 + 3 ^ 40 * 858909 * 2
def baseEnd_858909 : Nat := 98007367882818944063879

theorem tailTrace_858909 : CollatzResearch.WordTrace tailWord_858909 prefixEnd_858909 98007367882818944063879 := by
  unfold tailWord_858909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326984845326857823723781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20884656563551238549149187 31326984845326857823723781)
  ·
    refine ⟨5873809658498785841948209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31326984845326857823723781 5873809658498785841948209)
    ·
      refine ⟨4405357243874089381461157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5873809658498785841948209 4405357243874089381461157)
      ·
        refine ⟨826004483226391759023967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4405357243874089381461157 826004483226391759023967)
        ·
          refine ⟨1239006724839587638535951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826004483226391759023967 1239006724839587638535951)
          ·
            refine ⟨1858510087259381457803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239006724839587638535951 1858510087259381457803927)
            ·
              refine ⟨2787765130889072186705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858510087259381457803927 2787765130889072186705891)
              ·
                refine ⟨4181647696333608280058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787765130889072186705891 4181647696333608280058837)
                ·
                  refine ⟨98007367882818944063879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4181647696333608280058837 98007367882818944063879)
                  ·
                    rfl

theorem cell22_858909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_858909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858909 prefixEnd_858909 := by exact prefixLift 858909
  have htrace : WordTrace (prefixWord ++ tailWord_858909) baseStart_858909 baseEnd_858909 := by
    simpa [prefixWord, tailWord_858909, baseEnd_858909] using wordTrace_append hprefix tailTrace_858909
  have hstable : (prefixWord ++ tailWord_858909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858909).length < 2 ^ (prefixWord ++ tailWord_858909).sum := by decide
  have hdescent : baseEnd_858909 < baseStart_858909 := by decide
  rcases family_descends (prefixWord ++ tailWord_858909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858926 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_858926 : Nat := 118140960795 + 858926 * 2 ^ 59
def prefixEnd_858926 : Nat := 4983230072969 + 3 ^ 40 * 858926 * 2
def baseEnd_858926 : Nat := 98009307698624818172195

theorem tailTrace_858926 : CollatzResearch.WordTrace tailWord_858926 prefixEnd_858926 98009307698624818172195 := by
  unfold tailWord_858926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915950610783158715886579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20885069924176846484728421 3915950610783158715886579)
  ·
    refine ⟨5873925916174738073829869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915950610783158715886579 5873925916174738073829869)
    ·
      refine ⟨2202722218565526777686201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5873925916174738073829869 2202722218565526777686201)
      ·
        refine ⟨1652041663924145083264651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202722218565526777686201 1652041663924145083264651)
        ·
          refine ⟨2478062495886217624896977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652041663924145083264651 2478062495886217624896977)
          ·
            refine ⟨1858546871914663218672733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478062495886217624896977 1858546871914663218672733)
            ·
              refine ⟨696955076967998707002275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1858546871914663218672733 696955076967998707002275)
              ·
                refine ⟨1045432615451998060503413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696955076967998707002275 1045432615451998060503413)
                ·
                  refine ⟨98009307698624818172195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045432615451998060503413 98009307698624818172195)
                  ·
                    rfl

theorem cell22_858926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_858926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858926 prefixEnd_858926 := by exact prefixLift 858926
  have htrace : WordTrace (prefixWord ++ tailWord_858926) baseStart_858926 baseEnd_858926 := by
    simpa [prefixWord, tailWord_858926, baseEnd_858926] using wordTrace_append hprefix tailTrace_858926
  have hstable : (prefixWord ++ tailWord_858926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858926).length < 2 ^ (prefixWord ++ tailWord_858926).sum := by decide
  have hdescent : baseEnd_858926 < baseStart_858926 := by decide
  rcases family_descends (prefixWord ++ tailWord_858926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858952 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_858952 : Nat := 118140960795 + 858952 * 2 ^ 59
def prefixEnd_858952 : Nat := 4983230072969 + 3 ^ 40 * 858952 * 2
def baseEnd_858952 : Nat := 294036823427219053366505

theorem tailTrace_858952 : CollatzResearch.WordTrace tailWord_858952 prefixEnd_858952 294036823427219053366505 := by
  unfold tailWord_858952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15664276592085538083769555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20885702122780717445026073 15664276592085538083769555)
  ·
    refine ⟨23496414888128307125654333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15664276592085538083769555 23496414888128307125654333)
    ·
      refine ⟨8811155583048115172120375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23496414888128307125654333 8811155583048115172120375)
      ·
        refine ⟨13216733374572172758180563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811155583048115172120375 13216733374572172758180563)
        ·
          refine ⟨19825100061858259137270845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13216733374572172758180563 19825100061858259137270845)
          ·
            refine ⟨7434412523196847176476567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19825100061858259137270845 7434412523196847176476567)
            ·
              refine ⟨11151618784795270764714851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434412523196847176476567 11151618784795270764714851)
              ·
                refine ⟨16727428177192906147072277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151618784795270764714851 16727428177192906147072277)
                ·
                  refine ⟨784098195805917475644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16727428177192906147072277 784098195805917475644013)
                  ·
                    refine ⟨294036823427219053366505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784098195805917475644013 294036823427219053366505)
                    ·
                      rfl

theorem cell22_858952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_858952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858952 prefixEnd_858952 := by exact prefixLift 858952
  have htrace : WordTrace (prefixWord ++ tailWord_858952) baseStart_858952 baseEnd_858952 := by
    simpa [prefixWord, tailWord_858952, baseEnd_858952] using wordTrace_append hprefix tailTrace_858952
  have hstable : (prefixWord ++ tailWord_858952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858952).length < 2 ^ (prefixWord ++ tailWord_858952).sum := by decide
  have hdescent : baseEnd_858952 < baseStart_858952 := by decide
  rcases family_descends (prefixWord ++ tailWord_858952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_858967 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_858967 : Nat := 118140960795 + 858967 * 2 ^ 59
def prefixEnd_858967 : Nat := 4983230072969 + 3 ^ 40 * 858967 * 2
def baseEnd_858967 : Nat := 294041958233764014241459

theorem tailTrace_858967 : CollatzResearch.WordTrace tailWord_858967 prefixEnd_858967 294041958233764014241459 := by
  unfold tailWord_858967
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329100279116733729335155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20886066852744489152890103 31329100279116733729335155)
  ·
    refine ⟨46993650418675100594002733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31329100279116733729335155 46993650418675100594002733)
    ·
      refine ⟨17622618907003162722751025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46993650418675100594002733 17622618907003162722751025)
      ·
        refine ⟨13216964180252372042063269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17622618907003162722751025 13216964180252372042063269)
        ·
          refine ⟨2478180783797319757886863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13216964180252372042063269 2478180783797319757886863)
          ·
            refine ⟨3717271175695979636830295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478180783797319757886863 3717271175695979636830295)
            ·
              refine ⟨5575906763543969455245443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717271175695979636830295 5575906763543969455245443)
              ·
                refine ⟨8363860145315954182868165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575906763543969455245443 8363860145315954182868165)
                ·
                  refine ⟨1568223777246741409287781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8363860145315954182868165 1568223777246741409287781)
                  ·
                    refine ⟨294041958233764014241459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1568223777246741409287781 294041958233764014241459)
                    ·
                      rfl

theorem cell22_858967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_858967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_858967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_858967 prefixEnd_858967 := by exact prefixLift 858967
  have htrace : WordTrace (prefixWord ++ tailWord_858967) baseStart_858967 baseEnd_858967 := by
    simpa [prefixWord, tailWord_858967, baseEnd_858967] using wordTrace_append hprefix tailTrace_858967
  have hstable : (prefixWord ++ tailWord_858967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_858967).length < 2 ^ (prefixWord ++ tailWord_858967).sum := by decide
  have hdescent : baseEnd_858967 < baseStart_858967 := by decide
  rcases family_descends (prefixWord ++ tailWord_858967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859031 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 1, 3]
def baseStart_859031 : Nat := 118140960795 + 859031 * 2 ^ 59
def prefixEnd_859031 : Nat := 4983230072969 + 3 ^ 40 * 859031 * 2
def baseEnd_859031 : Nat := 294063866741689180641263

theorem tailTrace_859031 : CollatzResearch.WordTrace tailWord_859031 prefixEnd_859031 294063866741689180641263 := by
  unfold tailWord_859031
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331434550884872659664947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20887623033923248439776631 31331434550884872659664947)
  ·
    refine ⟨46997151826327308989497421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31331434550884872659664947 46997151826327308989497421)
    ·
      refine ⟨17623931934872740871061533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46997151826327308989497421 17623931934872740871061533)
      ·
        refine ⟨6608974475577277826648075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17623931934872740871061533 6608974475577277826648075)
        ·
          refine ⟨9913461713365916739972113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6608974475577277826648075 9913461713365916739972113)
          ·
            refine ⟨7435096285024437554979085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9913461713365916739972113 7435096285024437554979085)
            ·
              refine ⟨2788161106884164083117157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7435096285024437554979085 2788161106884164083117157)
              ·
                refine ⟨522780207540780765584467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2788161106884164083117157 522780207540780765584467)
                ·
                  refine ⟨784170311311171148376701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522780207540780765584467 784170311311171148376701)
                  ·
                    refine ⟨294063866741689180641263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784170311311171148376701 294063866741689180641263)
                    ·
                      rfl

theorem cell22_859031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_859031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859031 prefixEnd_859031 := by exact prefixLift 859031
  have htrace : WordTrace (prefixWord ++ tailWord_859031) baseStart_859031 baseEnd_859031 := by
    simpa [prefixWord, tailWord_859031, baseEnd_859031] using wordTrace_append hprefix tailTrace_859031
  have hstable : (prefixWord ++ tailWord_859031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859031).length < 2 ^ (prefixWord ++ tailWord_859031).sum := by decide
  have hdescent : baseEnd_859031 < baseStart_859031 := by decide
  rcases family_descends (prefixWord ++ tailWord_859031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859089 : List Nat := [1, 2, 2, 1, 2, 1, 3, 6, 4]
def baseStart_859089 : Nat := 118140960795 + 859089 * 2 ^ 59
def prefixEnd_859089 : Nat := 4983230072969 + 3 ^ 40 * 859089 * 2
def baseEnd_859089 : Nat := 98027907108998787563695

theorem tailTrace_859089 : CollatzResearch.WordTrace tailWord_859089 prefixEnd_859089 98027907108998787563695 := by
  unfold tailWord_859089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31333549984674748565276321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20889033323116499043517547 31333549984674748565276321)
  ·
    refine ⟨23500162488506061423957241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31333549984674748565276321 23500162488506061423957241)
    ·
      refine ⟨17625121866379546067967931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23500162488506061423957241 17625121866379546067967931)
      ·
        refine ⟨26437682799569319101951897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17625121866379546067967931 26437682799569319101951897)
        ·
          refine ⟨19828262099676989326463923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26437682799569319101951897 19828262099676989326463923)
          ·
            refine ⟨29742393149515483989695885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19828262099676989326463923 29742393149515483989695885)
            ·
              refine ⟨11153397431068306496135957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29742393149515483989695885 11153397431068306496135957)
              ·
                refine ⟨522815504581326867006373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11153397431068306496135957 522815504581326867006373)
                ·
                  refine ⟨98027907108998787563695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522815504581326867006373 98027907108998787563695)
                  ·
                    rfl

theorem cell22_859089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_859089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859089 prefixEnd_859089 := by exact prefixLift 859089
  have htrace : WordTrace (prefixWord ++ tailWord_859089) baseStart_859089 baseEnd_859089 := by
    simpa [prefixWord, tailWord_859089, baseEnd_859089] using wordTrace_append hprefix tailTrace_859089
  have hstable : (prefixWord ++ tailWord_859089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859089).length < 2 ^ (prefixWord ++ tailWord_859089).sum := by decide
  have hdescent : baseEnd_859089 < baseStart_859089 := by decide
  rcases family_descends (prefixWord ++ tailWord_859089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859106 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_859106 : Nat := 118140960795 + 859106 * 2 ^ 59
def prefixEnd_859106 : Nat := 4983230072969 + 3 ^ 40 * 859106 * 2
def baseEnd_859106 : Nat := 98029846924804661672011

theorem tailTrace_859106 : CollatzResearch.WordTrace tailWord_859106 prefixEnd_859106 98029846924804661672011 := by
  unfold tailWord_859106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833542506403290117161293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20889446683742106979096781 7833542506403290117161293)
  ·
    refine ⟨2937578439901233793935485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7833542506403290117161293 2937578439901233793935485)
    ·
      refine ⟨1101591914962962672725807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2937578439901233793935485 1101591914962962672725807)
      ·
        refine ⟨1652387872444444009088711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101591914962962672725807 1652387872444444009088711)
        ·
          refine ⟨2478581808666666013633067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652387872444444009088711 2478581808666666013633067)
          ·
            refine ⟨3717872712999999020449601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478581808666666013633067 3717872712999999020449601)
            ·
              refine ⟨2788404534749999265337201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717872712999999020449601 2788404534749999265337201)
              ·
                refine ⟨2091303401062499449002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788404534749999265337201 2091303401062499449002901)
                ·
                  refine ⟨98029846924804661672011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2091303401062499449002901 98029846924804661672011)
                  ·
                    rfl

theorem cell22_859106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_859106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859106 prefixEnd_859106 := by exact prefixLift 859106
  have htrace : WordTrace (prefixWord ++ tailWord_859106) baseStart_859106 baseEnd_859106 := by
    simpa [prefixWord, tailWord_859106, baseEnd_859106] using wordTrace_append hprefix tailTrace_859106
  have hstable : (prefixWord ++ tailWord_859106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859106).length < 2 ^ (prefixWord ++ tailWord_859106).sum := by decide
  have hdescent : baseEnd_859106 < baseStart_859106 := by decide
  rcases family_descends (prefixWord ++ tailWord_859106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859196 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_859196 : Nat := 118140960795 + 859196 * 2 ^ 59
def prefixEnd_859196 : Nat := 4983230072969 + 3 ^ 40 * 859196 * 2
def baseEnd_859196 : Nat := 98040116537894583421919

theorem tailTrace_859196 : CollatzResearch.WordTrace tailWord_859196 prefixEnd_859196 98040116537894583421919 := by
  unfold tailWord_859196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668726297643552919710721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20891635063524737226280961 15668726297643552919710721)
  ·
    refine ⟨11751544723232664689783041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15668726297643552919710721 11751544723232664689783041)
    ·
      refine ⟨8813658542424498517337281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11751544723232664689783041 8813658542424498517337281)
      ·
        refine ⟨6610243906818373888002961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8813658542424498517337281 6610243906818373888002961)
        ·
          refine ⟨4957682930113780416002221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6610243906818373888002961 4957682930113780416002221)
          ·
            refine ⟨1859131098792667656000833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4957682930113780416002221 1859131098792667656000833)
            ·
              refine ⟨1394348324094500742000625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859131098792667656000833 1394348324094500742000625)
              ·
                refine ⟨1045761243070875556500469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394348324094500742000625 1045761243070875556500469)
                ·
                  refine ⟨98040116537894583421919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045761243070875556500469 98040116537894583421919)
                  ·
                    rfl

theorem cell22_859196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_859196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859196 prefixEnd_859196 := by exact prefixLift 859196
  have htrace : WordTrace (prefixWord ++ tailWord_859196) baseStart_859196 baseEnd_859196 := by
    simpa [prefixWord, tailWord_859196, baseEnd_859196] using wordTrace_append hprefix tailTrace_859196
  have hstable : (prefixWord ++ tailWord_859196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859196).length < 2 ^ (prefixWord ++ tailWord_859196).sum := by decide
  have hdescent : baseEnd_859196 < baseStart_859196 := by decide
  rcases family_descends (prefixWord ++ tailWord_859196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859224 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_859224 : Nat := 118140960795 + 859224 * 2 ^ 59
def prefixEnd_859224 : Nat := 4983230072969 + 3 ^ 40 * 859224 * 2
def baseEnd_859224 : Nat := 98043311528633670188557

theorem tailTrace_859224 : CollatzResearch.WordTrace tailWord_859224 prefixEnd_859224 98043311528633670188557 := by
  unfold tailWord_859224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15669236919592833310720363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20892315892790444414293817 15669236919592833310720363)
  ·
    refine ⟨23503855379389249966080545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15669236919592833310720363 23503855379389249966080545)
    ·
      refine ⟨17627891534541937474560409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23503855379389249966080545 17627891534541937474560409)
      ·
        refine ⟨13220918650906453105920307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17627891534541937474560409 13220918650906453105920307)
        ·
          refine ⟨19831377976359679658880461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220918650906453105920307 19831377976359679658880461)
          ·
            refine ⟨7436766741134879872080173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19831377976359679658880461 7436766741134879872080173)
            ·
              refine ⟨2788787527925579952030065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7436766741134879872080173 2788787527925579952030065)
              ·
                refine ⟨2091590645944184964022549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788787527925579952030065 2091590645944184964022549)
                ·
                  refine ⟨98043311528633670188557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2091590645944184964022549 98043311528633670188557)
                  ·
                    rfl

theorem cell22_859224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_859224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859224 prefixEnd_859224 := by exact prefixLift 859224
  have htrace : WordTrace (prefixWord ++ tailWord_859224) baseStart_859224 baseEnd_859224 := by
    simpa [prefixWord, tailWord_859224, baseEnd_859224] using wordTrace_append hprefix tailTrace_859224
  have hstable : (prefixWord ++ tailWord_859224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859224).length < 2 ^ (prefixWord ++ tailWord_859224).sum := by decide
  have hdescent : baseEnd_859224 < baseStart_859224 := by decide
  rcases family_descends (prefixWord ++ tailWord_859224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859241 : List Nat := [1, 2, 1, 1, 1, 6, 1, 5, 4]
def baseStart_859241 : Nat := 118140960795 + 859241 * 2 ^ 59
def prefixEnd_859241 : Nat := 4983230072969 + 3 ^ 40 * 859241 * 2
def baseEnd_859241 : Nat := 98045251344439544296873

theorem tailTrace_859241 : CollatzResearch.WordTrace tailWord_859241 prefixEnd_859241 98045251344439544296873 := by
  unfold tailWord_859241
  simp only [CollatzResearch.WordTrace]
  refine ⟨31339093880124078524809577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20892729253416052349873051 31339093880124078524809577)
  ·
    refine ⟨23504320410093058893607183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31339093880124078524809577 23504320410093058893607183)
    ·
      refine ⟨35256480615139588340410775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23504320410093058893607183 35256480615139588340410775)
      ·
        refine ⟨52884720922709382510616163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35256480615139588340410775 52884720922709382510616163)
        ·
          refine ⟨79327081384064073765924245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52884720922709382510616163 79327081384064073765924245)
          ·
            refine ⟨3718456939878003457777699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79327081384064073765924245 3718456939878003457777699)
            ·
              refine ⟨5577685409817005186666549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718456939878003457777699 5577685409817005186666549)
              ·
                refine ⟨522908007170344236249989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5577685409817005186666549 522908007170344236249989)
                ·
                  refine ⟨98045251344439544296873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522908007170344236249989 98045251344439544296873)
                  ·
                    rfl

theorem cell22_859241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_859241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859241 prefixEnd_859241 := by exact prefixLift 859241
  have htrace : WordTrace (prefixWord ++ tailWord_859241) baseStart_859241 baseEnd_859241 := by
    simpa [prefixWord, tailWord_859241, baseEnd_859241] using wordTrace_append hprefix tailTrace_859241
  have hstable : (prefixWord ++ tailWord_859241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859241).length < 2 ^ (prefixWord ++ tailWord_859241).sum := by decide
  have hdescent : baseEnd_859241 < baseStart_859241 := by decide
  rcases family_descends (prefixWord ++ tailWord_859241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859391 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_859391 : Nat := 118140960795 + 859391 * 2 ^ 59
def prefixEnd_859391 : Nat := 4983230072969 + 3 ^ 40 * 859391 * 2
def baseEnd_859391 : Nat := 294187102098768241640159

theorem tailTrace_859391 : CollatzResearch.WordTrace tailWord_859391 prefixEnd_859391 294187102098768241640159 := by
  unfold tailWord_859391
  simp only [CollatzResearch.WordTrace]
  refine ⟨31344564829580654142770027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20896376553053769428513351 31344564829580654142770027)
  ·
    refine ⟨47016847244370981214155041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31344564829580654142770027 47016847244370981214155041)
    ·
      refine ⟨35262635433278235910616281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47016847244370981214155041 35262635433278235910616281)
      ·
        refine ⟨26446976574958676932962211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35262635433278235910616281 26446976574958676932962211)
        ·
          refine ⟨39670464862438015399443317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26446976574958676932962211 39670464862438015399443317)
          ·
            refine ⟨3719106080853563943697811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39670464862438015399443317 3719106080853563943697811)
            ·
              refine ⟨5578659121280345915546717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719106080853563943697811 5578659121280345915546717)
              ·
                refine ⟨2091997170480129718330019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5578659121280345915546717 2091997170480129718330019)
                ·
                  refine ⟨3137995755720194577495029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091997170480129718330019 3137995755720194577495029)
                  ·
                    refine ⟨294187102098768241640159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3137995755720194577495029 294187102098768241640159)
                    ·
                      rfl

theorem cell22_859391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_859391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859391 prefixEnd_859391 := by exact prefixLift 859391
  have htrace : WordTrace (prefixWord ++ tailWord_859391) baseStart_859391 baseEnd_859391 := by
    simpa [prefixWord, tailWord_859391, baseEnd_859391] using wordTrace_append hprefix tailTrace_859391
  have hstable : (prefixWord ++ tailWord_859391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859391).length < 2 ^ (prefixWord ++ tailWord_859391).sum := by decide
  have hdescent : baseEnd_859391 < baseStart_859391 := by decide
  rcases family_descends (prefixWord ++ tailWord_859391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859442 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_859442 : Nat := 118140960795 + 859442 * 2 ^ 59
def prefixEnd_859442 : Nat := 4983230072969 + 3 ^ 40 * 859442 * 2
def baseEnd_859442 : Nat := 294204560441021108615003

theorem tailTrace_859442 : CollatzResearch.WordTrace tailWord_859442 prefixEnd_859442 294204560441021108615003 := by
  unfold tailWord_859442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836606238098972463219145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20897616634930593235251053 7836606238098972463219145)
  ·
    refine ⟨5877454678574229347414359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7836606238098972463219145 5877454678574229347414359)
    ·
      refine ⟨8816182017861344021121539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877454678574229347414359 8816182017861344021121539)
      ·
        refine ⟨13224273026792016031682309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8816182017861344021121539 13224273026792016031682309)
        ·
          refine ⟨2479551192523503005940433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13224273026792016031682309 2479551192523503005940433)
          ·
            refine ⟨1859663394392627254455325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479551192523503005940433 1859663394392627254455325)
            ·
              refine ⟨697373772897235220420747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859663394392627254455325 697373772897235220420747)
              ·
                refine ⟨1046060659345852830631121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697373772897235220420747 1046060659345852830631121)
                ·
                  refine ⟨784545494509389622973341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046060659345852830631121 784545494509389622973341)
                  ·
                    refine ⟨294204560441021108615003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784545494509389622973341 294204560441021108615003)
                    ·
                      rfl

theorem cell22_859442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_859442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859442 prefixEnd_859442 := by exact prefixLift 859442
  have htrace : WordTrace (prefixWord ++ tailWord_859442) baseStart_859442 baseEnd_859442 := by
    simpa [prefixWord, tailWord_859442, baseEnd_859442] using wordTrace_append hprefix tailTrace_859442
  have hstable : (prefixWord ++ tailWord_859442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859442).length < 2 ^ (prefixWord ++ tailWord_859442).sum := by decide
  have hdescent : baseEnd_859442 < baseStart_859442 := by decide
  rcases family_descends (prefixWord ++ tailWord_859442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859478 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_859478 : Nat := 118140960795 + 859478 * 2 ^ 59
def prefixEnd_859478 : Nat := 4983230072969 + 3 ^ 40 * 859478 * 2
def baseEnd_859478 : Nat := 98072294658909671571631

theorem tailTrace_859478 : CollatzResearch.WordTrace tailWord_859478 prefixEnd_859478 98072294658909671571631 := by
  unfold tailWord_859478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959233623766591750074193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20898491986843645334124725 1959233623766591750074193)
  ·
    refine ⟨1469425217824943812555645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1959233623766591750074193 1469425217824943812555645)
    ·
      refine ⟨551034456684353929708367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1469425217824943812555645 551034456684353929708367)
      ·
        refine ⟨826551685026530894562551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551034456684353929708367 826551685026530894562551)
        ·
          refine ⟨1239827527539796341843827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826551685026530894562551 1239827527539796341843827)
          ·
            refine ⟨1859741291309694512765741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239827527539796341843827 1859741291309694512765741)
            ·
              refine ⟨697402984241135442287153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1859741291309694512765741 697402984241135442287153)
              ·
                refine ⟨523052238180851581715365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697402984241135442287153 523052238180851581715365)
                ·
                  refine ⟨98072294658909671571631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523052238180851581715365 98072294658909671571631)
                  ·
                    rfl

theorem cell22_859478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_859478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859478 prefixEnd_859478 := by exact prefixLift 859478
  have htrace : WordTrace (prefixWord ++ tailWord_859478) baseStart_859478 baseEnd_859478 := by
    simpa [prefixWord, tailWord_859478, baseEnd_859478] using wordTrace_append hprefix tailTrace_859478
  have hstable : (prefixWord ++ tailWord_859478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859478).length < 2 ^ (prefixWord ++ tailWord_859478).sum := by decide
  have hdescent : baseEnd_859478 < baseStart_859478 := by decide
  rcases family_descends (prefixWord ++ tailWord_859478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859481 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_859481 : Nat := 118140960795 + 859481 * 2 ^ 59
def prefixEnd_859481 : Nat := 4983230072969 + 3 ^ 40 * 859481 * 2
def baseEnd_859481 : Nat := 294217910938038006889883

theorem tailTrace_859481 : CollatzResearch.WordTrace tailWord_859481 prefixEnd_859481 294217910938038006889883 := by
  unfold tailWord_859481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31347847399254599513546297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20898564932836399675697531 31347847399254599513546297)
  ·
    refine ⟨23510885549440949635159723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31347847399254599513546297 23510885549440949635159723)
    ·
      refine ⟨35266328324161424452739585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23510885549440949635159723 35266328324161424452739585)
      ·
        refine ⟨26449746243121068339554689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35266328324161424452739585 26449746243121068339554689)
        ·
          refine ⟨19837309682340801254666017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26449746243121068339554689 19837309682340801254666017)
          ·
            refine ⟨14877982261755600940999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19837309682340801254666017 14877982261755600940999513)
            ·
              refine ⟨11158486696316700705749635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14877982261755600940999513 11158486696316700705749635)
              ·
                refine ⟨16737730044475051058624453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11158486696316700705749635 16737730044475051058624453)
                ·
                  refine ⟨3138324383339072073492085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16737730044475051058624453 3138324383339072073492085)
                  ·
                    refine ⟨294217910938038006889883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3138324383339072073492085 294217910938038006889883)
                    ·
                      rfl

theorem cell22_859481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_859481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859481 prefixEnd_859481 := by exact prefixLift 859481
  have htrace : WordTrace (prefixWord ++ tailWord_859481) baseStart_859481 baseEnd_859481 := by
    simpa [prefixWord, tailWord_859481, baseEnd_859481] using wordTrace_append hprefix tailTrace_859481
  have hstable : (prefixWord ++ tailWord_859481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859481).length < 2 ^ (prefixWord ++ tailWord_859481).sum := by decide
  have hdescent : baseEnd_859481 < baseStart_859481 := by decide
  rcases family_descends (prefixWord ++ tailWord_859481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859500 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_859500 : Nat := 118140960795 + 859500 * 2 ^ 59
def prefixEnd_859500 : Nat := 4983230072969 + 3 ^ 40 * 859500 * 2
def baseEnd_859500 : Nat := 98074805008776096888275

theorem tailTrace_859500 : CollatzResearch.WordTrace tailWord_859500 prefixEnd_859500 98074805008776096888275 := by
  unfold tailWord_859500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674270193092882879243977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20899026924123843838991969 15674270193092882879243977)
  ·
    refine ⟨11755702644819662159432983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15674270193092882879243977 11755702644819662159432983)
    ·
      refine ⟨17633553967229493239149475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11755702644819662159432983 17633553967229493239149475)
      ·
        refine ⟨26450330950844239858724213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633553967229493239149475 26450330950844239858724213)
        ·
          refine ⟨2479718526641647486755395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26450330950844239858724213 2479718526641647486755395)
          ·
            refine ⟨3719577789962471230133093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479718526641647486755395 3719577789962471230133093)
            ·
              refine ⟨697420835617963355649955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3719577789962471230133093 697420835617963355649955)
              ·
                refine ⟨1046131253426945033474933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697420835617963355649955 1046131253426945033474933)
                ·
                  refine ⟨98074805008776096888275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046131253426945033474933 98074805008776096888275)
                  ·
                    rfl

theorem cell22_859500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_859500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859500 prefixEnd_859500 := by exact prefixLift 859500
  have htrace : WordTrace (prefixWord ++ tailWord_859500) baseStart_859500 baseEnd_859500 := by
    simpa [prefixWord, tailWord_859500, baseEnd_859500] using wordTrace_append hprefix tailTrace_859500
  have hstable : (prefixWord ++ tailWord_859500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859500).length < 2 ^ (prefixWord ++ tailWord_859500).sum := by decide
  have hdescent : baseEnd_859500 < baseStart_859500 := by decide
  rcases family_descends (prefixWord ++ tailWord_859500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859511 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 8]
def baseStart_859511 : Nat := 118140960795 + 859511 * 2 ^ 59
def prefixEnd_859511 : Nat := 4983230072969 + 3 ^ 40 * 859511 * 2
def baseEnd_859511 : Nat := 98076060183709309546597

theorem tailTrace_859511 : CollatzResearch.WordTrace tailWord_859511 prefixEnd_859511 98076060183709309546597 := by
  unfold tailWord_859511
  simp only [CollatzResearch.WordTrace]
  refine ⟨31348941589145914637138387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20899294392763943091425591 31348941589145914637138387)
  ·
    refine ⟨47023412383718871955707581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31348941589145914637138387 47023412383718871955707581)
    ·
      refine ⟨17633779643894576983390343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47023412383718871955707581 17633779643894576983390343)
      ·
        refine ⟨26450669465841865475085515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17633779643894576983390343 26450669465841865475085515)
        ·
          refine ⟨39676004198762798212628273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26450669465841865475085515 39676004198762798212628273)
          ·
            refine ⟨29757003149072098659471205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39676004198762798212628273 29757003149072098659471205)
            ·
              refine ⟨5579438090451018498650851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29757003149072098659471205 5579438090451018498650851)
              ·
                refine ⟨8369157135676527747976277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579438090451018498650851 8369157135676527747976277)
                ·
                  refine ⟨98076060183709309546597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8369157135676527747976277 98076060183709309546597)
                  ·
                    rfl

theorem cell22_859511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_859511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859511 prefixEnd_859511 := by exact prefixLift 859511
  have htrace : WordTrace (prefixWord ++ tailWord_859511) baseStart_859511 baseEnd_859511 := by
    simpa [prefixWord, tailWord_859511, baseEnd_859511] using wordTrace_append hprefix tailTrace_859511
  have hstable : (prefixWord ++ tailWord_859511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859511).length < 2 ^ (prefixWord ++ tailWord_859511).sum := by decide
  have hdescent : baseEnd_859511 < baseStart_859511 := by decide
  rcases family_descends (prefixWord ++ tailWord_859511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859538 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_859538 : Nat := 118140960795 + 859538 * 2 ^ 59
def prefixEnd_859538 : Nat := 4983230072969 + 3 ^ 40 * 859538 * 2
def baseEnd_859538 : Nat := 294237423202908858214709

theorem tailTrace_859538 : CollatzResearch.WordTrace tailWord_859538 prefixEnd_859538 294237423202908858214709 := by
  unfold tailWord_859538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837481590012024562092817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20899950906698732165580845 7837481590012024562092817)
  ·
    refine ⟨5878111192509018421569613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7837481590012024562092817 5878111192509018421569613)
    ·
      refine ⟨2204291697190881908088605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5878111192509018421569613 2204291697190881908088605)
      ·
        refine ⟨826609386446580715533227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2204291697190881908088605 826609386446580715533227)
        ·
          refine ⟨1239914079669871073299841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826609386446580715533227 1239914079669871073299841)
          ·
            refine ⟨929935559752403304974881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239914079669871073299841 929935559752403304974881)
            ·
              refine ⟨697451669814302478731161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929935559752403304974881 697451669814302478731161)
              ·
                refine ⟨523088752360726859048371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697451669814302478731161 523088752360726859048371)
                ·
                  refine ⟨784633128541090288572557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523088752360726859048371 784633128541090288572557)
                  ·
                    refine ⟨294237423202908858214709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 784633128541090288572557 294237423202908858214709)
                    ·
                      rfl

theorem cell22_859538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_859538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859538 prefixEnd_859538 := by exact prefixLift 859538
  have htrace : WordTrace (prefixWord ++ tailWord_859538) baseStart_859538 baseEnd_859538 := by
    simpa [prefixWord, tailWord_859538, baseEnd_859538] using wordTrace_append hprefix tailTrace_859538
  have hstable : (prefixWord ++ tailWord_859538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859538).length < 2 ^ (prefixWord ++ tailWord_859538).sum := by decide
  have hdescent : baseEnd_859538 < baseStart_859538 := by decide
  rcases family_descends (prefixWord ++ tailWord_859538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859545 : List Nat := [1, 2, 1, 2, 1, 6, 1, 4, 4]
def baseStart_859545 : Nat := 118140960795 + 859545 * 2 ^ 59
def prefixEnd_859545 : Nat := 4983230072969 + 3 ^ 40 * 859545 * 2
def baseEnd_859545 : Nat := 98079939815321057763229

theorem tailTrace_859545 : CollatzResearch.WordTrace tailWord_859545 prefixEnd_859545 98079939815321057763229 := by
  unfold tailWord_859545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31350181671022738443876089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20900121114015158962584059 31350181671022738443876089)
  ·
    refine ⟨23512636253267053832907067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31350181671022738443876089 23512636253267053832907067)
    ·
      refine ⟨35268954379900580749360601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23512636253267053832907067 35268954379900580749360601)
      ·
        refine ⟨26451715784925435562020451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35268954379900580749360601 26451715784925435562020451)
        ·
          refine ⟨39677573677388153343030677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26451715784925435562020451 39677573677388153343030677)
          ·
            refine ⟨1859886266127569687954563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39677573677388153343030677 1859886266127569687954563)
            ·
              refine ⟨2789829399191354531931845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859886266127569687954563 2789829399191354531931845)
              ·
                refine ⟨523093012348378974737221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2789829399191354531931845 523093012348378974737221)
                ·
                  refine ⟨98079939815321057763229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523093012348378974737221 98079939815321057763229)
                  ·
                    rfl

theorem cell22_859545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_859545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859545 prefixEnd_859545 := by exact prefixLift 859545
  have htrace : WordTrace (prefixWord ++ tailWord_859545) baseStart_859545 baseEnd_859545 := by
    simpa [prefixWord, tailWord_859545, baseEnd_859545] using wordTrace_append hprefix tailTrace_859545
  have hstable : (prefixWord ++ tailWord_859545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859545).length < 2 ^ (prefixWord ++ tailWord_859545).sum := by decide
  have hdescent : baseEnd_859545 < baseStart_859545 := by decide
  rcases family_descends (prefixWord ++ tailWord_859545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859682 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_859682 : Nat := 118140960795 + 859682 * 2 ^ 59
def prefixEnd_859682 : Nat := 4983230072969 + 3 ^ 40 * 859682 * 2
def baseEnd_859682 : Nat := 294286717345740482614267

theorem tailTrace_859682 : CollatzResearch.WordTrace tailWord_859682 prefixEnd_859682 294286717345740482614267 := by
  unfold tailWord_859682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838794617881602710403325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20903452314350940561075533 7838794617881602710403325)
  ·
    refine ⟨2939547981705601016401247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7838794617881602710403325 2939547981705601016401247)
    ·
      refine ⟨4409321972558401524601871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939547981705601016401247 4409321972558401524601871)
      ·
        refine ⟨6613982958837602286902807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409321972558401524601871 6613982958837602286902807)
        ·
          refine ⟨9920974438256403430354211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613982958837602286902807 9920974438256403430354211)
          ·
            refine ⟨14881461657384605145531317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9920974438256403430354211 14881461657384605145531317)
            ·
              refine ⟨1395137030379806732393561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14881461657384605145531317 1395137030379806732393561)
              ·
                refine ⟨1046352772784855049295171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395137030379806732393561 1046352772784855049295171)
                ·
                  refine ⟨1569529159177282573942757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046352772784855049295171 1569529159177282573942757)
                  ·
                    refine ⟨294286717345740482614267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569529159177282573942757 294286717345740482614267)
                    ·
                      rfl

theorem cell22_859682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_859682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859682 prefixEnd_859682 := by exact prefixLift 859682
  have htrace : WordTrace (prefixWord ++ tailWord_859682) baseStart_859682 baseEnd_859682 := by
    simpa [prefixWord, tailWord_859682, baseEnd_859682] using wordTrace_append hprefix tailTrace_859682
  have hstable : (prefixWord ++ tailWord_859682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859682).length < 2 ^ (prefixWord ++ tailWord_859682).sum := by decide
  have hdescent : baseEnd_859682 < baseStart_859682 := by decide
  rcases family_descends (prefixWord ++ tailWord_859682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859708 : List Nat := [2, 2, 2, 2, 14]
def baseStart_859708 : Nat := 118140960795 + 859708 * 2 ^ 59
def prefixEnd_859708 : Nat := 4983230072969 + 3 ^ 40 * 859708 * 2
def baseEnd_859708 : Nat := 1211093076860432434009

theorem tailTrace_859708 : CollatzResearch.WordTrace tailWord_859708 prefixEnd_859708 1211093076860432434009 := by
  unfold tailWord_859708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678063384716108641029889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20904084512954811521373185 15678063384716108641029889)
  ·
    refine ⟨11758547538537081480772417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15678063384716108641029889 11758547538537081480772417)
    ·
      refine ⟨8818910653902811110579313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11758547538537081480772417 8818910653902811110579313)
      ·
        refine ⟨6614182990427108332934485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818910653902811110579313 6614182990427108332934485)
        ·
          refine ⟨1211093076860432434009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 6614182990427108332934485 1211093076860432434009)
          ·
            rfl

theorem cell22_859708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 14].length) (baseStart_859708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859708 prefixEnd_859708 := by exact prefixLift 859708
  have htrace : WordTrace (prefixWord ++ tailWord_859708) baseStart_859708 baseEnd_859708 := by
    simpa [prefixWord, tailWord_859708, baseEnd_859708] using wordTrace_append hprefix tailTrace_859708
  have hstable : (prefixWord ++ tailWord_859708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859708).length < 2 ^ (prefixWord ++ tailWord_859708).sum := by decide
  have hdescent : baseEnd_859708 < baseStart_859708 := by decide
  rcases family_descends (prefixWord ++ tailWord_859708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_859723 : Nat := 118140960795 + 859723 * 2 ^ 59
def prefixEnd_859723 : Nat := 4983230072969 + 3 ^ 40 * 859723 * 2
def baseEnd_859723 : Nat := 294300752483630042339141

theorem tailTrace_859723 : CollatzResearch.WordTrace tailWord_859723 prefixEnd_859723 294300752483630042339141 := by
  unfold tailWord_859723
  simp only [CollatzResearch.WordTrace]
  refine ⟨31356673864377874843855823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20904449242918583229237215 31356673864377874843855823)
  ·
    refine ⟨47035010796566812265783735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31356673864377874843855823 47035010796566812265783735)
    ·
      refine ⟨70552516194850218398675603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47035010796566812265783735 70552516194850218398675603)
      ·
        refine ⟨105828774292275327598013405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70552516194850218398675603 105828774292275327598013405)
        ·
          refine ⟨39685790359603247849255027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105828774292275327598013405 39685790359603247849255027)
          ·
            refine ⟨59528685539404871773882541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39685790359603247849255027 59528685539404871773882541)
            ·
              refine ⟨22323257077276826915205953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59528685539404871773882541 22323257077276826915205953)
              ·
                refine ⟨16742442807957620186404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22323257077276826915205953 16742442807957620186404465)
                ·
                  refine ⟨12556832105968215139803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16742442807957620186404465 12556832105968215139803349)
                  ·
                    refine ⟨294300752483630042339141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12556832105968215139803349 294300752483630042339141)
                    ·
                      rfl

theorem cell22_859723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_859723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859723 prefixEnd_859723 := by exact prefixLift 859723
  have htrace : WordTrace (prefixWord ++ tailWord_859723) baseStart_859723 baseEnd_859723 := by
    simpa [prefixWord, tailWord_859723, baseEnd_859723] using wordTrace_append hprefix tailTrace_859723
  have hstable : (prefixWord ++ tailWord_859723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859723).length < 2 ^ (prefixWord ++ tailWord_859723).sum := by decide
  have hdescent : baseEnd_859723 < baseStart_859723 := by decide
  rcases family_descends (prefixWord ++ tailWord_859723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859770 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_859770 : Nat := 118140960795 + 859770 * 2 ^ 59
def prefixEnd_859770 : Nat := 4983230072969 + 3 ^ 40 * 859770 * 2
def baseEnd_859770 : Nat := 98105613848045862137999

theorem tailTrace_859770 : CollatzResearch.WordTrace tailWord_859770 prefixEnd_859770 98105613848045862137999 := by
  unfold tailWord_859770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839597023801900467704191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20905592063471734580544509 7839597023801900467704191)
  ·
    refine ⟨11759395535702850701556287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7839597023801900467704191 11759395535702850701556287)
    ·
      refine ⟨17639093303554276052334431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11759395535702850701556287 17639093303554276052334431)
      ·
        refine ⟨26458639955331414078501647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639093303554276052334431 26458639955331414078501647)
        ·
          refine ⟨39687959932997121117752471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26458639955331414078501647 39687959932997121117752471)
          ·
            refine ⟨59531939899495681676628707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39687959932997121117752471 59531939899495681676628707)
            ·
              refine ⟨89297909849243522514943061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59531939899495681676628707 89297909849243522514943061)
              ·
                refine ⟨1046459881045822529471989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 89297909849243522514943061 1046459881045822529471989)
                ·
                  refine ⟨98105613848045862137999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046459881045822529471989 98105613848045862137999)
                  ·
                    rfl

theorem cell22_859770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_859770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859770 prefixEnd_859770 := by exact prefixLift 859770
  have htrace : WordTrace (prefixWord ++ tailWord_859770) baseStart_859770 baseEnd_859770 := by
    simpa [prefixWord, tailWord_859770, baseEnd_859770] using wordTrace_append hprefix tailTrace_859770
  have hstable : (prefixWord ++ tailWord_859770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859770).length < 2 ^ (prefixWord ++ tailWord_859770).sum := by decide
  have hdescent : baseEnd_859770 < baseStart_859770 := by decide
  rcases family_descends (prefixWord ++ tailWord_859770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859785 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_859785 : Nat := 118140960795 + 859785 * 2 ^ 59
def prefixEnd_859785 : Nat := 4983230072969 + 3 ^ 40 * 859785 * 2
def baseEnd_859785 : Nat := 294321976350682547288951

theorem tailTrace_859785 : CollatzResearch.WordTrace tailWord_859785 prefixEnd_859785 294321976350682547288951 := by
  unfold tailWord_859785
  simp only [CollatzResearch.WordTrace]
  refine ⟨31358935190153259432612809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20905956793435506288408539 31358935190153259432612809)
  ·
    refine ⟨23519201392614944574459607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31358935190153259432612809 23519201392614944574459607)
    ·
      refine ⟨35278802088922416861689411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23519201392614944574459607 35278802088922416861689411)
      ·
        refine ⟨52918203133383625292534117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35278802088922416861689411 52918203133383625292534117)
        ·
          refine ⟨9922163087509429742350147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52918203133383625292534117 9922163087509429742350147)
          ·
            refine ⟨14883244631264144613525221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922163087509429742350147 14883244631264144613525221)
            ·
              refine ⟨2790608368362027115035979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14883244631264144613525221 2790608368362027115035979)
              ·
                refine ⟨4185912552543040672553969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790608368362027115035979 4185912552543040672553969)
                ·
                  refine ⟨3139434414407280504415477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185912552543040672553969 3139434414407280504415477)
                  ·
                    refine ⟨294321976350682547288951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3139434414407280504415477 294321976350682547288951)
                    ·
                      rfl

theorem cell22_859785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_859785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859785 prefixEnd_859785 := by exact prefixLift 859785
  have htrace : WordTrace (prefixWord ++ tailWord_859785) baseStart_859785 baseEnd_859785 := by
    simpa [prefixWord, tailWord_859785, baseEnd_859785] using wordTrace_append hprefix tailTrace_859785
  have hstable : (prefixWord ++ tailWord_859785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859785).length < 2 ^ (prefixWord ++ tailWord_859785).sum := by decide
  have hdescent : baseEnd_859785 < baseStart_859785 := by decide
  rcases family_descends (prefixWord ++ tailWord_859785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859787 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 5]
def baseStart_859787 : Nat := 118140960795 + 859787 * 2 ^ 59
def prefixEnd_859787 : Nat := 4983230072969 + 3 ^ 40 * 859787 * 2
def baseEnd_859787 : Nat := 98107553663851736246315

theorem tailTrace_859787 : CollatzResearch.WordTrace tailWord_859787 prefixEnd_859787 98107553663851736246315 := by
  unfold tailWord_859787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359008136146013774185615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906005424097342516123743 31359008136146013774185615)
  ·
    refine ⟨47038512204219020661278423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31359008136146013774185615 47038512204219020661278423)
    ·
      refine ⟨70557768306328530991917635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47038512204219020661278423 70557768306328530991917635)
      ·
        refine ⟨105836652459492796487876453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70557768306328530991917635 105836652459492796487876453)
        ·
          refine ⟨19844372336154899341476835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105836652459492796487876453 19844372336154899341476835)
          ·
            refine ⟨29766558504232349012215253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19844372336154899341476835 29766558504232349012215253)
            ·
              refine ⟨697653714942945679973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29766558504232349012215253 697653714942945679973795)
              ·
                refine ⟨1046480572414418519960693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697653714942945679973795 1046480572414418519960693)
                ·
                  refine ⟨98107553663851736246315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1046480572414418519960693 98107553663851736246315)
                  ·
                    rfl

theorem cell22_859787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 5].length) (baseStart_859787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859787 prefixEnd_859787 := by exact prefixLift 859787
  have htrace : WordTrace (prefixWord ++ tailWord_859787) baseStart_859787 baseEnd_859787 := by
    simpa [prefixWord, tailWord_859787, baseEnd_859787] using wordTrace_append hprefix tailTrace_859787
  have hstable : (prefixWord ++ tailWord_859787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859787).length < 2 ^ (prefixWord ++ tailWord_859787).sum := by decide
  have hdescent : baseEnd_859787 < baseStart_859787 := by decide
  rcases family_descends (prefixWord ++ tailWord_859787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859832 : List Nat := [2, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_859832 : Nat := 118140960795 + 859832 * 2 ^ 59
def prefixEnd_859832 : Nat := 4983230072969 + 3 ^ 40 * 859832 * 2
def baseEnd_859832 : Nat := 98112688470396697121269

theorem tailTrace_859832 : CollatzResearch.WordTrace tailWord_859832 prefixEnd_859832 98112688470396697121269 := by
  unfold tailWord_859832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680324710491493229786875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20907099613988657639715833 15680324710491493229786875)
  ·
    refine ⟨23520487065737239844680313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15680324710491493229786875 23520487065737239844680313)
    ·
      refine ⟨17640365299302929883510235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23520487065737239844680313 17640365299302929883510235)
      ·
        refine ⟨26460547948954394825265353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640365299302929883510235 26460547948954394825265353)
        ·
          refine ⟨19845410961715796118949015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26460547948954394825265353 19845410961715796118949015)
          ·
            refine ⟨29768116442573694178423523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19845410961715796118949015 29768116442573694178423523)
            ·
              refine ⟨44652174663860541267635285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29768116442573694178423523 44652174663860541267635285)
              ·
                refine ⟨523267671842115717980101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44652174663860541267635285 523267671842115717980101)
                ·
                  refine ⟨98112688470396697121269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523267671842115717980101 98112688470396697121269)
                  ·
                    rfl

theorem cell22_859832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_859832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859832 prefixEnd_859832 := by exact prefixLift 859832
  have htrace : WordTrace (prefixWord ++ tailWord_859832) baseStart_859832 baseEnd_859832 := by
    simpa [prefixWord, tailWord_859832, baseEnd_859832] using wordTrace_append hprefix tailTrace_859832
  have hstable : (prefixWord ++ tailWord_859832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859832).length < 2 ^ (prefixWord ++ tailWord_859832).sum := by decide
  have hdescent : baseEnd_859832 < baseStart_859832 := by decide
  rcases family_descends (prefixWord ++ tailWord_859832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859868 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_859868 : Nat := 118140960795 + 859868 * 2 ^ 59
def prefixEnd_859868 : Nat := 4983230072969 + 3 ^ 40 * 859868 * 2
def baseEnd_859868 : Nat := 294350388946897997463697

theorem tailTrace_859868 : CollatzResearch.WordTrace tailWord_859868 prefixEnd_859868 294350388946897997463697 := by
  unfold tailWord_859868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680981224426282303942129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20907974965901709738589505 15680981224426282303942129)
  ·
    refine ⟨11760735918319711727956597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15680981224426282303942129 11760735918319711727956597)
    ·
      refine ⟨1102568992342472974495931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11760735918319711727956597 1102568992342472974495931)
      ·
        refine ⟨1653853488513709461743897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1102568992342472974495931 1653853488513709461743897)
        ·
          refine ⟨1240390116385282096307923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653853488513709461743897 1240390116385282096307923)
          ·
            refine ⟨1860585174577923144461885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240390116385282096307923 1860585174577923144461885)
            ·
              refine ⟨697719440466721179173207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860585174577923144461885 697719440466721179173207)
              ·
                refine ⟨1046579160700081768759811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697719440466721179173207 1046579160700081768759811)
                ·
                  refine ⟨1569868741050122653139717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046579160700081768759811 1569868741050122653139717)
                  ·
                    refine ⟨294350388946897997463697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1569868741050122653139717 294350388946897997463697)
                    ·
                      rfl

theorem cell22_859868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_859868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859868 prefixEnd_859868 := by exact prefixLift 859868
  have htrace : WordTrace (prefixWord ++ tailWord_859868) baseStart_859868 baseEnd_859868 := by
    simpa [prefixWord, tailWord_859868, baseEnd_859868] using wordTrace_append hprefix tailTrace_859868
  have hstable : (prefixWord ++ tailWord_859868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859868).length < 2 ^ (prefixWord ++ tailWord_859868).sum := by decide
  have hdescent : baseEnd_859868 < baseStart_859868 := by decide
  rcases family_descends (prefixWord ++ tailWord_859868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859894 : List Nat := [5, 1, 1, 1, 1, 5, 1, 7]
def baseStart_859894 : Nat := 118140960795 + 859894 * 2 ^ 59
def prefixEnd_859894 : Nat := 4983230072969 + 3 ^ 40 * 859894 * 2
def baseEnd_859894 : Nat := 32706587697582510701513

theorem tailTrace_859894 : CollatzResearch.WordTrace tailWord_859894 prefixEnd_859894 32706587697582510701513 := by
  unfold tailWord_859894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960181921672398190520671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20908607164505580698887157 1960181921672398190520671)
  ·
    refine ⟨2940272882508597285781007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960181921672398190520671 2940272882508597285781007)
    ·
      refine ⟨4410409323762895928671511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940272882508597285781007 4410409323762895928671511)
      ·
        refine ⟨6615613985644343893007267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410409323762895928671511 6615613985644343893007267)
        ·
          refine ⟨9923420978466515839510901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615613985644343893007267 9923420978466515839510901)
          ·
            refine ⟨930320716731235859954147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9923420978466515839510901 930320716731235859954147)
            ·
              refine ⟨1395481075096853789931221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930320716731235859954147 1395481075096853789931221)
              ·
                refine ⟨32706587697582510701513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1395481075096853789931221 32706587697582510701513)
                ·
                  rfl

theorem cell22_859894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_859894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859894 prefixEnd_859894 := by exact prefixLift 859894
  have htrace : WordTrace (prefixWord ++ tailWord_859894) baseStart_859894 baseEnd_859894 := by
    simpa [prefixWord, tailWord_859894, baseEnd_859894] using wordTrace_append hprefix tailTrace_859894
  have hstable : (prefixWord ++ tailWord_859894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859894).length < 2 ^ (prefixWord ++ tailWord_859894).sum := by decide
  have hdescent : baseEnd_859894 < baseStart_859894 := by decide
  rcases family_descends (prefixWord ++ tailWord_859894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859917 : List Nat := [1, 7, 2, 1, 1, 1, 2, 3, 4]
def baseStart_859917 : Nat := 118140960795 + 859917 * 2 ^ 59
def prefixEnd_859917 : Nat := 4983230072969 + 3 ^ 40 * 859917 * 2
def baseEnd_859917 : Nat := 98122387549426067662849

theorem tailTrace_859917 : CollatzResearch.WordTrace tailWord_859917 prefixEnd_859917 98122387549426067662849 := by
  unfold tailWord_859917
  simp only [CollatzResearch.WordTrace]
  refine ⟨31363749625675045976418005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20909166417116697317612003 31363749625675045976418005)
  ·
    refine ⟨735087881851758890072297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31363749625675045976418005 735087881851758890072297)
    ·
      refine ⟨551315911388819167554223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 735087881851758890072297 551315911388819167554223)
      ·
        refine ⟨826973867083228751331335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551315911388819167554223 826973867083228751331335)
        ·
          refine ⟨1240460800624843126997003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826973867083228751331335 1240460800624843126997003)
          ·
            refine ⟨1860691200937264690495505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240460800624843126997003 1860691200937264690495505)
            ·
              refine ⟨1395518400702948517871629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860691200937264690495505 1395518400702948517871629)
              ·
                refine ⟨523319400263605694201861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395518400702948517871629 523319400263605694201861)
                ·
                  refine ⟨98122387549426067662849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523319400263605694201861 98122387549426067662849)
                  ·
                    rfl

theorem cell22_859917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_859917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859917 prefixEnd_859917 := by exact prefixLift 859917
  have htrace : WordTrace (prefixWord ++ tailWord_859917) baseStart_859917 baseEnd_859917 := by
    simpa [prefixWord, tailWord_859917, baseEnd_859917] using wordTrace_append hprefix tailTrace_859917
  have hstable : (prefixWord ++ tailWord_859917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859917).length < 2 ^ (prefixWord ++ tailWord_859917).sum := by decide
  have hdescent : baseEnd_859917 < baseStart_859917 := by decide
  rcases family_descends (prefixWord ++ tailWord_859917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859937 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_859937 : Nat := 118140960795 + 859937 * 2 ^ 59
def prefixEnd_859937 : Nat := 4983230072969 + 3 ^ 40 * 859937 * 2
def baseEnd_859937 : Nat := 294374009057004817488485

theorem tailTrace_859937 : CollatzResearch.WordTrace tailWord_859937 prefixEnd_859937 294374009057004817488485 := by
  unfold tailWord_859937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364479085602589392146065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20909652723735059594764043 31364479085602589392146065)
  ·
    refine ⟨23523359314201942044109549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31364479085602589392146065 23523359314201942044109549)
    ·
      refine ⟨8821259742825728266541081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23523359314201942044109549 8821259742825728266541081)
      ·
        refine ⟨6615944807119296199905811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8821259742825728266541081 6615944807119296199905811)
        ·
          refine ⟨9923917210678944299858717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615944807119296199905811 9923917210678944299858717)
          ·
            refine ⟨3721468954004604112447019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9923917210678944299858717 3721468954004604112447019)
            ·
              refine ⟨5582203431006906168670529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721468954004604112447019 5582203431006906168670529)
              ·
                refine ⟨4186652573255179626502897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582203431006906168670529 4186652573255179626502897)
                ·
                  refine ⟨3139989429941384719877173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4186652573255179626502897 3139989429941384719877173)
                  ·
                    refine ⟨294374009057004817488485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3139989429941384719877173 294374009057004817488485)
                    ·
                      rfl

theorem cell22_859937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_859937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859937 prefixEnd_859937 := by exact prefixLift 859937
  have htrace : WordTrace (prefixWord ++ tailWord_859937) baseStart_859937 baseEnd_859937 := by
    simpa [prefixWord, tailWord_859937, baseEnd_859937] using wordTrace_append hprefix tailTrace_859937
  have hstable : (prefixWord ++ tailWord_859937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859937).length < 2 ^ (prefixWord ++ tailWord_859937).sum := by decide
  have hdescent : baseEnd_859937 < baseStart_859937 := by decide
  rcases family_descends (prefixWord ++ tailWord_859937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859999 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 4, 3]
def baseStart_859999 : Nat := 118140960795 + 859999 * 2 ^ 59
def prefixEnd_859999 : Nat := 4983230072969 + 3 ^ 40 * 859999 * 2
def baseEnd_859999 : Nat := 294395232924057322438295

theorem tailTrace_859999 : CollatzResearch.WordTrace tailWord_859999 prefixEnd_859999 294395232924057322438295 := by
  unfold tailWord_859999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366740411377973980903051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20911160274251982653935367 31366740411377973980903051)
  ·
    refine ⟨47050110617066960971354577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31366740411377973980903051 47050110617066960971354577)
    ·
      refine ⟨35287582962800220728515933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47050110617066960971354577 35287582962800220728515933)
      ·
        refine ⟨13232843611050082773193475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35287582962800220728515933 13232843611050082773193475)
        ·
          refine ⟨19849265416575124159790213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232843611050082773193475 19849265416575124159790213)
          ·
            refine ⟨3721737265607835779960665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19849265416575124159790213 3721737265607835779960665)
            ·
              refine ⟨2791302949205876834970499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721737265607835779960665 2791302949205876834970499)
              ·
                refine ⟨4186954423808815252455749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791302949205876834970499 4186954423808815252455749)
                ·
                  refine ⟨785053954464152859835453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4186954423808815252455749 785053954464152859835453)
                  ·
                    refine ⟨294395232924057322438295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785053954464152859835453 294395232924057322438295)
                    ·
                      rfl

theorem cell22_859999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_859999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_859999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_859999 prefixEnd_859999 := by exact prefixLift 859999
  have htrace : WordTrace (prefixWord ++ tailWord_859999) baseStart_859999 baseEnd_859999 := by
    simpa [prefixWord, tailWord_859999, baseEnd_859999] using wordTrace_append hprefix tailTrace_859999
  have hstable : (prefixWord ++ tailWord_859999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859999).length < 2 ^ (prefixWord ++ tailWord_859999).sum := by decide
  have hdescent : baseEnd_859999 < baseStart_859999 := by decide
  rcases family_descends (prefixWord ++ tailWord_859999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860001 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 4]
def baseStart_860001 : Nat := 118140960795 + 860001 * 2 ^ 59
def prefixEnd_860001 : Nat := 4983230072969 + 3 ^ 40 * 860001 * 2
def baseEnd_860001 : Nat := 98131972521643327962763

theorem tailTrace_860001 : CollatzResearch.WordTrace tailWord_860001 prefixEnd_860001 98131972521643327962763 := by
  unfold tailWord_860001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366813357370728322475857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20911208904913818881650571 31366813357370728322475857)
  ·
    refine ⟨23525110018028046241856893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31366813357370728322475857 23525110018028046241856893)
    ·
      refine ⟨8821916256760517340696335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23525110018028046241856893 8821916256760517340696335)
      ·
        refine ⟨13232874385140776011044503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821916256760517340696335 13232874385140776011044503)
        ·
          refine ⟨19849311577711164016566755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232874385140776011044503 19849311577711164016566755)
          ·
            refine ⟨29773967366566746024850133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19849311577711164016566755 29773967366566746024850133)
            ·
              refine ⟨697827360153908109957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29773967366566746024850133 697827360153908109957425)
              ·
                refine ⟨523370520115431082468069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697827360153908109957425 523370520115431082468069)
                ·
                  refine ⟨98131972521643327962763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523370520115431082468069 98131972521643327962763)
                  ·
                    rfl

theorem cell22_860001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_860001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860001 prefixEnd_860001 := by exact prefixLift 860001
  have htrace : WordTrace (prefixWord ++ tailWord_860001) baseStart_860001 baseEnd_860001 := by
    simpa [prefixWord, tailWord_860001, baseEnd_860001] using wordTrace_append hprefix tailTrace_860001
  have hstable : (prefixWord ++ tailWord_860001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860001).length < 2 ^ (prefixWord ++ tailWord_860001).sum := by decide
  have hdescent : baseEnd_860001 < baseStart_860001 := by decide
  rcases family_descends (prefixWord ++ tailWord_860001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860012 : List Nat := [2, 2, 1, 1, 4, 2, 1, 9]
def baseStart_860012 : Nat := 118140960795 + 860012 * 2 ^ 59
def prefixEnd_860012 : Nat := 4983230072969 + 3 ^ 40 * 860012 * 2
def baseEnd_860012 : Nat := 32711075898858846873695

theorem tailTrace_860012 : CollatzResearch.WordTrace tailWord_860012 prefixEnd_860012 32711075898858846873695 := by
  unfold tailWord_860012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683607280165438600563145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20911476373553918134084193 15683607280165438600563145)
  ·
    refine ⟨11762705460124078950422359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15683607280165438600563145 11762705460124078950422359)
    ·
      refine ⟨17644058190186118425633539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762705460124078950422359 17644058190186118425633539)
      ·
        refine ⟨26466087285279177638450309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17644058190186118425633539 26466087285279177638450309)
        ·
          refine ⟨4962391365989845807209433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26466087285279177638450309 4962391365989845807209433)
          ·
            refine ⟨3721793524492384355407075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4962391365989845807209433 3721793524492384355407075)
            ·
              refine ⟨5582690286738576533110613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721793524492384355407075 5582690286738576533110613)
              ·
                refine ⟨32711075898858846873695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5582690286738576533110613 32711075898858846873695)
                ·
                  rfl

theorem cell22_860012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_860012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860012 prefixEnd_860012 := by exact prefixLift 860012
  have htrace : WordTrace (prefixWord ++ tailWord_860012) baseStart_860012 baseEnd_860012 := by
    simpa [prefixWord, tailWord_860012, baseEnd_860012] using wordTrace_append hprefix tailTrace_860012
  have hstable : (prefixWord ++ tailWord_860012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860012).length < 2 ^ (prefixWord ++ tailWord_860012).sum := by decide
  have hdescent : baseEnd_860012 < baseStart_860012 := by decide
  rcases family_descends (prefixWord ++ tailWord_860012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860046 : List Nat := [4, 1, 1, 5, 2, 9]
def baseStart_860046 : Nat := 118140960795 + 860046 * 2 ^ 59
def prefixEnd_860046 : Nat := 4983230072969 + 3 ^ 40 * 860046 * 2
def baseEnd_860046 : Nat := 3634707678821788475471

theorem tailTrace_860046 : CollatzResearch.WordTrace tailWord_860046 prefixEnd_860046 3634707678821788475471 := by
  unfold tailWord_860046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921056830275962625982999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20912303094805134005242661 3921056830275962625982999)
  ·
    refine ⟨5881585245413943938974499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3921056830275962625982999 5881585245413943938974499)
    ·
      refine ⟨8822377868120915908461749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881585245413943938974499 8822377868120915908461749)
      ·
        refine ⟨827097925136335866418289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8822377868120915908461749 827097925136335866418289)
        ·
          refine ⟨620323443852251899813717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827097925136335866418289 620323443852251899813717)
          ·
            refine ⟨3634707678821788475471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 620323443852251899813717 3634707678821788475471)
            ·
              rfl

theorem cell22_860046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 9].length) (baseStart_860046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860046 prefixEnd_860046 := by exact prefixLift 860046
  have htrace : WordTrace (prefixWord ++ tailWord_860046) baseStart_860046 baseEnd_860046 := by
    simpa [prefixWord, tailWord_860046, baseEnd_860046] using wordTrace_append hprefix tailTrace_860046
  have hstable : (prefixWord ++ tailWord_860046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860046).length < 2 ^ (prefixWord ++ tailWord_860046).sum := by decide
  have hdescent : baseEnd_860046 < baseStart_860046 := by decide
  rcases family_descends (prefixWord ++ tailWord_860046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860057 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 7]
def baseStart_860057 : Nat := 118140960795 + 860057 * 2 ^ 59
def prefixEnd_860057 : Nat := 4983230072969 + 3 ^ 40 * 860057 * 2
def baseEnd_860057 : Nat := 98138362503121501496039

theorem tailTrace_860057 : CollatzResearch.WordTrace tailWord_860057 prefixEnd_860057 98138362503121501496039 := by
  unfold tailWord_860057
  simp only [CollatzResearch.WordTrace]
  refine ⟨31368855845167849886514425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20912570563445233257676283 31368855845167849886514425)
  ·
    refine ⟨23526641883875887414885819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31368855845167849886514425 23526641883875887414885819)
    ·
      refine ⟨35289962825813831122328729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23526641883875887414885819 35289962825813831122328729)
      ·
        refine ⟨26467472119360373341746547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35289962825813831122328729 26467472119360373341746547)
        ·
          refine ⟨39701208179040560012619821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26467472119360373341746547 39701208179040560012619821)
          ·
            refine ⟨14887953067140210004732433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39701208179040560012619821 14887953067140210004732433)
            ·
              refine ⟨11165964800355157503549325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14887953067140210004732433 11165964800355157503549325)
              ·
                refine ⟨4187236800133184063830997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11165964800355157503549325 4187236800133184063830997)
                ·
                  refine ⟨98138362503121501496039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4187236800133184063830997 98138362503121501496039)
                  ·
                    rfl

theorem cell22_860057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_860057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860057 prefixEnd_860057 := by exact prefixLift 860057
  have htrace : WordTrace (prefixWord ++ tailWord_860057) baseStart_860057 baseEnd_860057 := by
    simpa [prefixWord, tailWord_860057, baseEnd_860057] using wordTrace_append hprefix tailTrace_860057
  have hstable : (prefixWord ++ tailWord_860057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860057).length < 2 ^ (prefixWord ++ tailWord_860057).sum := by decide
  have hdescent : baseEnd_860057 < baseStart_860057 := by decide
  rcases family_descends (prefixWord ++ tailWord_860057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860119 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 6]
def baseStart_860119 : Nat := 118140960795 + 860119 * 2 ^ 59
def prefixEnd_860119 : Nat := 4983230072969 + 3 ^ 40 * 860119 * 2
def baseEnd_860119 : Nat := 98145437125472336479309

theorem tailTrace_860119 : CollatzResearch.WordTrace tailWord_860119 prefixEnd_860119 98145437125472336479309 := by
  unfold tailWord_860119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371117170943234475271411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20914078113962156316847607 31371117170943234475271411)
  ·
    refine ⟨47056675756414851712907117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31371117170943234475271411 47056675756414851712907117)
    ·
      refine ⟨17646253408655569392340169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47056675756414851712907117 17646253408655569392340169)
      ·
        refine ⟨13234690056491677044255127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17646253408655569392340169 13234690056491677044255127)
        ·
          refine ⟨19852035084737515566382691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234690056491677044255127 19852035084737515566382691)
          ·
            refine ⟨29778052627106273349574037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852035084737515566382691 29778052627106273349574037)
            ·
              refine ⟨1395846216895606563261283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29778052627106273349574037 1395846216895606563261283)
              ·
                refine ⟨2093769325343409844891925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395846216895606563261283 2093769325343409844891925)
                ·
                  refine ⟨98145437125472336479309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2093769325343409844891925 98145437125472336479309)
                  ·
                    rfl

theorem cell22_860119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_860119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860119 prefixEnd_860119 := by exact prefixLift 860119
  have htrace : WordTrace (prefixWord ++ tailWord_860119) baseStart_860119 baseEnd_860119 := by
    simpa [prefixWord, tailWord_860119, baseEnd_860119] using wordTrace_append hprefix tailTrace_860119
  have hstable : (prefixWord ++ tailWord_860119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860119).length < 2 ^ (prefixWord ++ tailWord_860119).sum := by decide
  have hdescent : baseEnd_860119 < baseStart_860119 := by decide
  rcases family_descends (prefixWord ++ tailWord_860119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860153 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 4]
def baseStart_860153 : Nat := 118140960795 + 860153 * 2 ^ 59
def prefixEnd_860153 : Nat := 4983230072969 + 3 ^ 40 * 860153 * 2
def baseEnd_860153 : Nat := 98149316757084084695941

theorem tailTrace_860153 : CollatzResearch.WordTrace tailWord_860153 prefixEnd_860153 98149316757084084695941 := by
  unfold tailWord_860153
  simp only [CollatzResearch.WordTrace]
  refine ⟨31372357252820058282009113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20914904835213372188006075 31372357252820058282009113)
  ·
    refine ⟨23529267939615043711506835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31372357252820058282009113 23529267939615043711506835)
    ·
      refine ⟨35293901909422565567260253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23529267939615043711506835 35293901909422565567260253)
      ·
        refine ⟨13235213216033462087722595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35293901909422565567260253 13235213216033462087722595)
        ·
          refine ⟨19852819824050193131583893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13235213216033462087722595 19852819824050193131583893)
          ·
            refine ⟨930600929252352803042995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19852819824050193131583893 930600929252352803042995)
            ·
              refine ⟨1395901393878529204564493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930600929252352803042995 1395901393878529204564493)
              ·
                refine ⟨523463022704448451711685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395901393878529204564493 523463022704448451711685)
                ·
                  refine ⟨98149316757084084695941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523463022704448451711685 98149316757084084695941)
                  ·
                    rfl

theorem cell22_860153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_860153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860153 prefixEnd_860153 := by exact prefixLift 860153
  have htrace : WordTrace (prefixWord ++ tailWord_860153) baseStart_860153 baseEnd_860153 := by
    simpa [prefixWord, tailWord_860153, baseEnd_860153] using wordTrace_append hprefix tailTrace_860153
  have hstable : (prefixWord ++ tailWord_860153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860153).length < 2 ^ (prefixWord ++ tailWord_860153).sum := by decide
  have hdescent : baseEnd_860153 < baseStart_860153 := by decide
  rcases family_descends (prefixWord ++ tailWord_860153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860170 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_860170 : Nat := 118140960795 + 860170 * 2 ^ 59
def prefixEnd_860170 : Nat := 4983230072969 + 3 ^ 40 * 860170 * 2
def baseEnd_860170 : Nat := 98151256572889958804257

theorem tailTrace_860170 : CollatzResearch.WordTrace tailWord_860170 prefixEnd_860170 98151256572889958804257 := by
  unfold tailWord_860170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843244323439617546344491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20915318195838980123585309 7843244323439617546344491)
  ·
    refine ⟨11764866485159426319516737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843244323439617546344491 11764866485159426319516737)
    ·
      refine ⟨8823649863869569739637553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11764866485159426319516737 8823649863869569739637553)
      ·
        refine ⟨6617737397902177304728165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823649863869569739637553 6617737397902177304728165)
        ·
          refine ⟨1240825762106658244636531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6617737397902177304728165 1240825762106658244636531)
          ·
            refine ⟨1861238643159987366954797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240825762106658244636531 1861238643159987366954797)
            ·
              refine ⟨697964491184995262608049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1861238643159987366954797 697964491184995262608049)
              ·
                refine ⟨523473368388746446956037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697964491184995262608049 523473368388746446956037)
                ·
                  refine ⟨98151256572889958804257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523473368388746446956037 98151256572889958804257)
                  ·
                    rfl

theorem cell22_860170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_860170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860170 prefixEnd_860170 := by exact prefixLift 860170
  have htrace : WordTrace (prefixWord ++ tailWord_860170) baseStart_860170 baseEnd_860170 := by
    simpa [prefixWord, tailWord_860170, baseEnd_860170] using wordTrace_append hprefix tailTrace_860170
  have hstable : (prefixWord ++ tailWord_860170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860170).length < 2 ^ (prefixWord ++ tailWord_860170).sum := by decide
  have hdescent : baseEnd_860170 < baseStart_860170 := by decide
  rcases family_descends (prefixWord ++ tailWord_860170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860181 : List Nat := [1, 3, 2, 1, 5, 1, 2, 7]
def baseStart_860181 : Nat := 118140960795 + 860181 * 2 ^ 59
def prefixEnd_860181 : Nat := 4983230072969 + 3 ^ 40 * 860181 * 2
def baseEnd_860181 : Nat := 32717503915941057154193

theorem tailTrace_860181 : CollatzResearch.WordTrace tailWord_860181 prefixEnd_860181 32717503915941057154193 := by
  unfold tailWord_860181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373378496718619064028397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20915585664479079376018931 31373378496718619064028397)
  ·
    refine ⟨11765016936269482149010649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31373378496718619064028397 11765016936269482149010649)
    ·
      refine ⟨8823762702202111611757987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11765016936269482149010649 8823762702202111611757987)
      ·
        refine ⟨13235644053303167417636981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8823762702202111611757987 13235644053303167417636981)
        ·
          refine ⟨1240841629997171945403467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13235644053303167417636981 1240841629997171945403467)
          ·
            refine ⟨1861262444995757918105201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240841629997171945403467 1861262444995757918105201)
            ·
              refine ⟨1395946833746818438578901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861262444995757918105201 1395946833746818438578901)
              ·
                refine ⟨32717503915941057154193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1395946833746818438578901 32717503915941057154193)
                ·
                  rfl

theorem cell22_860181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 7].length) (baseStart_860181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860181 prefixEnd_860181 := by exact prefixLift 860181
  have htrace : WordTrace (prefixWord ++ tailWord_860181) baseStart_860181 baseEnd_860181 := by
    simpa [prefixWord, tailWord_860181, baseEnd_860181] using wordTrace_append hprefix tailTrace_860181
  have hstable : (prefixWord ++ tailWord_860181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860181).length < 2 ^ (prefixWord ++ tailWord_860181).sum := by decide
  have hdescent : baseEnd_860181 < baseStart_860181 := by decide
  rcases family_descends (prefixWord ++ tailWord_860181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860200 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_860200 : Nat := 118140960795 + 860200 * 2 ^ 59
def prefixEnd_860200 : Nat := 4983230072969 + 3 ^ 40 * 860200 * 2
def baseEnd_860200 : Nat := 294464039331759798162679

theorem tailTrace_860200 : CollatzResearch.WordTrace tailWord_860200 prefixEnd_860200 294464039331759798162679 := by
  unfold tailWord_860200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15687035741824892654485027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20916047655766523539313369 15687035741824892654485027)
  ·
    refine ⟨23530553612737338981727541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15687035741824892654485027 23530553612737338981727541)
    ·
      refine ⟨2205989401194125529536957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23530553612737338981727541 2205989401194125529536957)
      ·
        refine ⟨827246025447797073576359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2205989401194125529536957 827246025447797073576359)
        ·
          refine ⟨1240869038171695610364539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827246025447797073576359 1240869038171695610364539)
          ·
            refine ⟨1861303557257543415546809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240869038171695610364539 1861303557257543415546809)
            ·
              refine ⟨1395977667943157561660107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861303557257543415546809 1395977667943157561660107)
              ·
                refine ⟨2093966501914736342490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395977667943157561660107 2093966501914736342490161)
                ·
                  refine ⟨1570474876436052256867621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093966501914736342490161 1570474876436052256867621)
                  ·
                    refine ⟨294464039331759798162679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570474876436052256867621 294464039331759798162679)
                    ·
                      rfl

theorem cell22_860200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_860200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860200 prefixEnd_860200 := by exact prefixLift 860200
  have htrace : WordTrace (prefixWord ++ tailWord_860200) baseStart_860200 baseEnd_860200 := by
    simpa [prefixWord, tailWord_860200, baseEnd_860200] using wordTrace_append hprefix tailTrace_860200
  have hstable : (prefixWord ++ tailWord_860200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860200).length < 2 ^ (prefixWord ++ tailWord_860200).sum := by decide
  have hdescent : baseEnd_860200 < baseStart_860200 := by decide
  rcases family_descends (prefixWord ++ tailWord_860200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860230 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_860230 : Nat := 118140960795 + 860230 * 2 ^ 59
def prefixEnd_860230 : Nat := 4983230072969 + 3 ^ 40 * 860230 * 2
def baseEnd_860230 : Nat := 294474308944849719912587

theorem tailTrace_860230 : CollatzResearch.WordTrace tailWord_860230 prefixEnd_860230 294474308944849719912587 := by
  unfold tailWord_860230
  simp only [CollatzResearch.WordTrace]
  refine ⟨980473927298159388517567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20916777115694066955041429 980473927298159388517567)
  ·
    refine ⟨1470710890947239082776351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980473927298159388517567 1470710890947239082776351)
    ·
      refine ⟨2206066336420858624164527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470710890947239082776351 2206066336420858624164527)
      ·
        refine ⟨3309099504631287936246791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206066336420858624164527 3309099504631287936246791)
        ·
          refine ⟨4963649256946931904370187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309099504631287936246791 4963649256946931904370187)
          ·
            refine ⟨7445473885420397856555281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963649256946931904370187 7445473885420397856555281)
            ·
              refine ⟨5584105414065298392416461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7445473885420397856555281 5584105414065298392416461)
              ·
                refine ⟨2094039530274486897156173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5584105414065298392416461 2094039530274486897156173)
                ·
                  refine ⟨785264823852932586433565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2094039530274486897156173 785264823852932586433565)
                  ·
                    refine ⟨294474308944849719912587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785264823852932586433565 294474308944849719912587)
                    ·
                      rfl

theorem cell22_860230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_860230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860230 prefixEnd_860230 := by exact prefixLift 860230
  have htrace : WordTrace (prefixWord ++ tailWord_860230) baseStart_860230 baseEnd_860230 := by
    simpa [prefixWord, tailWord_860230, baseEnd_860230] using wordTrace_append hprefix tailTrace_860230
  have hstable : (prefixWord ++ tailWord_860230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860230).length < 2 ^ (prefixWord ++ tailWord_860230).sum := by decide
  have hdescent : baseEnd_860230 < baseStart_860230 := by decide
  rcases family_descends (prefixWord ++ tailWord_860230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860256 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_860256 : Nat := 118140960795 + 860256 * 2 ^ 59
def prefixEnd_860256 : Nat := 4983230072969 + 3 ^ 40 * 860256 * 2
def baseEnd_860256 : Nat := 294483209276194318762507

theorem tailTrace_860256 : CollatzResearch.WordTrace tailWord_860256 prefixEnd_860256 294483209276194318762507 := by
  unfold tailWord_860256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15688056985723453436504311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20917409314297937915339081 15688056985723453436504311)
  ·
    refine ⟨23532085478585180154756467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15688056985723453436504311 23532085478585180154756467)
    ·
      refine ⟨35298128217877770232134701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532085478585180154756467 35298128217877770232134701)
      ·
        refine ⟨13236798081704163837050513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35298128217877770232134701 13236798081704163837050513)
        ·
          refine ⟨9927598561278122877787885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13236798081704163837050513 9927598561278122877787885)
          ·
            refine ⟨3722849460479296079170457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9927598561278122877787885 3722849460479296079170457)
            ·
              refine ⟨2792137095359472059377843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722849460479296079170457 2792137095359472059377843)
              ·
                refine ⟨4188205643039208089066765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792137095359472059377843 4188205643039208089066765)
                ·
                  refine ⟨1570577116139703033400037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4188205643039208089066765 1570577116139703033400037)
                  ·
                    refine ⟨294483209276194318762507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570577116139703033400037 294483209276194318762507)
                    ·
                      rfl

theorem cell22_860256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_860256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860256 prefixEnd_860256 := by exact prefixLift 860256
  have htrace : WordTrace (prefixWord ++ tailWord_860256) baseStart_860256 baseEnd_860256 := by
    simpa [prefixWord, tailWord_860256, baseEnd_860256] using wordTrace_append hprefix tailTrace_860256
  have hstable : (prefixWord ++ tailWord_860256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860256).length < 2 ^ (prefixWord ++ tailWord_860256).sum := by decide
  have hdescent : baseEnd_860256 < baseStart_860256 := by decide
  rcases family_descends (prefixWord ++ tailWord_860256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860316 : List Nat := [2, 2, 3, 2, 1, 1, 3, 8]
def baseStart_860316 : Nat := 118140960795 + 860316 * 2 ^ 59
def prefixEnd_860316 : Nat := 4983230072969 + 3 ^ 40 * 860316 * 2
def baseEnd_860316 : Nat := 32722638722486018029147

theorem tailTrace_860316 : CollatzResearch.WordTrace tailWord_860316 prefixEnd_860316 32722638722486018029147 := by
  unfold tailWord_860316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689151175614768560096401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20918868234153024746795201 15689151175614768560096401)
  ·
    refine ⟨11766863381711076420072301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15689151175614768560096401 11766863381711076420072301)
    ·
      refine ⟨4412573768141653657527113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11766863381711076420072301 4412573768141653657527113)
      ·
        refine ⟨3309430326106240243145335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4412573768141653657527113 3309430326106240243145335)
        ·
          refine ⟨4964145489159360364718003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309430326106240243145335 4964145489159360364718003)
          ·
            refine ⟨7446218233739040547077005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964145489159360364718003 7446218233739040547077005)
            ·
              refine ⟨2792331837652140205153877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7446218233739040547077005 2792331837652140205153877)
              ·
                refine ⟨32722638722486018029147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2792331837652140205153877 32722638722486018029147)
                ·
                  rfl

theorem cell22_860316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_860316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860316 prefixEnd_860316 := by exact prefixLift 860316
  have htrace : WordTrace (prefixWord ++ tailWord_860316) baseStart_860316 baseEnd_860316 := by
    simpa [prefixWord, tailWord_860316, baseEnd_860316] using wordTrace_append hprefix tailTrace_860316
  have hstable : (prefixWord ++ tailWord_860316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860316).length < 2 ^ (prefixWord ++ tailWord_860316).sum := by decide
  have hdescent : baseEnd_860316 < baseStart_860316 := by decide
  rcases family_descends (prefixWord ++ tailWord_860316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860322 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_860322 : Nat := 118140960795 + 860322 * 2 ^ 59
def prefixEnd_860322 : Nat := 4983230072969 + 3 ^ 40 * 860322 * 2
def baseEnd_860322 : Nat := 98168600808330715537435

theorem tailTrace_860322 : CollatzResearch.WordTrace tailWord_860322 prefixEnd_860322 98168600808330715537435 := by
  unfold tailWord_860322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844630297301950036227805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20919014126138533429940813 7844630297301950036227805)
  ·
    refine ⟨2941736361488231263585427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7844630297301950036227805 2941736361488231263585427)
    ·
      refine ⟨4412604542232346895378141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941736361488231263585427 4412604542232346895378141)
      ·
        refine ⟨1654726703337130085766803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4412604542232346895378141 1654726703337130085766803)
        ·
          refine ⟨2482090055005695128650205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654726703337130085766803 2482090055005695128650205)
          ·
            refine ⟨930783770627135673243827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2482090055005695128650205 930783770627135673243827)
            ·
              refine ⟨1396175655940703509865741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930783770627135673243827 1396175655940703509865741)
              ·
                refine ⟨523565870977763816199653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396175655940703509865741 523565870977763816199653)
                ·
                  refine ⟨98168600808330715537435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523565870977763816199653 98168600808330715537435)
                  ·
                    rfl

theorem cell22_860322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_860322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860322 prefixEnd_860322 := by exact prefixLift 860322
  have htrace : WordTrace (prefixWord ++ tailWord_860322) baseStart_860322 baseEnd_860322 := by
    simpa [prefixWord, tailWord_860322, baseEnd_860322] using wordTrace_append hprefix tailTrace_860322
  have hstable : (prefixWord ++ tailWord_860322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860322).length < 2 ^ (prefixWord ++ tailWord_860322).sum := by decide
  have hdescent : baseEnd_860322 < baseStart_860322 := by decide
  rcases family_descends (prefixWord ++ tailWord_860322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860333 : List Nat := [1, 5, 2, 1, 2, 3, 8]
def baseStart_860333 : Nat := 118140960795 + 860333 * 2 ^ 59
def prefixEnd_860333 : Nat := 4983230072969 + 3 ^ 40 * 860333 * 2
def baseEnd_860333 : Nat := 10907761775918214243973

theorem tailTrace_860333 : CollatzResearch.WordTrace tailWord_860333 prefixEnd_860333 10907761775918214243973 := by
  unfold tailWord_860333
  simp only [CollatzResearch.WordTrace]
  refine ⟨31378922392167949023561653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20919281594778632682374435 31378922392167949023561653)
  ·
    refine ⟨2941773974265745220958905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31378922392167949023561653 2941773974265745220958905)
    ·
      refine ⟨2206330480699308915719179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2941773974265745220958905 2206330480699308915719179)
      ·
        refine ⟨3309495721048963373578769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206330480699308915719179 3309495721048963373578769)
        ·
          refine ⟨2482121790786722530184077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3309495721048963373578769 2482121790786722530184077)
          ·
            refine ⟨930795671545020948819029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2482121790786722530184077 930795671545020948819029)
            ·
              refine ⟨10907761775918214243973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 930795671545020948819029 10907761775918214243973)
              ·
                rfl

theorem cell22_860333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 8].length) (baseStart_860333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860333 prefixEnd_860333 := by exact prefixLift 860333
  have htrace : WordTrace (prefixWord ++ tailWord_860333) baseStart_860333 baseEnd_860333 := by
    simpa [prefixWord, tailWord_860333, baseEnd_860333] using wordTrace_append hprefix tailTrace_860333
  have hstable : (prefixWord ++ tailWord_860333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860333).length < 2 ^ (prefixWord ++ tailWord_860333).sum := by decide
  have hdescent : baseEnd_860333 < baseStart_860333 := by decide
  rcases family_descends (prefixWord ++ tailWord_860333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860354 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_860354 : Nat := 118140960795 + 860354 * 2 ^ 59
def prefixEnd_860354 : Nat := 4983230072969 + 3 ^ 40 * 860354 * 2
def baseEnd_860354 : Nat := 294516756678954729812207

theorem tailTrace_860354 : CollatzResearch.WordTrace tailWord_860354 prefixEnd_860354 294516756678954729812207 := by
  unfold tailWord_860354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844922081272967402519029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20919792216727913073384077 7844922081272967402519029)
  ·
    refine ⟨735461445119340693986159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7844922081272967402519029 735461445119340693986159)
    ·
      refine ⟨1103192167679011040979239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735461445119340693986159 1103192167679011040979239)
      ·
        refine ⟨1654788251518516561468859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103192167679011040979239 1654788251518516561468859)
        ·
          refine ⟨2482182377277774842203289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654788251518516561468859 2482182377277774842203289)
          ·
            refine ⟨1861636782958331131652467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2482182377277774842203289 1861636782958331131652467)
            ·
              refine ⟨2792455174437496697478701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861636782958331131652467 2792455174437496697478701)
              ·
                refine ⟨1047170690414061261554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2792455174437496697478701 1047170690414061261554513)
                ·
                  refine ⟨785378017810545946165885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1047170690414061261554513 785378017810545946165885)
                  ·
                    refine ⟨294516756678954729812207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785378017810545946165885 294516756678954729812207)
                    ·
                      rfl

theorem cell22_860354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_860354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860354 prefixEnd_860354 := by exact prefixLift 860354
  have htrace : WordTrace (prefixWord ++ tailWord_860354) baseStart_860354 baseEnd_860354 := by
    simpa [prefixWord, tailWord_860354, baseEnd_860354] using wordTrace_append hprefix tailTrace_860354
  have hstable : (prefixWord ++ tailWord_860354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860354).length < 2 ^ (prefixWord ++ tailWord_860354).sum := by decide
  have hdescent : baseEnd_860354 < baseStart_860354 := by decide
  rcases family_descends (prefixWord ++ tailWord_860354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860399 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 1, 3]
def baseStart_860399 : Nat := 118140960795 + 860399 * 2 ^ 59
def prefixEnd_860399 : Nat := 4983230072969 + 3 ^ 40 * 860399 * 2
def baseEnd_860399 : Nat := 294532161098589612437069

theorem tailTrace_860399 : CollatzResearch.WordTrace tailWord_860399 prefixEnd_860399 294532161098589612437069 := by
  unfold tailWord_860399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381329609928842295464251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20920886406619228196976167 31381329609928842295464251)
  ·
    refine ⟨47071994414893263443196377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31381329609928842295464251 47071994414893263443196377)
    ·
      refine ⟨35303995811169947582397283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47071994414893263443196377 35303995811169947582397283)
      ·
        refine ⟨52955993716754921373595925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35303995811169947582397283 52955993716754921373595925)
        ·
          refine ⟨2482312205472886939387309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52955993716754921373595925 2482312205472886939387309)
          ·
            refine ⟨930867077052332602270241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2482312205472886939387309 930867077052332602270241)
            ·
              refine ⟨698150307789249451702681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930867077052332602270241 698150307789249451702681)
              ·
                refine ⟨523612730841937088777011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698150307789249451702681 523612730841937088777011)
                ·
                  refine ⟨785419096262905633165517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523612730841937088777011 785419096262905633165517)
                  ·
                    refine ⟨294532161098589612437069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785419096262905633165517 294532161098589612437069)
                    ·
                      rfl

theorem cell22_860399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_860399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860399 prefixEnd_860399 := by exact prefixLift 860399
  have htrace : WordTrace (prefixWord ++ tailWord_860399) baseStart_860399 baseEnd_860399 := by
    simpa [prefixWord, tailWord_860399, baseEnd_860399] using wordTrace_append hprefix tailTrace_860399
  have hstable : (prefixWord ++ tailWord_860399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860399).length < 2 ^ (prefixWord ++ tailWord_860399).sum := by decide
  have hdescent : baseEnd_860399 < baseStart_860399 := by decide
  rcases family_descends (prefixWord ++ tailWord_860399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860440 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_860440 : Nat := 118140960795 + 860440 * 2 ^ 59
def prefixEnd_860440 : Nat := 4983230072969 + 3 ^ 40 * 860440 * 2
def baseEnd_860440 : Nat := 98182065412159724053981

theorem tailTrace_860440 : CollatzResearch.WordTrace tailWord_860440 prefixEnd_860440 98182065412159724053981 := by
  unfold tailWord_860440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691412501390153148853387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20921883335186870865137849 15691412501390153148853387)
  ·
    refine ⟨23537118752085229723280081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15691412501390153148853387 23537118752085229723280081)
    ·
      refine ⟨17652839064063922292460061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23537118752085229723280081 17652839064063922292460061)
      ·
        refine ⟨6619814649023970859672523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17652839064063922292460061 6619814649023970859672523)
        ·
          refine ⟨9929721973535956289508785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619814649023970859672523 9929721973535956289508785)
          ·
            refine ⟨7447291480151967217131589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929721973535956289508785 7447291480151967217131589)
            ·
              refine ⟨1396367152528493853212173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7447291480151967217131589 1396367152528493853212173)
              ·
                refine ⟨523637682198185194954565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1396367152528493853212173 523637682198185194954565)
                ·
                  refine ⟨98182065412159724053981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523637682198185194954565 98182065412159724053981)
                  ·
                    rfl

theorem cell22_860440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_860440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860440 prefixEnd_860440 := by exact prefixLift 860440
  have htrace : WordTrace (prefixWord ++ tailWord_860440) baseStart_860440 baseEnd_860440 := by
    simpa [prefixWord, tailWord_860440, baseEnd_860440] using wordTrace_append hprefix tailTrace_860440
  have hstable : (prefixWord ++ tailWord_860440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860440).length < 2 ^ (prefixWord ++ tailWord_860440).sum := by decide
  have hdescent : baseEnd_860440 < baseStart_860440 := by decide
  rcases family_descends (prefixWord ++ tailWord_860440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860451 : List Nat := [1, 1, 1, 4, 2, 2, 11]
def baseStart_860451 : Nat := 118140960795 + 860451 * 2 ^ 59
def prefixEnd_860451 : Nat := 4983230072969 + 3 ^ 40 * 860451 * 2
def baseEnd_860451 : Nat := 10909257843010326301367

theorem tailTrace_860451 : CollatzResearch.WordTrace tailWord_860451 prefixEnd_860451 10909257843010326301367 := by
  unfold tailWord_860451
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383226205740455176357207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20922150803826970117571471 31383226205740455176357207)
  ·
    refine ⟨47074839308610682764535811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31383226205740455176357207 47074839308610682764535811)
    ·
      refine ⟨70612258962916024146803717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47074839308610682764535811 70612258962916024146803717)
      ·
        refine ⟨13239798555546754527525697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70612258962916024146803717 13239798555546754527525697)
        ·
          refine ⟨9929848916660065895644273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13239798555546754527525697 9929848916660065895644273)
          ·
            refine ⟨7447386687495049421733205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929848916660065895644273 7447386687495049421733205)
            ·
              refine ⟨10909257843010326301367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7447386687495049421733205 10909257843010326301367)
              ·
                rfl

theorem cell22_860451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 11].length) (baseStart_860451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860451 prefixEnd_860451 := by exact prefixLift 860451
  have htrace : WordTrace (prefixWord ++ tailWord_860451) baseStart_860451 baseEnd_860451 := by
    simpa [prefixWord, tailWord_860451, baseEnd_860451] using wordTrace_append hprefix tailTrace_860451
  have hstable : (prefixWord ++ tailWord_860451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860451).length < 2 ^ (prefixWord ++ tailWord_860451).sum := by decide
  have hdescent : baseEnd_860451 < baseStart_860451 := by decide
  rcases family_descends (prefixWord ++ tailWord_860451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860517 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_860517 : Nat := 118140960795 + 860517 * 2 ^ 59
def prefixEnd_860517 : Nat := 4983230072969 + 3 ^ 40 * 860517 * 2
def baseEnd_860517 : Nat := 294572554910076637986707

theorem tailTrace_860517 : CollatzResearch.WordTrace tailWord_860517 prefixEnd_860517 294572554910076637986707 := by
  unfold tailWord_860517
  simp only [CollatzResearch.WordTrace]
  refine ⟨31385633423501348448259805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20923755615667565632173203 31385633423501348448259805)
  ·
    refine ⟨11769612533813005668097427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31385633423501348448259805 11769612533813005668097427)
    ·
      refine ⟨17654418800719508502146141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769612533813005668097427 17654418800719508502146141)
      ·
        refine ⟨6620407050269815688304803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17654418800719508502146141 6620407050269815688304803)
        ·
          refine ⟨9930610575404723532457205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620407050269815688304803 9930610575404723532457205)
          ·
            refine ⟨930994741444192831167863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9930610575404723532457205 930994741444192831167863)
            ·
              refine ⟨1396492112166289246751795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930994741444192831167863 1396492112166289246751795)
              ·
                refine ⟨2094738168249433870127693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396492112166289246751795 2094738168249433870127693)
                ·
                  refine ⟨785526813093537701297885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2094738168249433870127693 785526813093537701297885)
                  ·
                    refine ⟨294572554910076637986707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 785526813093537701297885 294572554910076637986707)
                    ·
                      rfl

theorem cell22_860517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_860517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860517 prefixEnd_860517 := by exact prefixLift 860517
  have htrace : WordTrace (prefixWord ++ tailWord_860517) baseStart_860517 baseEnd_860517 := by
    simpa [prefixWord, tailWord_860517, baseEnd_860517] using wordTrace_append hprefix tailTrace_860517
  have hstable : (prefixWord ++ tailWord_860517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860517).length < 2 ^ (prefixWord ++ tailWord_860517).sum := by decide
  have hdescent : baseEnd_860517 < baseStart_860517 := by decide
  rcases family_descends (prefixWord ++ tailWord_860517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860530 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_860530 : Nat := 118140960795 + 860530 * 2 ^ 59
def prefixEnd_860530 : Nat := 4983230072969 + 3 ^ 40 * 860530 * 2
def baseEnd_860530 : Nat := 98192335025249645803889

theorem tailTrace_860530 : CollatzResearch.WordTrace tailWord_860530 prefixEnd_860530 98192335025249645803889 := by
  unfold tailWord_860530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846526893113562917120761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20924071714969501112322029 7846526893113562917120761)
  ·
    refine ⟨5884895169835172187840571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7846526893113562917120761 5884895169835172187840571)
    ·
      refine ⟨8827342754752758281760857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884895169835172187840571 8827342754752758281760857)
      ·
        refine ⟨6620507066064568711320643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8827342754752758281760857 6620507066064568711320643)
        ·
          refine ⟨9930760599096853066980965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620507066064568711320643 9930760599096853066980965)
          ·
            refine ⟨1862017612330659950058931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9930760599096853066980965 1862017612330659950058931)
            ·
              refine ⟨2793026418495989925088397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862017612330659950058931 2793026418495989925088397)
              ·
                refine ⟨1047384906935996221908149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2793026418495989925088397 1047384906935996221908149)
                ·
                  refine ⟨98192335025249645803889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047384906935996221908149 98192335025249645803889)
                  ·
                    rfl

theorem cell22_860530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_860530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860530 prefixEnd_860530 := by exact prefixLift 860530
  have htrace : WordTrace (prefixWord ++ tailWord_860530) baseStart_860530 baseEnd_860530 := by
    simpa [prefixWord, tailWord_860530, baseEnd_860530] using wordTrace_append hprefix tailTrace_860530
  have hstable : (prefixWord ++ tailWord_860530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860530).length < 2 ^ (prefixWord ++ tailWord_860530).sum := by decide
  have hdescent : baseEnd_860530 < baseStart_860530 := by decide
  rcases family_descends (prefixWord ++ tailWord_860530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860543 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_860543 : Nat := 118140960795 + 860543 * 2 ^ 59
def prefixEnd_860543 : Nat := 4983230072969 + 3 ^ 40 * 860543 * 2
def baseEnd_860543 : Nat := 294581455241421236836627

theorem tailTrace_860543 : CollatzResearch.WordTrace tailWord_860543 prefixEnd_860543 294581455241421236836627 := by
  unfold tailWord_860543
  simp only [CollatzResearch.WordTrace]
  refine ⟨31386581721407154888706283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20924387814271436592470855 31386581721407154888706283)
  ·
    refine ⟨47079872582110732333059425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31386581721407154888706283 47079872582110732333059425)
    ·
      refine ⟨35309904436583049249794569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47079872582110732333059425 35309904436583049249794569)
      ·
        refine ⟨26482428327437286937345927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35309904436583049249794569 26482428327437286937345927)
        ·
          refine ⟨39723642491155930406018891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26482428327437286937345927 39723642491155930406018891)
          ·
            refine ⟨59585463736733895609028337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39723642491155930406018891 59585463736733895609028337)
            ·
              refine ⟨44689097802550421706771253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59585463736733895609028337 44689097802550421706771253)
              ·
                refine ⟨4189602918989102035009805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44689097802550421706771253 4189602918989102035009805)
                ·
                  refine ⟨1571101094620913263128677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4189602918989102035009805 1571101094620913263128677)
                  ·
                    refine ⟨294581455241421236836627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571101094620913263128677 294581455241421236836627)
                    ·
                      rfl

theorem cell22_860543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_860543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860543 prefixEnd_860543 := by exact prefixLift 860543
  have htrace : WordTrace (prefixWord ++ tailWord_860543) baseStart_860543 baseEnd_860543 := by
    simpa [prefixWord, tailWord_860543, baseEnd_860543] using wordTrace_append hprefix tailTrace_860543
  have hstable : (prefixWord ++ tailWord_860543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860543).length < 2 ^ (prefixWord ++ tailWord_860543).sum := by decide
  have hdescent : baseEnd_860543 < baseStart_860543 := by decide
  rcases family_descends (prefixWord ++ tailWord_860543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860588 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_860588 : Nat := 118140960795 + 860588 * 2 ^ 59
def prefixEnd_860588 : Nat := 4983230072969 + 3 ^ 40 * 860588 * 2
def baseEnd_860588 : Nat := 294596859661056119461489

theorem tailTrace_860588 : CollatzResearch.WordTrace tailWord_860588 prefixEnd_860588 294596859661056119461489 := by
  unfold tailWord_860588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15694111503122063787047209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20925482004162751716062945 15694111503122063787047209)
  ·
    refine ⟨11770583627341547840285407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15694111503122063787047209 11770583627341547840285407)
    ·
      refine ⟨17655875441012321760428111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11770583627341547840285407 17655875441012321760428111)
      ·
        refine ⟨26483813161518482640642167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17655875441012321760428111 26483813161518482640642167)
        ·
          refine ⟨39725719742277723960963251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26483813161518482640642167 39725719742277723960963251)
          ·
            refine ⟨59588579613416585941444877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39725719742277723960963251 59588579613416585941444877)
            ·
              refine ⟨22345717355031219728041829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59588579613416585941444877 22345717355031219728041829)
              ·
                refine ⟨4189822004068353699007843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22345717355031219728041829 4189822004068353699007843)
                ·
                  refine ⟨6284733006102530548511765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189822004068353699007843 6284733006102530548511765)
                  ·
                    refine ⟨294596859661056119461489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6284733006102530548511765 294596859661056119461489)
                    ·
                      rfl

theorem cell22_860588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_860588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860588 prefixEnd_860588 := by exact prefixLift 860588
  have htrace : WordTrace (prefixWord ++ tailWord_860588) baseStart_860588 baseEnd_860588 := by
    simpa [prefixWord, tailWord_860588, baseEnd_860588] using wordTrace_append hprefix tailTrace_860588
  have hstable : (prefixWord ++ tailWord_860588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860588).length < 2 ^ (prefixWord ++ tailWord_860588).sum := by decide
  have hdescent : baseEnd_860588 < baseStart_860588 := by decide
  rcases family_descends (prefixWord ++ tailWord_860588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860605 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_860605 : Nat := 118140960795 + 860605 * 2 ^ 59
def prefixEnd_860605 : Nat := 4983230072969 + 3 ^ 40 * 860605 * 2
def baseEnd_860605 : Nat := 294602679108473741786437

theorem tailTrace_860605 : CollatzResearch.WordTrace tailWord_860605 prefixEnd_860605 294602679108473741786437 := by
  unfold tailWord_860605
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388843047182539477463269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20925895364788359651642179 31388843047182539477463269)
  ·
    refine ⟨5885408071346726152024363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31388843047182539477463269 5885408071346726152024363)
    ·
      refine ⟨8828112107020089228036545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885408071346726152024363 8828112107020089228036545)
      ·
        refine ⟨6621084080265066921027409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8828112107020089228036545 6621084080265066921027409)
        ·
          refine ⟨4965813060198800190770557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6621084080265066921027409 4965813060198800190770557)
          ·
            refine ⟨1862179897574550071538959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965813060198800190770557 1862179897574550071538959)
            ·
              refine ⟨2793269846361825107308439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862179897574550071538959 2793269846361825107308439)
              ·
                refine ⟨4189904769542737660962659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793269846361825107308439 4189904769542737660962659)
                ·
                  refine ⟨6284857154314106491443989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189904769542737660962659 6284857154314106491443989)
                  ·
                    refine ⟨294602679108473741786437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6284857154314106491443989 294602679108473741786437)
                    ·
                      rfl

theorem cell22_860605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_860605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860605 prefixEnd_860605 := by exact prefixLift 860605
  have htrace : WordTrace (prefixWord ++ tailWord_860605) baseStart_860605 baseEnd_860605 := by
    simpa [prefixWord, tailWord_860605, baseEnd_860605] using wordTrace_append hprefix tailTrace_860605
  have hstable : (prefixWord ++ tailWord_860605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860605).length < 2 ^ (prefixWord ++ tailWord_860605).sum := by decide
  have hdescent : baseEnd_860605 < baseStart_860605 := by decide
  rcases family_descends (prefixWord ++ tailWord_860605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860620 : List Nat := [2, 2, 1, 4, 3, 1, 9]
def baseStart_860620 : Nat := 118140960795 + 860620 * 2 ^ 59
def prefixEnd_860620 : Nat := 4983230072969 + 3 ^ 40 * 860620 * 2
def baseEnd_860620 : Nat := 10911400515371063061533

theorem tailTrace_860620 : CollatzResearch.WordTrace tailWord_860620 prefixEnd_860620 10911400515371063061533 := by
  unfold tailWord_860620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15694695071064098519629657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20926260094752131359506209 15694695071064098519629657)
  ·
    refine ⟨11771021303298073889722243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15694695071064098519629657 11771021303298073889722243)
    ·
      refine ⟨17656531954947110834583365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771021303298073889722243 17656531954947110834583365)
      ·
        refine ⟨3310599741552583281484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17656531954947110834583365 3310599741552583281484381)
        ·
          refine ⟨1241474903082218730556643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3310599741552583281484381 1241474903082218730556643)
          ·
            refine ⟨1862212354623328095834965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241474903082218730556643 1862212354623328095834965)
            ·
              refine ⟨10911400515371063061533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1862212354623328095834965 10911400515371063061533)
              ·
                rfl

theorem cell22_860620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 9].length) (baseStart_860620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860620 prefixEnd_860620 := by exact prefixLift 860620
  have htrace : WordTrace (prefixWord ++ tailWord_860620) baseStart_860620 baseEnd_860620 := by
    simpa [prefixWord, tailWord_860620, baseEnd_860620] using wordTrace_append hprefix tailTrace_860620
  have hstable : (prefixWord ++ tailWord_860620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860620).length < 2 ^ (prefixWord ++ tailWord_860620).sum := by decide
  have hdescent : baseEnd_860620 < baseStart_860620 := by decide
  rcases family_descends (prefixWord ++ tailWord_860620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860727 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 4]
def baseStart_860727 : Nat := 118140960795 + 860727 * 2 ^ 59
def prefixEnd_860727 : Nat := 4983230072969 + 3 ^ 40 * 860727 * 2
def baseEnd_860727 : Nat := 98214814067235363412021

theorem tailTrace_860727 : CollatzResearch.WordTrace tailWord_860727 prefixEnd_860727 98214814067235363412021 := by
  unfold tailWord_860727
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393292752740554313404435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20928861835160369542269623 31393292752740554313404435)
  ·
    refine ⟨47089939129110831470106653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393292752740554313404435 47089939129110831470106653)
    ·
      refine ⟨17658727173416561801289995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47089939129110831470106653 17658727173416561801289995)
      ·
        refine ⟨26488090760124842701934993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17658727173416561801289995 26488090760124842701934993)
        ·
          refine ⟨19866068070093632026451245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26488090760124842701934993 19866068070093632026451245)
          ·
            refine ⟨7449775526285112009919217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19866068070093632026451245 7449775526285112009919217)
            ·
              refine ⟨5587331644713834007439413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449775526285112009919217 5587331644713834007439413)
              ·
                refine ⟨523812341691921938197445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5587331644713834007439413 523812341691921938197445)
                ·
                  refine ⟨98214814067235363412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523812341691921938197445 98214814067235363412021)
                  ·
                    rfl

theorem cell22_860727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 4].length) (baseStart_860727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_860727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_860727 prefixEnd_860727 := by exact prefixLift 860727
  have htrace : WordTrace (prefixWord ++ tailWord_860727) baseStart_860727 baseEnd_860727 := by
    simpa [prefixWord, tailWord_860727, baseEnd_860727] using wordTrace_append hprefix tailTrace_860727
  have hstable : (prefixWord ++ tailWord_860727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860727).length < 2 ^ (prefixWord ++ tailWord_860727).sum := by decide
  have hdescent : baseEnd_860727 < baseStart_860727 := by decide
  rcases family_descends (prefixWord ++ tailWord_860727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
