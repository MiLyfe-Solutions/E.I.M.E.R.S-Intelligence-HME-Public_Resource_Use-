import V185TrunkScan23Chunk0453

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2686117 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_2686117 : Nat := 118140960795 + 2686117 * 2 ^ 59
def prefixEnd_2686117 : Nat := 4983230072969 + 3 ^ 40 * 2686117 * 2
def baseEnd_2686117 : Nat := 1379269115213172288584279

theorem tailTrace_2686117 : CollatzResearch.WordTrace tailWord_2686117 prefixEnd_2686117 1379269115213172288584279 := by
  unfold tailWord_2686117
  simp only [CollatzResearch.WordTrace]
  refine ⟨97970735609664336105576605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65313823739776224070384403 97970735609664336105576605)
  ·
    refine ⟨36739025853624126039591227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97970735609664336105576605 36739025853624126039591227)
    ·
      refine ⟨55108538780436189059386841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36739025853624126039591227 55108538780436189059386841)
      ·
        refine ⟨41331404085327141794540131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55108538780436189059386841 41331404085327141794540131)
        ·
          refine ⟨61997106127990712691810197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41331404085327141794540131 61997106127990712691810197)
          ·
            refine ⟨2906114349749564657428603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61997106127990712691810197 2906114349749564657428603)
            ·
              refine ⟨4359171524624346986142905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906114349749564657428603 4359171524624346986142905)
              ·
                refine ⟨3269378643468260239607179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359171524624346986142905 3269378643468260239607179)
                ·
                  refine ⟨4904067965202390359410769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269378643468260239607179 4904067965202390359410769)
                  ·
                    refine ⟨3678050973901792769558077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904067965202390359410769 3678050973901792769558077)
                    ·
                      refine ⟨1379269115213172288584279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678050973901792769558077 1379269115213172288584279)
                      ·
                        rfl

theorem cell23_2686117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_2686117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686117 prefixEnd_2686117 := by exact prefixLift 2686117
  have htrace : WordTrace (prefixWord ++ tailWord_2686117) baseStart_2686117 baseEnd_2686117 := by
    simpa [prefixWord, tailWord_2686117, baseEnd_2686117] using wordTrace_append hprefix tailTrace_2686117
  have hstable : (prefixWord ++ tailWord_2686117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686117).length < 2 ^ (prefixWord ++ tailWord_2686117).sum := by decide
  have hdescent : baseEnd_2686117 < baseStart_2686117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686130 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_2686130 : Nat := 118140960795 + 2686130 * 2 ^ 59
def prefixEnd_2686130 : Nat := 4983230072969 + 3 ^ 40 * 2686130 * 2
def baseEnd_2686130 : Nat := 1379275790461680737721719

theorem tailTrace_2686130 : CollatzResearch.WordTrace tailWord_2686130 prefixEnd_2686130 1379275790461680737721719 := by
  unfold tailWord_2686130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492802439654309831449961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65314139839078159550533229 24492802439654309831449961)
  ·
    refine ⟨18369601829740732373587471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24492802439654309831449961 18369601829740732373587471)
    ·
      refine ⟨27554402744611098560381207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18369601829740732373587471 27554402744611098560381207)
      ·
        refine ⟨41331604116916647840571811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27554402744611098560381207 41331604116916647840571811)
        ·
          refine ⟨61997406175374971760857717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41331604116916647840571811 61997406175374971760857717)
          ·
            refine ⟨5812256828941403602580411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61997406175374971760857717 5812256828941403602580411)
            ·
              refine ⟨8718385243412105403870617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812256828941403602580411 8718385243412105403870617)
              ·
                refine ⟨6538788932559079052902963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718385243412105403870617 6538788932559079052902963)
                ·
                  refine ⟨9808183398838618579354445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538788932559079052902963 9808183398838618579354445)
                  ·
                    refine ⟨3678068774564481967257917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9808183398838618579354445 3678068774564481967257917)
                    ·
                      refine ⟨1379275790461680737721719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678068774564481967257917 1379275790461680737721719)
                      ·
                        rfl

theorem cell23_2686130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_2686130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686130 prefixEnd_2686130 := by exact prefixLift 2686130
  have htrace : WordTrace (prefixWord ++ tailWord_2686130) baseStart_2686130 baseEnd_2686130 := by
    simpa [prefixWord, tailWord_2686130, baseEnd_2686130] using wordTrace_append hprefix tailTrace_2686130
  have hstable : (prefixWord ++ tailWord_2686130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686130).length < 2 ^ (prefixWord ++ tailWord_2686130).sum := by decide
  have hdescent : baseEnd_2686130 < baseStart_2686130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686164 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2686164 : Nat := 118140960795 + 2686164 * 2 ^ 59
def prefixEnd_2686164 : Nat := 4983230072969 + 3 ^ 40 * 2686164 * 2
def baseEnd_2686164 : Nat := 1379293248803933604696563

theorem tailTrace_2686164 : CollatzResearch.WordTrace tailWord_2686164 prefixEnd_2686164 1379293248803933604696563 := by
  unfold tailWord_2686164
  simp only [CollatzResearch.WordTrace]
  refine ⟨48986224920247031566268773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65314966560329375421691697 48986224920247031566268773)
  ·
    refine ⟨9184917172546318418675395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48986224920247031566268773 9184917172546318418675395)
    ·
      refine ⟨13777375758819477628013093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184917172546318418675395 13777375758819477628013093)
      ·
        refine ⟨2583257954778652055252455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13777375758819477628013093 2583257954778652055252455)
        ·
          refine ⟨3874886932167978082878683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583257954778652055252455 3874886932167978082878683)
          ·
            refine ⟨5812330398251967124318025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874886932167978082878683 5812330398251967124318025)
            ·
              refine ⟨4359247798688975343238519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812330398251967124318025 4359247798688975343238519)
              ·
                refine ⟨6538871698033463014857779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359247798688975343238519 6538871698033463014857779)
                ·
                  refine ⟨9808307547050194522286669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538871698033463014857779 9808307547050194522286669)
                  ·
                    refine ⟨3678115330143822945857501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9808307547050194522286669 3678115330143822945857501)
                    ·
                      refine ⟨1379293248803933604696563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678115330143822945857501 1379293248803933604696563)
                      ·
                        rfl

theorem cell23_2686164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2686164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686164 prefixEnd_2686164 := by exact prefixLift 2686164
  have htrace : WordTrace (prefixWord ++ tailWord_2686164) baseStart_2686164 baseEnd_2686164 := by
    simpa [prefixWord, tailWord_2686164, baseEnd_2686164] using wordTrace_append hprefix tailTrace_2686164
  have hstable : (prefixWord ++ tailWord_2686164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686164).length < 2 ^ (prefixWord ++ tailWord_2686164).sum := by decide
  have hdescent : baseEnd_2686164 < baseStart_2686164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686191 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 1, 3, 2]
def baseStart_2686191 : Nat := 118140960795 + 2686191 * 2 ^ 59
def prefixEnd_2686191 : Nat := 4983230072969 + 3 ^ 40 * 2686191 * 2
def baseEnd_2686191 : Nat := 1379307112781604999058939

theorem tailTrace_2686191 : CollatzResearch.WordTrace tailWord_2686191 prefixEnd_2686191 1379307112781604999058939 := by
  unfold tailWord_2686191
  simp only [CollatzResearch.WordTrace]
  refine ⟨97973434611396246743770427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65315623074264164495846951 97973434611396246743770427)
  ·
    refine ⟨146960151917094370115655641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97973434611396246743770427 146960151917094370115655641)
    ·
      refine ⟨110220113937820777586741731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146960151917094370115655641 110220113937820777586741731)
      ·
        refine ⟨165330170906731166380112597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110220113937820777586741731 165330170906731166380112597)
        ·
          refine ⟨3874925880626511712033889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 165330170906731166380112597 3874925880626511712033889)
          ·
            refine ⟨2906194410469883784025417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874925880626511712033889 2906194410469883784025417)
            ·
              refine ⟨2179645807852412838019063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906194410469883784025417 2179645807852412838019063)
              ·
                refine ⟨3269468711778619257028595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179645807852412838019063 3269468711778619257028595)
                ·
                  refine ⟨4904203067667928885542893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269468711778619257028595 4904203067667928885542893)
                  ·
                    refine ⟨1839076150375473332078585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4904203067667928885542893 1839076150375473332078585)
                    ·
                      refine ⟨1379307112781604999058939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839076150375473332078585 1379307112781604999058939)
                      ·
                        rfl

theorem cell23_2686191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 3, 2].length) (baseStart_2686191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686191 prefixEnd_2686191 := by exact prefixLift 2686191
  have htrace : WordTrace (prefixWord ++ tailWord_2686191) baseStart_2686191 baseEnd_2686191 := by
    simpa [prefixWord, tailWord_2686191, baseEnd_2686191] using wordTrace_append hprefix tailTrace_2686191
  have hstable : (prefixWord ++ tailWord_2686191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686191).length < 2 ^ (prefixWord ++ tailWord_2686191).sum := by decide
  have hdescent : baseEnd_2686191 < baseStart_2686191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686204 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_2686204 : Nat := 118140960795 + 2686204 * 2 ^ 59
def prefixEnd_2686204 : Nat := 4983230072969 + 3 ^ 40 * 2686204 * 2
def baseEnd_2686204 : Nat := 1379313788030113448196379

theorem tailTrace_2686204 : CollatzResearch.WordTrace tailWord_2686204 prefixEnd_2686204 1379313788030113448196379 := by
  unfold tailWord_2686204
  simp only [CollatzResearch.WordTrace]
  refine ⟨48986954380174574981996833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65315939173566099975995777 48986954380174574981996833)
  ·
    refine ⟨36740215785130931236497625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48986954380174574981996833 36740215785130931236497625)
    ·
      refine ⟨27555161838848198427373219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36740215785130931236497625 27555161838848198427373219)
      ·
        refine ⟨41332742758272297641059829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27555161838848198427373219 41332742758272297641059829)
        ·
          refine ⟨3874944633588027903849359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41332742758272297641059829 3874944633588027903849359)
          ·
            refine ⟨5812416950382041855774039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874944633588027903849359 5812416950382041855774039)
            ·
              refine ⟨8718625425573062783661059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812416950382041855774039 8718625425573062783661059)
              ·
                refine ⟨13077938138359594175491589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718625425573062783661059 13077938138359594175491589)
                ·
                  refine ⟨2452113400942423907904673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13077938138359594175491589 2452113400942423907904673)
                  ·
                    refine ⟨1839085050706817930928505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452113400942423907904673 1839085050706817930928505)
                    ·
                      refine ⟨1379313788030113448196379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839085050706817930928505 1379313788030113448196379)
                      ·
                        rfl

theorem cell23_2686204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_2686204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686204 prefixEnd_2686204 := by exact prefixLift 2686204
  have htrace : WordTrace (prefixWord ++ tailWord_2686204) baseStart_2686204 baseEnd_2686204 := by
    simpa [prefixWord, tailWord_2686204, baseEnd_2686204] using wordTrace_append hprefix tailTrace_2686204
  have hstable : (prefixWord ++ tailWord_2686204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686204).length < 2 ^ (prefixWord ++ tailWord_2686204).sum := by decide
  have hdescent : baseEnd_2686204 < baseStart_2686204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686220 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2686220 : Nat := 118140960795 + 2686220 * 2 ^ 59
def prefixEnd_2686220 : Nat := 4983230072969 + 3 ^ 40 * 2686220 * 2
def baseEnd_2686220 : Nat := 1379322003720585385596305

theorem tailTrace_2686220 : CollatzResearch.WordTrace tailWord_2686220 prefixEnd_2686220 1379322003720585385596305 := by
  unfold tailWord_2686220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48987246164145592348288057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65316328218860789797717409 48987246164145592348288057)
  ·
    refine ⟨36740434623109194261216043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48987246164145592348288057 36740434623109194261216043)
    ·
      refine ⟨55110651934663791391824065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36740434623109194261216043 55110651934663791391824065)
      ·
        refine ⟨41332988950997843543868049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55110651934663791391824065 41332988950997843543868049)
        ·
          refine ⟨30999741713248382657901037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41332988950997843543868049 30999741713248382657901037)
          ·
            refine ⟨11624903142468143496712889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30999741713248382657901037 11624903142468143496712889)
            ·
              refine ⟨8718677356851107622534667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11624903142468143496712889 8718677356851107622534667)
              ·
                refine ⟨13078016035276661433802001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718677356851107622534667 13078016035276661433802001)
                ·
                  refine ⟨9808512026457496075351501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13078016035276661433802001 9808512026457496075351501)
                  ·
                    refine ⟨3678192009921561028256813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9808512026457496075351501 3678192009921561028256813)
                    ·
                      refine ⟨1379322003720585385596305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678192009921561028256813 1379322003720585385596305)
                      ·
                        rfl

theorem cell23_2686220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2686220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686220 prefixEnd_2686220 := by exact prefixLift 2686220
  have htrace : WordTrace (prefixWord ++ tailWord_2686220) baseStart_2686220 baseEnd_2686220 := by
    simpa [prefixWord, tailWord_2686220, baseEnd_2686220] using wordTrace_append hprefix tailTrace_2686220
  have hstable : (prefixWord ++ tailWord_2686220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686220).length < 2 ^ (prefixWord ++ tailWord_2686220).sum := by decide
  have hdescent : baseEnd_2686220 < baseStart_2686220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686280 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_2686280 : Nat := 118140960795 + 2686280 * 2 ^ 59
def prefixEnd_2686280 : Nat := 4983230072969 + 3 ^ 40 * 2686280 * 2
def baseEnd_2686280 : Nat := 1379352812559855150846029

theorem tailTrace_2686280 : CollatzResearch.WordTrace tailWord_2686280 prefixEnd_2686280 1379352812559855150846029 := by
  unfold tailWord_2686280
  simp only [CollatzResearch.WordTrace]
  refine ⟨48988340354036907471880147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65317787138715876629173529 48988340354036907471880147)
  ·
    refine ⟨73482510531055361207820221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48988340354036907471880147 73482510531055361207820221)
    ·
      refine ⟨27555941449145760452932583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73482510531055361207820221 27555941449145760452932583)
      ·
        refine ⟨41333912173718640679398875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27555941449145760452932583 41333912173718640679398875)
        ·
          refine ⟨62000868260577961019098313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41333912173718640679398875 62000868260577961019098313)
          ·
            refine ⟨46500651195433470764323735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62000868260577961019098313 46500651195433470764323735)
            ·
              refine ⟨69750976793150206146485603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46500651195433470764323735 69750976793150206146485603)
              ·
                refine ⟨104626465189725309219728405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69750976793150206146485603 104626465189725309219728405)
                ·
                  refine ⟨4904365555768373869674769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104626465189725309219728405 4904365555768373869674769)
                  ·
                    refine ⟨3678274166826280402256077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904365555768373869674769 3678274166826280402256077)
                    ·
                      refine ⟨1379352812559855150846029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678274166826280402256077 1379352812559855150846029)
                      ·
                        rfl

theorem cell23_2686280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_2686280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686280 prefixEnd_2686280 := by exact prefixLift 2686280
  have htrace : WordTrace (prefixWord ++ tailWord_2686280) baseStart_2686280 baseEnd_2686280 := by
    simpa [prefixWord, tailWord_2686280, baseEnd_2686280] using wordTrace_append hprefix tailTrace_2686280
  have hstable : (prefixWord ++ tailWord_2686280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686280).length < 2 ^ (prefixWord ++ tailWord_2686280).sum := by decide
  have hdescent : baseEnd_2686280 < baseStart_2686280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686303 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2686303 : Nat := 118140960795 + 2686303 * 2 ^ 59
def prefixEnd_2686303 : Nat := 4983230072969 + 3 ^ 40 * 2686303 * 2
def baseEnd_2686303 : Nat := 1379364622614908560858423

theorem tailTrace_2686303 : CollatzResearch.WordTrace tailWord_2686303 prefixEnd_2686303 1379364622614908560858423 := by
  unfold tailWord_2686303
  simp only [CollatzResearch.WordTrace]
  refine ⟨97977519586990489871847563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65318346391326993247898375 97977519586990489871847563)
  ·
    refine ⟨146966279380485734807771345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97977519586990489871847563 146966279380485734807771345)
    ·
      refine ⟨110224709535364301105828509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146966279380485734807771345 110224709535364301105828509)
      ·
        refine ⟨41334266075761612914685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110224709535364301105828509 41334266075761612914685691)
        ·
          refine ⟨62001399113642419372028537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41334266075761612914685691 62001399113642419372028537)
          ·
            refine ⟨46501049335231814529021403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62001399113642419372028537 46501049335231814529021403)
            ·
              refine ⟨69751574002847721793532105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46501049335231814529021403 69751574002847721793532105)
              ·
                refine ⟨52313680502135791345149079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69751574002847721793532105 52313680502135791345149079)
                ·
                  refine ⟨78470520753203687017723619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52313680502135791345149079 78470520753203687017723619)
                  ·
                    refine ⟨117705781129805530526585429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78470520753203687017723619 117705781129805530526585429)
                    ·
                      refine ⟨1379364622614908560858423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117705781129805530526585429 1379364622614908560858423)
                      ·
                        rfl

theorem cell23_2686303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2686303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686303 prefixEnd_2686303 := by exact prefixLift 2686303
  have htrace : WordTrace (prefixWord ++ tailWord_2686303) baseStart_2686303 baseEnd_2686303 := by
    simpa [prefixWord, tailWord_2686303, baseEnd_2686303] using wordTrace_append hprefix tailTrace_2686303
  have hstable : (prefixWord ++ tailWord_2686303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686303).length < 2 ^ (prefixWord ++ tailWord_2686303).sum := by decide
  have hdescent : baseEnd_2686303 < baseStart_2686303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686317 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2686317 : Nat := 118140960795 + 2686317 * 2 ^ 59
def prefixEnd_2686317 : Nat := 4983230072969 + 3 ^ 40 * 2686317 * 2
def baseEnd_2686317 : Nat := 153263534593785722898151

theorem tailTrace_2686317 : CollatzResearch.WordTrace tailWord_2686317 prefixEnd_2686317 153263534593785722898151 := by
  unfold tailWord_2686317
  simp only [CollatzResearch.WordTrace]
  refine ⟨97978030208939770262857205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65318686805959846841904803 97978030208939770262857205)
  ·
    refine ⟨9185440332088103462142863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97978030208939770262857205 9185440332088103462142863)
    ·
      refine ⟨13778160498132155193214295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185440332088103462142863 13778160498132155193214295)
      ·
        refine ⟨20667240747198232789821443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13778160498132155193214295 20667240747198232789821443)
        ·
          refine ⟨31000861120797349184732165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20667240747198232789821443 31000861120797349184732165)
          ·
            refine ⟨5812661460149502972137281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31000861120797349184732165 5812661460149502972137281)
            ·
              refine ⟨4359496095112127229102961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812661460149502972137281 4359496095112127229102961)
              ·
                refine ⟨3269622071334095421827221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359496095112127229102961 3269622071334095421827221)
                ·
                  refine ⟨153263534593785722898151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3269622071334095421827221 153263534593785722898151)
                  ·
                    rfl

theorem cell23_2686317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2686317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686317 prefixEnd_2686317 := by exact prefixLift 2686317
  have htrace : WordTrace (prefixWord ++ tailWord_2686317) baseStart_2686317 baseEnd_2686317 := by
    simpa [prefixWord, tailWord_2686317, baseEnd_2686317] using wordTrace_append hprefix tailTrace_2686317
  have hstable : (prefixWord ++ tailWord_2686317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686317).length < 2 ^ (prefixWord ++ tailWord_2686317).sum := by decide
  have hdescent : baseEnd_2686317 < baseStart_2686317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686323 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_2686323 : Nat := 118140960795 + 2686323 * 2 ^ 59
def prefixEnd_2686323 : Nat := 4983230072969 + 3 ^ 40 * 2686323 * 2
def baseEnd_2686323 : Nat := 1379374892227998482608331

theorem tailTrace_2686323 : CollatzResearch.WordTrace tailWord_2686323 prefixEnd_2686323 1379374892227998482608331 := by
  unfold tailWord_2686323
  simp only [CollatzResearch.WordTrace]
  refine ⟨97978249046918033287575623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65318832697945355525050415 97978249046918033287575623)
  ·
    refine ⟨146967373570377049931363435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97978249046918033287575623 146967373570377049931363435)
    ·
      refine ⟨220451060355565574897045153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146967373570377049931363435 220451060355565574897045153)
      ·
        refine ⟨165338295266674181172783865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220451060355565574897045153 165338295266674181172783865)
        ·
          refine ⟨124003721450005635879587899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165338295266674181172783865 124003721450005635879587899)
          ·
            refine ⟨186005582175008453819381849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124003721450005635879587899 186005582175008453819381849)
            ·
              refine ⟨139504186631256340364536387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186005582175008453819381849 139504186631256340364536387)
              ·
                refine ⟨209256279946884510546804581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139504186631256340364536387 209256279946884510546804581)
                ·
                  refine ⟨39235552490040845727525859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209256279946884510546804581 39235552490040845727525859)
                  ·
                    refine ⟨58853328735061268591288789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39235552490040845727525859 58853328735061268591288789)
                    ·
                      refine ⟨1379374892227998482608331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58853328735061268591288789 1379374892227998482608331)
                      ·
                        rfl

theorem cell23_2686323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_2686323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686323 prefixEnd_2686323 := by exact prefixLift 2686323
  have htrace : WordTrace (prefixWord ++ tailWord_2686323) baseStart_2686323 baseEnd_2686323 := by
    simpa [prefixWord, tailWord_2686323, baseEnd_2686323] using wordTrace_append hprefix tailTrace_2686323
  have hstable : (prefixWord ++ tailWord_2686323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686323).length < 2 ^ (prefixWord ++ tailWord_2686323).sum := by decide
  have hdescent : baseEnd_2686323 < baseStart_2686323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686327 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_2686327 : Nat := 118140960795 + 2686327 * 2 ^ 59
def prefixEnd_2686327 : Nat := 4983230072969 + 3 ^ 40 * 2686327 * 2
def baseEnd_2686327 : Nat := 1379376946150616466958313

theorem tailTrace_2686327 : CollatzResearch.WordTrace tailWord_2686327 prefixEnd_2686327 1379376946150616466958313 := by
  unfold tailWord_2686327
  simp only [CollatzResearch.WordTrace]
  refine ⟨97978394938903541970721235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65318929959269027980480823 97978394938903541970721235)
  ·
    refine ⟨146967592408355312956081853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97978394938903541970721235 146967592408355312956081853)
    ·
      refine ⟨55112847153133242358530695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146967592408355312956081853 55112847153133242358530695)
      ·
        refine ⟨82669270729699863537796043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55112847153133242358530695 82669270729699863537796043)
        ·
          refine ⟨124003906094549795306694065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82669270729699863537796043 124003906094549795306694065)
          ·
            refine ⟨93002929570912346480020549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124003906094549795306694065 93002929570912346480020549)
            ·
              refine ⟨17438049294546064965003853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93002929570912346480020549 17438049294546064965003853)
              ·
                refine ⟨6539268485454774361876445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17438049294546064965003853 6539268485454774361876445)
                ·
                  refine ⟨2452225682045540385703667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6539268485454774361876445 2452225682045540385703667)
                  ·
                    refine ⟨3678338523068310578555501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452225682045540385703667 3678338523068310578555501)
                    ·
                      refine ⟨1379376946150616466958313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678338523068310578555501 1379376946150616466958313)
                      ·
                        rfl

theorem cell23_2686327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_2686327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686327 prefixEnd_2686327 := by exact prefixLift 2686327
  have htrace : WordTrace (prefixWord ++ tailWord_2686327) baseStart_2686327 baseEnd_2686327 := by
    simpa [prefixWord, tailWord_2686327, baseEnd_2686327] using wordTrace_append hprefix tailTrace_2686327
  have hstable : (prefixWord ++ tailWord_2686327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686327).length < 2 ^ (prefixWord ++ tailWord_2686327).sum := by decide
  have hdescent : baseEnd_2686327 < baseStart_2686327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686344 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2686344 : Nat := 118140960795 + 2686344 * 2 ^ 59
def prefixEnd_2686344 : Nat := 4983230072969 + 3 ^ 40 * 2686344 * 2
def baseEnd_2686344 : Nat := 1379385675321742900445735

theorem tailTrace_2686344 : CollatzResearch.WordTrace tailWord_2686344 prefixEnd_2686344 1379385675321742900445735 := by
  unfold tailWord_2686344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48989507489920976937045043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65319343319894635916060057 48989507489920976937045043)
  ·
    refine ⟨73484261234881465405567565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48989507489920976937045043 73484261234881465405567565)
    ·
      refine ⟨27556597963080549527087837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73484261234881465405567565 27556597963080549527087837)
      ·
        refine ⟨10333724236155206072657939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27556597963080549527087837 10333724236155206072657939)
        ·
          refine ⟨15500586354232809108986909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10333724236155206072657939 15500586354232809108986909)
          ·
            refine ⟨5812719882837303415870091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15500586354232809108986909 5812719882837303415870091)
            ·
              refine ⟨8719079824255955123805137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812719882837303415870091 8719079824255955123805137)
              ·
                refine ⟨6539309868191966342853853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719079824255955123805137 6539309868191966342853853)
                ·
                  refine ⟨2452241200571987378570195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6539309868191966342853853 2452241200571987378570195)
                  ·
                    refine ⟨3678361800857981067855293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452241200571987378570195 3678361800857981067855293)
                    ·
                      refine ⟨1379385675321742900445735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678361800857981067855293 1379385675321742900445735)
                      ·
                        rfl

theorem cell23_2686344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2686344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686344 prefixEnd_2686344 := by exact prefixLift 2686344
  have htrace : WordTrace (prefixWord ++ tailWord_2686344) baseStart_2686344 baseEnd_2686344 := by
    simpa [prefixWord, tailWord_2686344, baseEnd_2686344] using wordTrace_append hprefix tailTrace_2686344
  have hstable : (prefixWord ++ tailWord_2686344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686344).length < 2 ^ (prefixWord ++ tailWord_2686344).sum := by decide
  have hdescent : baseEnd_2686344 < baseStart_2686344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686361 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 1, 1, 3]
def baseStart_2686361 : Nat := 118140960795 + 2686361 * 2 ^ 59
def prefixEnd_2686361 : Nat := 4983230072969 + 3 ^ 40 * 2686361 * 2
def baseEnd_2686361 : Nat := 1379394404492869333933157

theorem tailTrace_2686361 : CollatzResearch.WordTrace tailWord_2686361 prefixEnd_2686361 1379394404492869333933157 := by
  unfold tailWord_2686361
  simp only [CollatzResearch.WordTrace]
  refine ⟨97979635020780365777458937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65319756680520243851639291 97979635020780365777458937)
  ·
    refine ⟨73484726265585274333094203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97979635020780365777458937 73484726265585274333094203)
    ·
      refine ⟨110227089398377911499641305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73484726265585274333094203 110227089398377911499641305)
      ·
        refine ⟨82670317048783433624730979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110227089398377911499641305 82670317048783433624730979)
        ·
          refine ⟨124005475573175150437096469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82670317048783433624730979 124005475573175150437096469)
          ·
            refine ⟨5812756667492585176738897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124005475573175150437096469 5812756667492585176738897)
            ·
              refine ⟨4359567500619438882554173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812756667492585176738897 4359567500619438882554173)
              ·
                refine ⟨1634837812732289580957815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4359567500619438882554173 1634837812732289580957815)
                ·
                  refine ⟨2452256719098434371436723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634837812732289580957815 2452256719098434371436723)
                  ·
                    refine ⟨3678385078647651557155085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2452256719098434371436723 3678385078647651557155085)
                    ·
                      refine ⟨1379394404492869333933157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678385078647651557155085 1379394404492869333933157)
                      ·
                        rfl

theorem cell23_2686361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_2686361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686361 prefixEnd_2686361 := by exact prefixLift 2686361
  have htrace : WordTrace (prefixWord ++ tailWord_2686361) baseStart_2686361 baseEnd_2686361 := by
    simpa [prefixWord, tailWord_2686361, baseEnd_2686361] using wordTrace_append hprefix tailTrace_2686361
  have hstable : (prefixWord ++ tailWord_2686361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686361).length < 2 ^ (prefixWord ++ tailWord_2686361).sum := by decide
  have hdescent : baseEnd_2686361 < baseStart_2686361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686380 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_2686380 : Nat := 118140960795 + 2686380 * 2 ^ 59
def prefixEnd_2686380 : Nat := 4983230072969 + 3 ^ 40 * 2686380 * 2
def baseEnd_2686380 : Nat := 1379404160625304759595569

theorem tailTrace_2686380 : CollatzResearch.WordTrace tailWord_2686380 prefixEnd_2686380 1379404160625304759595569 := by
  unfold tailWord_2686380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48990164003855766011200297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65320218671807688014933729 48990164003855766011200297)
  ·
    refine ⟨36742623002891824508400223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48990164003855766011200297 36742623002891824508400223)
    ·
      refine ⟨55113934504337736762600335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36742623002891824508400223 55113934504337736762600335)
      ·
        refine ⟨82670901756506605143900503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55113934504337736762600335 82670901756506605143900503)
        ·
          refine ⟨124006352634759907715850755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82670901756506605143900503 124006352634759907715850755)
          ·
            refine ⟨186009528952139861573776133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124006352634759907715850755 186009528952139861573776133)
            ·
              refine ⟨34876786678526224045083025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186009528952139861573776133 34876786678526224045083025)
              ·
                refine ⟨26157590008894668033812269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34876786678526224045083025 26157590008894668033812269)
                ·
                  refine ⟨9809096253335500512679601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26157590008894668033812269 9809096253335500512679601)
                  ·
                    refine ⟨7356822190001625384509701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9809096253335500512679601 7356822190001625384509701)
                    ·
                      refine ⟨1379404160625304759595569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7356822190001625384509701 1379404160625304759595569)
                      ·
                        rfl

theorem cell23_2686380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_2686380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686380 prefixEnd_2686380 := by exact prefixLift 2686380
  have htrace : WordTrace (prefixWord ++ tailWord_2686380) baseStart_2686380 baseEnd_2686380 := by
    simpa [prefixWord, tailWord_2686380, baseEnd_2686380] using wordTrace_append hprefix tailTrace_2686380
  have hstable : (prefixWord ++ tailWord_2686380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686380).length < 2 ^ (prefixWord ++ tailWord_2686380).sum := by decide
  have hdescent : baseEnd_2686380 < baseStart_2686380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686435 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2686435 : Nat := 118140960795 + 2686435 * 2 ^ 59
def prefixEnd_2686435 : Nat := 4983230072969 + 3 ^ 40 * 2686435 * 2
def baseEnd_2686435 : Nat := 1379432402061302044407817

theorem tailTrace_2686435 : CollatzResearch.WordTrace tailWord_2686435 prefixEnd_2686435 1379432402061302044407817 := by
  unfold tailWord_2686435
  simp only [CollatzResearch.WordTrace]
  refine ⟨97982334022512276415652759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65321556015008184277101839 97982334022512276415652759)
  ·
    refine ⟨146973501033768414623479139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97982334022512276415652759 146973501033768414623479139)
    ·
      refine ⟨220460251550652621935218709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146973501033768414623479139 220460251550652621935218709)
      ·
        refine ⟨10334074291436841653213377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 220460251550652621935218709 10334074291436841653213377)
        ·
          refine ⟨7750555718577631239910033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10334074291436841653213377 7750555718577631239910033)
          ·
            refine ⟨5812916788933223429932525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750555718577631239910033 5812916788933223429932525)
            ·
              refine ⟨2179843795849958786224697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5812916788933223429932525 2179843795849958786224697)
              ·
                refine ⟨1634882846887469089668523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179843795849958786224697 1634882846887469089668523)
                ·
                  refine ⟨2452324270331203634502785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634882846887469089668523 2452324270331203634502785)
                  ·
                    refine ⟨1839243202748402725877089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452324270331203634502785 1839243202748402725877089)
                    ·
                      refine ⟨1379432402061302044407817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839243202748402725877089 1379432402061302044407817)
                      ·
                        rfl

theorem cell23_2686435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2686435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686435 prefixEnd_2686435 := by exact prefixLift 2686435
  have htrace : WordTrace (prefixWord ++ tailWord_2686435) baseStart_2686435 baseEnd_2686435 := by
    simpa [prefixWord, tailWord_2686435, baseEnd_2686435] using wordTrace_append hprefix tailTrace_2686435
  have hstable : (prefixWord ++ tailWord_2686435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686435).length < 2 ^ (prefixWord ++ tailWord_2686435).sum := by decide
  have hdescent : baseEnd_2686435 < baseStart_2686435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686445 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2686445 : Nat := 118140960795 + 2686445 * 2 ^ 59
def prefixEnd_2686445 : Nat := 4983230072969 + 3 ^ 40 * 2686445 * 2
def baseEnd_2686445 : Nat := 459812512289282335094257

theorem tailTrace_2686445 : CollatzResearch.WordTrace tailWord_2686445 prefixEnd_2686445 459812512289282335094257 := by
  unfold tailWord_2686445
  simp only [CollatzResearch.WordTrace]
  refine ⟨97982698752476048123516789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65321799168317365415677859 97982698752476048123516789)
  ·
    refine ⟨9185878008044629511579699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97982698752476048123516789 9185878008044629511579699)
    ·
      refine ⟨13778817012066944267369549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185878008044629511579699 13778817012066944267369549)
      ·
        refine ⟨5167056379525104100263581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13778817012066944267369549 5167056379525104100263581)
        ·
          refine ⟨1937646142321914037598843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5167056379525104100263581 1937646142321914037598843)
          ·
            refine ⟨2906469213482871056398265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937646142321914037598843 2906469213482871056398265)
            ·
              refine ⟨2179851910112153292298699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906469213482871056398265 2179851910112153292298699)
              ·
                refine ⟨3269777865168229938448049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179851910112153292298699 3269777865168229938448049)
                ·
                  refine ⟨2452333398876172453836037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269777865168229938448049 2452333398876172453836037)
                  ·
                    refine ⟨459812512289282335094257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2452333398876172453836037 459812512289282335094257)
                    ·
                      rfl

theorem cell23_2686445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2686445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686445 prefixEnd_2686445 := by exact prefixLift 2686445
  have htrace : WordTrace (prefixWord ++ tailWord_2686445) baseStart_2686445 baseEnd_2686445 := by
    simpa [prefixWord, tailWord_2686445, baseEnd_2686445] using wordTrace_append hprefix tailTrace_2686445
  have hstable : (prefixWord ++ tailWord_2686445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686445).length < 2 ^ (prefixWord ++ tailWord_2686445).sum := by decide
  have hdescent : baseEnd_2686445 < baseStart_2686445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686461 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_2686461 : Nat := 118140960795 + 2686461 * 2 ^ 59
def prefixEnd_2686461 : Nat := 4983230072969 + 3 ^ 40 * 2686461 * 2
def baseEnd_2686461 : Nat := 1379445752558318942682697

theorem tailTrace_2686461 : CollatzResearch.WordTrace tailWord_2686461 prefixEnd_2686461 1379445752558318942682697 := by
  unfold tailWord_2686461
  simp only [CollatzResearch.WordTrace]
  refine ⟨97983282320418082856099237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65322188213612055237399491 97983282320418082856099237)
  ·
    refine ⟨18371865435078390535518607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97983282320418082856099237 18371865435078390535518607)
    ·
      refine ⟨27557798152617585803277911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18371865435078390535518607 27557798152617585803277911)
      ·
        refine ⟨41336697228926378704916867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27557798152617585803277911 41336697228926378704916867)
        ·
          refine ⟨62005045843389568057375301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41336697228926378704916867 62005045843389568057375301)
          ·
            refine ⟨11625946095635544010757869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62005045843389568057375301 11625946095635544010757869)
            ·
              refine ⟨4359729785863329004034201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11625946095635544010757869 4359729785863329004034201)
              ·
                refine ⟨3269797339397496753025651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359729785863329004034201 3269797339397496753025651)
                ·
                  refine ⟨4904696009096245129538477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269797339397496753025651 4904696009096245129538477)
                  ·
                    refine ⟨1839261003411091923576929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4904696009096245129538477 1839261003411091923576929)
                    ·
                      refine ⟨1379445752558318942682697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839261003411091923576929 1379445752558318942682697)
                      ·
                        rfl

theorem cell23_2686461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_2686461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686461 prefixEnd_2686461 := by exact prefixLift 2686461
  have htrace : WordTrace (prefixWord ++ tailWord_2686461) baseStart_2686461 baseEnd_2686461 := by
    simpa [prefixWord, tailWord_2686461, baseEnd_2686461] using wordTrace_append hprefix tailTrace_2686461
  have hstable : (prefixWord ++ tailWord_2686461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686461).length < 2 ^ (prefixWord ++ tailWord_2686461).sum := by decide
  have hdescent : baseEnd_2686461 < baseStart_2686461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686474 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_2686474 : Nat := 118140960795 + 2686474 * 2 ^ 59
def prefixEnd_2686474 : Nat := 4983230072969 + 3 ^ 40 * 2686474 * 2
def baseEnd_2686474 : Nat := 1379452427806827391820137

theorem tailTrace_2686474 : CollatzResearch.WordTrace tailWord_2686474 prefixEnd_2686474 1379452427806827391820137 := by
  unfold tailWord_2686474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24495939117342746519080619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65322504312913990717548317 24495939117342746519080619)
  ·
    refine ⟨36743908676014119778620929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24495939117342746519080619 36743908676014119778620929)
    ·
      refine ⟨27557931507010589833965697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36743908676014119778620929 27557931507010589833965697)
      ·
        refine ⟨20668448630257942375474273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27557931507010589833965697 20668448630257942375474273)
        ·
          refine ⟨15501336472693456781605705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20668448630257942375474273 15501336472693456781605705)
          ·
            refine ⟨11626002354520092586204279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15501336472693456781605705 11626002354520092586204279)
            ·
              refine ⟨17439003531780138879306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11626002354520092586204279 17439003531780138879306419)
              ·
                refine ⟨26158505297670208318959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17439003531780138879306419 26158505297670208318959629)
                ·
                  refine ⟨9809439486626328119609861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26158505297670208318959629 9809439486626328119609861)
                  ·
                    refine ⟨1839269903742436522426849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9809439486626328119609861 1839269903742436522426849)
                    ·
                      refine ⟨1379452427806827391820137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839269903742436522426849 1379452427806827391820137)
                      ·
                        rfl

theorem cell23_2686474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_2686474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686474 prefixEnd_2686474 := by exact prefixLift 2686474
  have htrace : WordTrace (prefixWord ++ tailWord_2686474) baseStart_2686474 baseEnd_2686474 := by
    simpa [prefixWord, tailWord_2686474, baseEnd_2686474] using wordTrace_append hprefix tailTrace_2686474
  have hstable : (prefixWord ++ tailWord_2686474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686474).length < 2 ^ (prefixWord ++ tailWord_2686474).sum := by decide
  have hdescent : baseEnd_2686474 < baseStart_2686474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686527 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 1, 7]
def baseStart_2686527 : Nat := 118140960795 + 2686527 * 2 ^ 59
def prefixEnd_2686527 : Nat := 4983230072969 + 3 ^ 40 * 2686527 * 2
def baseEnd_2686527 : Nat := 459826547427171894819131

theorem tailTrace_2686527 : CollatzResearch.WordTrace tailWord_2686527 prefixEnd_2686527 459826547427171894819131 := by
  unfold tailWord_2686527
  simp only [CollatzResearch.WordTrace]
  refine ⟨97985689538178976128001835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65323793025452650752001223 97985689538178976128001835)
  ·
    refine ⟨146978534307268464192002753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97985689538178976128001835 146978534307268464192002753)
    ·
      refine ⟨110233900730451348144002065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146978534307268464192002753 110233900730451348144002065)
      ·
        refine ⟨82675425547838511108001549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110233900730451348144002065 82675425547838511108001549)
        ·
          refine ⟨31003284580439441665500581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82675425547838511108001549 31003284580439441665500581)
          ·
            refine ⟨5813115858832395312281359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31003284580439441665500581 5813115858832395312281359)
            ·
              refine ⟨8719673788248592968422039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813115858832395312281359 8719673788248592968422039)
              ·
                refine ⟨13079510682372889452633059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719673788248592968422039 13079510682372889452633059)
                ·
                  refine ⟨19619266023559334178949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13079510682372889452633059 19619266023559334178949589)
                  ·
                    refine ⟨459826547427171894819131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19619266023559334178949589 459826547427171894819131)
                    ·
                      rfl

theorem cell23_2686527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_2686527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686527 prefixEnd_2686527 := by exact prefixLift 2686527
  have htrace : WordTrace (prefixWord ++ tailWord_2686527) baseStart_2686527 baseEnd_2686527 := by
    simpa [prefixWord, tailWord_2686527, baseEnd_2686527] using wordTrace_append hprefix tailTrace_2686527
  have hstable : (prefixWord ++ tailWord_2686527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686527).length < 2 ^ (prefixWord ++ tailWord_2686527).sum := by decide
  have hdescent : baseEnd_2686527 < baseStart_2686527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686667 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_2686667 : Nat := 118140960795 + 2686667 * 2 ^ 59
def prefixEnd_2686667 : Nat := 4983230072969 + 3 ^ 40 * 2686667 * 2
def baseEnd_2686667 : Nat := 1379551529573145136706749

theorem tailTrace_2686667 : CollatzResearch.WordTrace tailWord_2686667 prefixEnd_2686667 1379551529573145136706749 := by
  unfold tailWord_2686667
  simp only [CollatzResearch.WordTrace]
  refine ⟨97990795757671780038098255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65327197171781186692065503 97990795757671780038098255)
  ·
    refine ⟨146986193636507670057147383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97990795757671780038098255 146986193636507670057147383)
    ·
      refine ⟨220479290454761505085721075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146986193636507670057147383 220479290454761505085721075)
      ·
        refine ⟨330718935682142257628581613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220479290454761505085721075 330718935682142257628581613)
        ·
          refine ⟨124019600880803346610718105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330718935682142257628581613 124019600880803346610718105)
          ·
            refine ⟨93014700660602509958038579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124019600880803346610718105 93014700660602509958038579)
            ·
              refine ⟨139522050990903764937057869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93014700660602509958038579 139522050990903764937057869)
              ·
                refine ⟨52320769121588911851396701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139522050990903764937057869 52320769121588911851396701)
                ·
                  refine ⟨19620288420595841944273763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52320769121588911851396701 19620288420595841944273763)
                  ·
                    refine ⟨29430432630893762916410645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19620288420595841944273763 29430432630893762916410645)
                    ·
                      refine ⟨1379551529573145136706749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29430432630893762916410645 1379551529573145136706749)
                      ·
                        rfl

theorem cell23_2686667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_2686667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686667 prefixEnd_2686667 := by exact prefixLift 2686667
  have htrace : WordTrace (prefixWord ++ tailWord_2686667) baseStart_2686667 baseEnd_2686667 := by
    simpa [prefixWord, tailWord_2686667, baseEnd_2686667] using wordTrace_append hprefix tailTrace_2686667
  have hstable : (prefixWord ++ tailWord_2686667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686667).length < 2 ^ (prefixWord ++ tailWord_2686667).sum := by decide
  have hdescent : baseEnd_2686667 < baseStart_2686667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686671 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 7, 2, 2]
def baseStart_2686671 : Nat := 118140960795 + 2686671 * 2 ^ 59
def prefixEnd_2686671 : Nat := 4983230072969 + 3 ^ 40 * 2686671 * 2
def baseEnd_2686671 : Nat := 1379553583495763121056731

theorem tailTrace_2686671 : CollatzResearch.WordTrace tailWord_2686671 prefixEnd_2686671 1379553583495763121056731 := by
  unfold tailWord_2686671
  simp only [CollatzResearch.WordTrace]
  refine ⟨97990941649657288721243867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65327294433104859147495911 97990941649657288721243867)
  ·
    refine ⟨146986412474485933081865801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97990941649657288721243867 146986412474485933081865801)
    ·
      refine ⟨110239809355864449811399351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146986412474485933081865801 110239809355864449811399351)
      ·
        refine ⟨165359714033796674717099027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110239809355864449811399351 165359714033796674717099027)
        ·
          refine ⟨248039571050695012075648541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165359714033796674717099027 248039571050695012075648541)
          ·
            refine ⟨93014839144010629528368203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248039571050695012075648541 93014839144010629528368203)
            ·
              refine ⟨139522258716015944292552305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93014839144010629528368203 139522258716015944292552305)
              ·
                refine ⟨104641694037011958219414229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139522258716015944292552305 104641694037011958219414229)
                ·
                  refine ⟨2452539703992467770767521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104641694037011958219414229 2452539703992467770767521)
                  ·
                    refine ⟨1839404777994350828075641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452539703992467770767521 1839404777994350828075641)
                    ·
                      refine ⟨1379553583495763121056731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839404777994350828075641 1379553583495763121056731)
                      ·
                        rfl

theorem cell23_2686671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 2, 2].length) (baseStart_2686671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686671 prefixEnd_2686671 := by exact prefixLift 2686671
  have htrace : WordTrace (prefixWord ++ tailWord_2686671) baseStart_2686671 baseEnd_2686671 := by
    simpa [prefixWord, tailWord_2686671, baseEnd_2686671] using wordTrace_append hprefix tailTrace_2686671
  have hstable : (prefixWord ++ tailWord_2686671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686671).length < 2 ^ (prefixWord ++ tailWord_2686671).sum := by decide
  have hdescent : baseEnd_2686671 < baseStart_2686671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686681 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 2, 4]
def baseStart_2686681 : Nat := 118140960795 + 2686681 * 2 ^ 59
def prefixEnd_2686681 : Nat := 4983230072969 + 3 ^ 40 * 2686681 * 2
def baseEnd_2686681 : Nat := 459852906100769360643895

theorem tailTrace_2686681 : CollatzResearch.WordTrace tailWord_2686681 prefixEnd_2686681 459852906100769360643895 := by
  unfold tailWord_2686681
  simp only [CollatzResearch.WordTrace]
  refine ⟨97991306379621060429107897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65327537586414040286071931 97991306379621060429107897)
  ·
    refine ⟨73493479784715795321830923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97991306379621060429107897 73493479784715795321830923)
    ·
      refine ⟨110240219677073692982746385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73493479784715795321830923 110240219677073692982746385)
      ·
        refine ⟨82680164757805269737059789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110240219677073692982746385 82680164757805269737059789)
        ·
          refine ⟨31005061784176976151397421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82680164757805269737059789 31005061784176976151397421)
          ·
            refine ⟨11626898169066366056774033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31005061784176976151397421 11626898169066366056774033)
            ·
              refine ⟨8720173626799774542580525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626898169066366056774033 8720173626799774542580525)
              ·
                refine ⟨3270065110049915453467697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8720173626799774542580525 3270065110049915453467697)
                ·
                  refine ⟨2452548832537436590100773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270065110049915453467697 2452548832537436590100773)
                  ·
                    refine ⟨459852906100769360643895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2452548832537436590100773 459852906100769360643895)
                    ·
                      rfl

theorem cell23_2686681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_2686681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686681 prefixEnd_2686681 := by exact prefixLift 2686681
  have htrace : WordTrace (prefixWord ++ tailWord_2686681) baseStart_2686681 baseEnd_2686681 := by
    simpa [prefixWord, tailWord_2686681, baseEnd_2686681] using wordTrace_append hprefix tailTrace_2686681
  have hstable : (prefixWord ++ tailWord_2686681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686681).length < 2 ^ (prefixWord ++ tailWord_2686681).sum := by decide
  have hdescent : baseEnd_2686681 < baseStart_2686681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686701 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2686701 : Nat := 118140960795 + 2686701 * 2 ^ 59
def prefixEnd_2686701 : Nat := 4983230072969 + 3 ^ 40 * 2686701 * 2
def baseEnd_2686701 : Nat := 1379568987915398003681593

theorem tailTrace_2686701 : CollatzResearch.WordTrace tailWord_2686701 prefixEnd_2686701 1379568987915398003681593 := by
  unfold tailWord_2686701
  simp only [CollatzResearch.WordTrace]
  refine ⟨97992035839548603844835957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65328023893032402563223971 97992035839548603844835957)
  ·
    refine ⟨9186753359957681610453371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97992035839548603844835957 9186753359957681610453371)
    ·
      refine ⟨13780130039936522415680057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9186753359957681610453371 13780130039936522415680057)
      ·
        refine ⟨10335097529952391811760043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13780130039936522415680057 10335097529952391811760043)
        ·
          refine ⟨15502646294928587717640065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335097529952391811760043 15502646294928587717640065)
          ·
            refine ⟨11626984721196440788230049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15502646294928587717640065 11626984721196440788230049)
            ·
              refine ⟨8720238540897330591172537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626984721196440788230049 8720238540897330591172537)
              ·
                refine ⟨6540178905672997943379403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8720238540897330591172537 6540178905672997943379403)
                ·
                  refine ⟨9810268358509496915069105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540178905672997943379403 9810268358509496915069105)
                  ·
                    refine ⟨7357701268882122686301829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9810268358509496915069105 7357701268882122686301829)
                    ·
                      refine ⟨1379568987915398003681593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7357701268882122686301829 1379568987915398003681593)
                      ·
                        rfl

theorem cell23_2686701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2686701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686701 prefixEnd_2686701 := by exact prefixLift 2686701
  have htrace : WordTrace (prefixWord ++ tailWord_2686701) baseStart_2686701 baseEnd_2686701 := by
    simpa [prefixWord, tailWord_2686701, baseEnd_2686701] using wordTrace_append hprefix tailTrace_2686701
  have hstable : (prefixWord ++ tailWord_2686701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686701).length < 2 ^ (prefixWord ++ tailWord_2686701).sum := by decide
  have hdescent : baseEnd_2686701 < baseStart_2686701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686704 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_2686704 : Nat := 118140960795 + 2686704 * 2 ^ 59
def prefixEnd_2686704 : Nat := 4983230072969 + 3 ^ 40 * 2686704 * 2
def baseEnd_2686704 : Nat := 1379570528357361491944079

theorem tailTrace_2686704 : CollatzResearch.WordTrace tailWord_2686704 prefixEnd_2686704 1379570528357361491944079 := by
  unfold tailWord_2686704
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996072629268867678597583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65328096839025156904796777 48996072629268867678597583)
  ·
    refine ⟨73494108943903301517896375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48996072629268867678597583 73494108943903301517896375)
    ·
      refine ⟨110241163415854952276844563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73494108943903301517896375 110241163415854952276844563)
      ·
        refine ⟨165361745123782428415266845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110241163415854952276844563 165361745123782428415266845)
        ·
          refine ⟨62010654421418410655725067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165361745123782428415266845 62010654421418410655725067)
          ·
            refine ⟨93015981632127615983587601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62010654421418410655725067 93015981632127615983587601)
            ·
              refine ⟨69761986224095711987690701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93015981632127615983587601 69761986224095711987690701)
              ·
                refine ⟨26160744834035891995384013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69761986224095711987690701 26160744834035891995384013)
                ·
                  refine ⟨9810279312763459498269005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26160744834035891995384013 9810279312763459498269005)
                  ·
                    refine ⟨3678854742286297311850877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9810279312763459498269005 3678854742286297311850877)
                    ·
                      refine ⟨1379570528357361491944079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3678854742286297311850877 1379570528357361491944079)
                      ·
                        rfl

theorem cell23_2686704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_2686704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686704 prefixEnd_2686704 := by exact prefixLift 2686704
  have htrace : WordTrace (prefixWord ++ tailWord_2686704) baseStart_2686704 baseEnd_2686704 := by
    simpa [prefixWord, tailWord_2686704, baseEnd_2686704] using wordTrace_append hprefix tailTrace_2686704
  have hstable : (prefixWord ++ tailWord_2686704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686704).length < 2 ^ (prefixWord ++ tailWord_2686704).sum := by decide
  have hdescent : baseEnd_2686704 < baseStart_2686704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686705 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 1, 2, 2]
def baseStart_2686705 : Nat := 118140960795 + 2686705 * 2 ^ 59
def prefixEnd_2686705 : Nat := 4983230072969 + 3 ^ 40 * 2686705 * 2
def baseEnd_2686705 : Nat := 1379571041838015988031575

theorem tailTrace_2686705 : CollatzResearch.WordTrace tailWord_2686705 prefixEnd_2686705 1379571041838015988031575 := by
  unfold tailWord_2686705
  simp only [CollatzResearch.WordTrace]
  refine ⟨97992181731534112527981569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65328121154356075018654379 97992181731534112527981569)
  ·
    refine ⟨73494136298650584395986177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97992181731534112527981569 73494136298650584395986177)
    ·
      refine ⟨55120602223987938296989633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73494136298650584395986177 55120602223987938296989633)
      ·
        refine ⟨41340451667990953722742225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55120602223987938296989633 41340451667990953722742225)
        ·
          refine ⟨31005338750993215292056669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41340451667990953722742225 31005338750993215292056669)
          ·
            refine ⟨11627002031622455734521251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31005338750993215292056669 11627002031622455734521251)
            ·
              refine ⟨17440503047433683601781877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627002031622455734521251 17440503047433683601781877)
              ·
                refine ⟨1635047160696907837667051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17440503047433683601781877 1635047160696907837667051)
                ·
                  refine ⟨2452570741045361756500577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635047160696907837667051 2452570741045361756500577)
                  ·
                    refine ⟨1839428055784021317375433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452570741045361756500577 1839428055784021317375433)
                    ·
                      refine ⟨1379571041838015988031575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839428055784021317375433 1379571041838015988031575)
                      ·
                        rfl

theorem cell23_2686705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_2686705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686705 prefixEnd_2686705 := by exact prefixLift 2686705
  have htrace : WordTrace (prefixWord ++ tailWord_2686705) baseStart_2686705 baseEnd_2686705 := by
    simpa [prefixWord, tailWord_2686705, baseEnd_2686705] using wordTrace_append hprefix tailTrace_2686705
  have hstable : (prefixWord ++ tailWord_2686705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686705).length < 2 ^ (prefixWord ++ tailWord_2686705).sum := by decide
  have hdescent : baseEnd_2686705 < baseStart_2686705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686722 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_2686722 : Nat := 118140960795 + 2686722 * 2 ^ 59
def prefixEnd_2686722 : Nat := 4983230072969 + 3 ^ 40 * 2686722 * 2
def baseEnd_2686722 : Nat := 1379579771009142421518997

theorem tailTrace_2686722 : CollatzResearch.WordTrace tailWord_2686722 prefixEnd_2686722 1379579771009142421518997 := by
  unfold tailWord_2686722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24498200443118131107837605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65328534514981682954233613 24498200443118131107837605)
  ·
    refine ⟨4593412583084649582719551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24498200443118131107837605 4593412583084649582719551)
    ·
      refine ⟨6890118874626974374079327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593412583084649582719551 6890118874626974374079327)
      ·
        refine ⟨10335178311940461561118991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890118874626974374079327 10335178311940461561118991)
        ·
          refine ⟨15502767467910692341678487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335178311940461561118991 15502767467910692341678487)
          ·
            refine ⟨23254151201866038512517731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15502767467910692341678487 23254151201866038512517731)
            ·
              refine ⟨34881226802799057768776597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23254151201866038512517731 34881226802799057768776597)
              ·
                refine ⟨1635057506381205832911403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34881226802799057768776597 1635057506381205832911403)
                ·
                  refine ⟨2452586259571808749367105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635057506381205832911403 2452586259571808749367105)
                  ·
                    refine ⟨1839439694678856562025329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452586259571808749367105 1839439694678856562025329)
                    ·
                      refine ⟨1379579771009142421518997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839439694678856562025329 1379579771009142421518997)
                      ·
                        rfl

theorem cell23_2686722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_2686722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686722 prefixEnd_2686722 := by exact prefixLift 2686722
  have htrace : WordTrace (prefixWord ++ tailWord_2686722) baseStart_2686722 baseEnd_2686722 := by
    simpa [prefixWord, tailWord_2686722, baseEnd_2686722] using wordTrace_append hprefix tailTrace_2686722
  have hstable : (prefixWord ++ tailWord_2686722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686722).length < 2 ^ (prefixWord ++ tailWord_2686722).sum := by decide
  have hdescent : baseEnd_2686722 < baseStart_2686722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686731 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 5, 3, 2]
def baseStart_2686731 : Nat := 118140960795 + 2686731 * 2 ^ 59
def prefixEnd_2686731 : Nat := 4983230072969 + 3 ^ 40 * 2686731 * 2
def baseEnd_2686731 : Nat := 1379584392335032886306455

theorem tailTrace_2686731 : CollatzResearch.WordTrace tailWord_2686731 prefixEnd_2686731 1379584392335032886306455 := by
  unfold tailWord_2686731
  simp only [CollatzResearch.WordTrace]
  refine ⟨97993130029439918968428047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65328753352959945978952031 97993130029439918968428047)
  ·
    refine ⟨146989695044159878452642071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97993130029439918968428047 146989695044159878452642071)
    ·
      refine ⟨220484542566239817678963107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146989695044159878452642071 220484542566239817678963107)
      ·
        refine ⟨330726813849359726518444661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220484542566239817678963107 330726813849359726518444661)
        ·
          refine ⟨31005638798377474361104187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330726813849359726518444661 31005638798377474361104187)
          ·
            refine ⟨46508458197566211541656281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31005638798377474361104187 46508458197566211541656281)
            ·
              refine ⟨34881343648174658656242211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46508458197566211541656281 34881343648174658656242211)
              ·
                refine ⟨52322015472261987984363317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34881343648174658656242211 52322015472261987984363317)
                ·
                  refine ⟨4905188950524561373534061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52322015472261987984363317 4905188950524561373534061)
                  ·
                    refine ⟨1839445856446710515075273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4905188950524561373534061 1839445856446710515075273)
                    ·
                      refine ⟨1379584392335032886306455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839445856446710515075273 1379584392335032886306455)
                      ·
                        rfl

theorem cell23_2686731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3, 2].length) (baseStart_2686731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686731 prefixEnd_2686731 := by exact prefixLift 2686731
  have htrace : WordTrace (prefixWord ++ tailWord_2686731) baseStart_2686731 baseEnd_2686731 := by
    simpa [prefixWord, tailWord_2686731, baseEnd_2686731] using wordTrace_append hprefix tailTrace_2686731
  have hstable : (prefixWord ++ tailWord_2686731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686731).length < 2 ^ (prefixWord ++ tailWord_2686731).sum := by decide
  have hdescent : baseEnd_2686731 < baseStart_2686731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686744 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2686744 : Nat := 118140960795 + 2686744 * 2 ^ 59
def prefixEnd_2686744 : Nat := 4983230072969 + 3 ^ 40 * 2686744 * 2
def baseEnd_2686744 : Nat := 1379591067583541335443895

theorem tailTrace_2686744 : CollatzResearch.WordTrace tailWord_2686744 prefixEnd_2686744 1379591067583541335443895 := by
  unfold tailWord_2686744
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996802089196411094325643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65329069452261881459100857 48996802089196411094325643)
  ·
    refine ⟨73495203133794616641488465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48996802089196411094325643 73495203133794616641488465)
    ·
      refine ⟨55121402350345962481116349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73495203133794616641488465 55121402350345962481116349)
      ·
        refine ⟨20670525881379735930418631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55121402350345962481116349 20670525881379735930418631)
        ·
          refine ⟨31005788822069603895627947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20670525881379735930418631 31005788822069603895627947)
          ·
            refine ⟨46508683233104405843441921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31005788822069603895627947 46508683233104405843441921)
            ·
              refine ⟨34881512424828304382581441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46508683233104405843441921 34881512424828304382581441)
              ·
                refine ⟨26161134318621228286936081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34881512424828304382581441 26161134318621228286936081)
                ·
                  refine ⟨19620850738965921215202061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26161134318621228286936081 19620850738965921215202061)
                  ·
                    refine ⟨7357819027112220455700773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19620850738965921215202061 7357819027112220455700773)
                    ·
                      refine ⟨1379591067583541335443895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7357819027112220455700773 1379591067583541335443895)
                      ·
                        rfl

theorem cell23_2686744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2686744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686744 prefixEnd_2686744 := by exact prefixLift 2686744
  have htrace : WordTrace (prefixWord ++ tailWord_2686744) baseStart_2686744 baseEnd_2686744 := by
    simpa [prefixWord, tailWord_2686744, baseEnd_2686744] using wordTrace_append hprefix tailTrace_2686744
  have hstable : (prefixWord ++ tailWord_2686744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686744).length < 2 ^ (prefixWord ++ tailWord_2686744).sum := by decide
  have hdescent : baseEnd_2686744 < baseStart_2686744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686764 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_2686764 : Nat := 118140960795 + 2686764 * 2 ^ 59
def prefixEnd_2686764 : Nat := 4983230072969 + 3 ^ 40 * 2686764 * 2
def baseEnd_2686764 : Nat := 1379601337196631257193803

theorem tailTrace_2686764 : CollatzResearch.WordTrace tailWord_2686764 prefixEnd_2686764 1379601337196631257193803 := by
  unfold tailWord_2686764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48997166819160182802189673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65329555758880243736252897 48997166819160182802189673)
  ·
    refine ⟨36747875114370137101642255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48997166819160182802189673 36747875114370137101642255)
    ·
      refine ⟨55121812671555205652463383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36747875114370137101642255 55121812671555205652463383)
      ·
        refine ⟨82682719007332808478695075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55121812671555205652463383 82682719007332808478695075)
        ·
          refine ⟨124024078510999212718042613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82682719007332808478695075 124024078510999212718042613)
          ·
            refine ⟨11627257360406176192316495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124024078510999212718042613 11627257360406176192316495)
            ·
              refine ⟨17440886040609264288474743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627257360406176192316495 17440886040609264288474743)
              ·
                refine ⟨26161329060913896432712115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17440886040609264288474743 26161329060913896432712115)
                ·
                  refine ⟨39241993591370844649068173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26161329060913896432712115 39241993591370844649068173)
                  ·
                    refine ⟨14715747596764066743400565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39241993591370844649068173 14715747596764066743400565)
                    ·
                      refine ⟨1379601337196631257193803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14715747596764066743400565 1379601337196631257193803)
                      ·
                        rfl

theorem cell23_2686764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_2686764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686764 prefixEnd_2686764 := by exact prefixLift 2686764
  have htrace : WordTrace (prefixWord ++ tailWord_2686764) baseStart_2686764 baseEnd_2686764 := by
    simpa [prefixWord, tailWord_2686764, baseEnd_2686764] using wordTrace_append hprefix tailTrace_2686764
  have hstable : (prefixWord ++ tailWord_2686764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686764).length < 2 ^ (prefixWord ++ tailWord_2686764).sum := by decide
  have hdescent : baseEnd_2686764 < baseStart_2686764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686844 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_2686844 : Nat := 118140960795 + 2686844 * 2 ^ 59
def prefixEnd_2686844 : Nat := 4983230072969 + 3 ^ 40 * 2686844 * 2
def baseEnd_2686844 : Nat := 459880805216330314731145

theorem tailTrace_2686844 : CollatzResearch.WordTrace tailWord_2686844 prefixEnd_2686844 459880805216330314731145 := by
  unfold tailWord_2686844
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998625739015269633645793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65331500985353692844861057 48998625739015269633645793)
  ·
    refine ⟨36748969304261452225234345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48998625739015269633645793 36748969304261452225234345)
    ·
      refine ⟨27561726978196089168925759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36748969304261452225234345 27561726978196089168925759)
      ·
        refine ⟨41342590467294133753388639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27561726978196089168925759 41342590467294133753388639)
        ·
          refine ⟨62013885700941200630082959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41342590467294133753388639 62013885700941200630082959)
          ·
            refine ⟨93020828551411800945124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62013885700941200630082959 93020828551411800945124439)
            ·
              refine ⟨139531242827117701417686659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93020828551411800945124439 139531242827117701417686659)
              ·
                refine ⟨209296864240676552126529989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139531242827117701417686659 209296864240676552126529989)
                ·
                  refine ⟨39243162045126853523724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209296864240676552126529989 39243162045126853523724373)
                  ·
                    refine ⟨459880805216330314731145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39243162045126853523724373 459880805216330314731145)
                    ·
                      rfl

theorem cell23_2686844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_2686844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686844 prefixEnd_2686844 := by exact prefixLift 2686844
  have htrace : WordTrace (prefixWord ++ tailWord_2686844) baseStart_2686844 baseEnd_2686844 := by
    simpa [prefixWord, tailWord_2686844, baseEnd_2686844] using wordTrace_append hprefix tailTrace_2686844
  have hstable : (prefixWord ++ tailWord_2686844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686844).length < 2 ^ (prefixWord ++ tailWord_2686844).sum := by decide
  have hdescent : baseEnd_2686844 < baseStart_2686844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686864 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_2686864 : Nat := 118140960795 + 2686864 * 2 ^ 59
def prefixEnd_2686864 : Nat := 4983230072969 + 3 ^ 40 * 2686864 * 2
def baseEnd_2686864 : Nat := 1379652685262080865943343

theorem tailTrace_2686864 : CollatzResearch.WordTrace tailWord_2686864 prefixEnd_2686864 1379652685262080865943343 := by
  unfold tailWord_2686864
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998990468979041341509823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65331987291972055122013097 48998990468979041341509823)
  ·
    refine ⟨73498485703468562012264735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48998990468979041341509823 73498485703468562012264735)
    ·
      refine ⟨110247728555202843018397103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73498485703468562012264735 110247728555202843018397103)
      ·
        refine ⟨165371592832804264527595655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110247728555202843018397103 165371592832804264527595655)
        ·
          refine ⟨248057389249206396791393483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165371592832804264527595655 248057389249206396791393483)
          ·
            refine ⟨372086083873809595187090225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248057389249206396791393483 372086083873809595187090225)
            ·
              refine ⟨279064562905357196390317669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372086083873809595187090225 279064562905357196390317669)
              ·
                refine ⟨52324605544754474323184563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279064562905357196390317669 52324605544754474323184563)
                ·
                  refine ⟨78486908317131711484776845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52324605544754474323184563 78486908317131711484776845)
                  ·
                    refine ⟨29432590618924391806791317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78486908317131711484776845 29432590618924391806791317)
                    ·
                      refine ⟨1379652685262080865943343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29432590618924391806791317 1379652685262080865943343)
                      ·
                        rfl

theorem cell23_2686864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_2686864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686864 prefixEnd_2686864 := by exact prefixLift 2686864
  have htrace : WordTrace (prefixWord ++ tailWord_2686864) baseStart_2686864 baseEnd_2686864 := by
    simpa [prefixWord, tailWord_2686864, baseEnd_2686864] using wordTrace_append hprefix tailTrace_2686864
  have hstable : (prefixWord ++ tailWord_2686864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686864).length < 2 ^ (prefixWord ++ tailWord_2686864).sum := by decide
  have hdescent : baseEnd_2686864 < baseStart_2686864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686868 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2686868 : Nat := 118140960795 + 2686868 * 2 ^ 59
def prefixEnd_2686868 : Nat := 4983230072969 + 3 ^ 40 * 2686868 * 2
def baseEnd_2686868 : Nat := 1379654739184698850293325

theorem tailTrace_2686868 : CollatzResearch.WordTrace tailWord_2686868 prefixEnd_2686868 1379654739184698850293325 := by
  unfold tailWord_2686868
  simp only [CollatzResearch.WordTrace]
  refine ⟨48999063414971795683082629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65332084553295727577443505 48999063414971795683082629)
  ·
    refine ⟨9187324390307211690577993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48999063414971795683082629 9187324390307211690577993)
    ·
      refine ⟨6890493292730408767933495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9187324390307211690577993 6890493292730408767933495)
      ·
        refine ⟨10335739939095613151900243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890493292730408767933495 10335739939095613151900243)
        ·
          refine ⟨15503609908643419727850365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335739939095613151900243 15503609908643419727850365)
          ·
            refine ⟨5813853715741282397943887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15503609908643419727850365 5813853715741282397943887)
            ·
              refine ⟨8720780573611923596915831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813853715741282397943887 8720780573611923596915831)
              ·
                refine ⟨13081170860417885395373747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8720780573611923596915831 13081170860417885395373747)
                ·
                  refine ⟨19621756290626828093060621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13081170860417885395373747 19621756290626828093060621)
                  ·
                    refine ⟨7358158608985060534897733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19621756290626828093060621 7358158608985060534897733)
                    ·
                      refine ⟨1379654739184698850293325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7358158608985060534897733 1379654739184698850293325)
                      ·
                        rfl

theorem cell23_2686868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2686868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686868 prefixEnd_2686868 := by exact prefixLift 2686868
  have htrace : WordTrace (prefixWord ++ tailWord_2686868) baseStart_2686868 baseEnd_2686868 := by
    simpa [prefixWord, tailWord_2686868, baseEnd_2686868] using wordTrace_append hprefix tailTrace_2686868
  have hstable : (prefixWord ++ tailWord_2686868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686868).length < 2 ^ (prefixWord ++ tailWord_2686868).sum := by decide
  have hdescent : baseEnd_2686868 < baseStart_2686868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686928 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2]
def baseStart_2686928 : Nat := 118140960795 + 2686928 * 2 ^ 59
def prefixEnd_2686928 : Nat := 4983230072969 + 3 ^ 40 * 2686928 * 2
def baseEnd_2686928 : Nat := 1379685548023968615543049

theorem tailTrace_2686928 : CollatzResearch.WordTrace tailWord_2686928 prefixEnd_2686928 1379685548023968615543049 := by
  unfold tailWord_2686928
  simp only [CollatzResearch.WordTrace]
  refine ⟨49000157604863110806674719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65333543473150814408899625 49000157604863110806674719)
  ·
    refine ⟨73500236407294666210012079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49000157604863110806674719 73500236407294666210012079)
    ·
      refine ⟨110250354610941999315018119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73500236407294666210012079 110250354610941999315018119)
      ·
        refine ⟨165375531916412998972527179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110250354610941999315018119 165375531916412998972527179)
        ·
          refine ⟨248063297874619498458790769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165375531916412998972527179 248063297874619498458790769)
          ·
            refine ⟨186047473405964623844093077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248063297874619498458790769 186047473405964623844093077)
            ·
              refine ⟨8720975315904591742691863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186047473405964623844093077 8720975315904591742691863)
              ·
                refine ⟨13081462973856887614037795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8720975315904591742691863 13081462973856887614037795)
                ·
                  refine ⟨19622194460785331421056693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13081462973856887614037795 19622194460785331421056693)
                  ·
                    refine ⟨1839580730698624820724065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19622194460785331421056693 1839580730698624820724065)
                    ·
                      refine ⟨1379685548023968615543049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839580730698624820724065 1379685548023968615543049)
                      ·
                        rfl

theorem cell23_2686928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2].length) (baseStart_2686928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686928 prefixEnd_2686928 := by exact prefixLift 2686928
  have htrace : WordTrace (prefixWord ++ tailWord_2686928) baseStart_2686928 baseEnd_2686928 := by
    simpa [prefixWord, tailWord_2686928, baseEnd_2686928] using wordTrace_append hprefix tailTrace_2686928
  have hstable : (prefixWord ++ tailWord_2686928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686928).length < 2 ^ (prefixWord ++ tailWord_2686928).sum := by decide
  have hdescent : baseEnd_2686928 < baseStart_2686928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686946 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2686946 : Nat := 118140960795 + 2686946 * 2 ^ 59
def prefixEnd_2686946 : Nat := 4983230072969 + 3 ^ 40 * 2686946 * 2
def baseEnd_2686946 : Nat := 459898263558583181705989

theorem tailTrace_2686946 : CollatzResearch.WordTrace tailWord_2686946 prefixEnd_2686946 459898263558583181705989 := by
  unfold tailWord_2686946
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500242930915252671876173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65333981149107340458336461 24500242930915252671876173)
  ·
    refine ⟨9187591099093219751953565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24500242930915252671876173 9187591099093219751953565)
    ·
      refine ⟨3445346662159957406982587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9187591099093219751953565 3445346662159957406982587)
      ·
        refine ⟨5168019993239936110473881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445346662159957406982587 5168019993239936110473881)
        ·
          refine ⟨3876014994929952082855411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5168019993239936110473881 3876014994929952082855411)
          ·
            refine ⟨5814022492394928124283117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876014994929952082855411 5814022492394928124283117)
            ·
              refine ⟨2180258434648098046606169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5814022492394928124283117 2180258434648098046606169)
              ·
                refine ⟨1635193825986073534954627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180258434648098046606169 1635193825986073534954627)
                ·
                  refine ⟨2452790738979110302431941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635193825986073534954627 2452790738979110302431941)
                  ·
                    refine ⟨459898263558583181705989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2452790738979110302431941 459898263558583181705989)
                    ·
                      rfl

theorem cell23_2686946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2686946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686946 prefixEnd_2686946 := by exact prefixLift 2686946
  have htrace : WordTrace (prefixWord ++ tailWord_2686946) baseStart_2686946 baseEnd_2686946 := by
    simpa [prefixWord, tailWord_2686946, baseEnd_2686946] using wordTrace_append hprefix tailTrace_2686946
  have hstable : (prefixWord ++ tailWord_2686946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686946).length < 2 ^ (prefixWord ++ tailWord_2686946).sum := by decide
  have hdescent : baseEnd_2686946 < baseStart_2686946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686971 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_2686971 : Nat := 118140960795 + 2686971 * 2 ^ 59
def prefixEnd_2686971 : Nat := 4983230072969 + 3 ^ 40 * 2686971 * 2
def baseEnd_2686971 : Nat := 1379707627692111947305351

theorem tailTrace_2686971 : CollatzResearch.WordTrace tailWord_2686971 prefixEnd_2686971 1379707627692111947305351 := by
  unfold tailWord_2686971
  simp only [CollatzResearch.WordTrace]
  refine ⟨98001883548570439957164767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65334589032380293304776511 98001883548570439957164767)
  ·
    refine ⟨147002825322855659935747151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98001883548570439957164767 147002825322855659935747151)
    ·
      refine ⟨220504237984283489903620727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147002825322855659935747151 220504237984283489903620727)
      ·
        refine ⟨330756356976425234855431091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220504237984283489903620727 330756356976425234855431091)
        ·
          refine ⟨496134535464637852283146637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330756356976425234855431091 496134535464637852283146637)
          ·
            refine ⟨186050450799239194606179989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496134535464637852283146637 186050450799239194606179989)
            ·
              refine ⟨8721114881214337247164687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186050450799239194606179989 8721114881214337247164687)
              ·
                refine ⟨13081672321821505870747031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8721114881214337247164687 13081672321821505870747031)
                ·
                  refine ⟨19622508482732258806120547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13081672321821505870747031 19622508482732258806120547)
                  ·
                    refine ⟨29433762724098388209180821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19622508482732258806120547 29433762724098388209180821)
                    ·
                      refine ⟨1379707627692111947305351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29433762724098388209180821 1379707627692111947305351)
                      ·
                        rfl

theorem cell23_2686971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_2686971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686971 prefixEnd_2686971 := by exact prefixLift 2686971
  have htrace : WordTrace (prefixWord ++ tailWord_2686971) baseStart_2686971 baseEnd_2686971 := by
    simpa [prefixWord, tailWord_2686971, baseEnd_2686971] using wordTrace_append hprefix tailTrace_2686971
  have hstable : (prefixWord ++ tailWord_2686971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686971).length < 2 ^ (prefixWord ++ tailWord_2686971).sum := by decide
  have hdescent : baseEnd_2686971 < baseStart_2686971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686975 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 3, 2, 2]
def baseStart_2686975 : Nat := 118140960795 + 2686975 * 2 ^ 59
def prefixEnd_2686975 : Nat := 4983230072969 + 3 ^ 40 * 2686975 * 2
def baseEnd_2686975 : Nat := 1379709681614729931655333

theorem tailTrace_2686975 : CollatzResearch.WordTrace tailWord_2686975 prefixEnd_2686975 1379709681614729931655333 := by
  unfold tailWord_2686975
  simp only [CollatzResearch.WordTrace]
  refine ⟨98002029440555948640310379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65334686293703965760206919 98002029440555948640310379)
  ·
    refine ⟨147003044160833922960465569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98002029440555948640310379 147003044160833922960465569)
    ·
      refine ⟨110252283120625442220349177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147003044160833922960465569 110252283120625442220349177)
      ·
        refine ⟨82689212340469081665261883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110252283120625442220349177 82689212340469081665261883)
        ·
          refine ⟨124033818510703622497892825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82689212340469081665261883 124033818510703622497892825)
          ·
            refine ⟨93025363883027716873419619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124033818510703622497892825 93025363883027716873419619)
            ·
              refine ⟨139538045824541575310129429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93025363883027716873419619 139538045824541575310129429)
              ·
                refine ⟨6540845898025386342662317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139538045824541575310129429 6540845898025386342662317)
                ·
                  refine ⟨2452817211759519878498369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6540845898025386342662317 2452817211759519878498369)
                  ·
                    refine ⟨1839612908819639908873777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452817211759519878498369 1839612908819639908873777)
                    ·
                      refine ⟨1379709681614729931655333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839612908819639908873777 1379709681614729931655333)
                      ·
                        rfl

theorem cell23_2686975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_2686975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686975 prefixEnd_2686975 := by exact prefixLift 2686975
  have htrace : WordTrace (prefixWord ++ tailWord_2686975) baseStart_2686975 baseEnd_2686975 := by
    simpa [prefixWord, tailWord_2686975, baseEnd_2686975] using wordTrace_append hprefix tailTrace_2686975
  have hstable : (prefixWord ++ tailWord_2686975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686975).length < 2 ^ (prefixWord ++ tailWord_2686975).sum := by decide
  have hdescent : baseEnd_2686975 < baseStart_2686975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686981 : List Nat := [1, 3, 1, 1, 2, 4, 2, 9]
def baseStart_2686981 : Nat := 118140960795 + 2686981 * 2 ^ 59
def prefixEnd_2686981 : Nat := 4983230072969 + 3 ^ 40 * 2686981 * 2
def baseEnd_2686981 : Nat := 51100472685135441043715

theorem tailTrace_2686981 : CollatzResearch.WordTrace tailWord_2686981 prefixEnd_2686981 51100472685135441043715 := by
  unfold tailWord_2686981
  simp only [CollatzResearch.WordTrace]
  refine ⟨98002248278534211665028797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65334832185689474443352531 98002248278534211665028797)
  ·
    refine ⟨36750843104450329374385799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98002248278534211665028797 36750843104450329374385799)
    ·
      refine ⟨55126264656675494061578699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36750843104450329374385799 55126264656675494061578699)
      ·
        refine ⟨82689396985013241092368049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55126264656675494061578699 82689396985013241092368049)
        ·
          refine ⟨62017047738759930819276037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82689396985013241092368049 62017047738759930819276037)
          ·
            refine ⟨11628196451017487028614257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62017047738759930819276037 11628196451017487028614257)
            ·
              refine ⟨8721147338263115271460693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11628196451017487028614257 8721147338263115271460693)
              ·
                refine ⟨51100472685135441043715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8721147338263115271460693 51100472685135441043715)
                ·
                  rfl

theorem cell23_2686981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 9].length) (baseStart_2686981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686981 prefixEnd_2686981 := by exact prefixLift 2686981
  have htrace : WordTrace (prefixWord ++ tailWord_2686981) baseStart_2686981 baseEnd_2686981 := by
    simpa [prefixWord, tailWord_2686981, baseEnd_2686981] using wordTrace_append hprefix tailTrace_2686981
  have hstable : (prefixWord ++ tailWord_2686981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686981).length < 2 ^ (prefixWord ++ tailWord_2686981).sum := by decide
  have hdescent : baseEnd_2686981 < baseStart_2686981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686988 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2686988 : Nat := 118140960795 + 2686988 * 2 ^ 59
def prefixEnd_2686988 : Nat := 4983230072969 + 3 ^ 40 * 2686988 * 2
def baseEnd_2686988 : Nat := 1379716356863238380792773

theorem tailTrace_2686988 : CollatzResearch.WordTrace tailWord_2686988 prefixEnd_2686988 1379716356863238380792773 := by
  unfold tailWord_2686988
  simp only [CollatzResearch.WordTrace]
  refine ⟨49001251794754425930266809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65335002393005901240355745 49001251794754425930266809)
  ·
    refine ⟨36750938846065819447700107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49001251794754425930266809 36750938846065819447700107)
    ·
      refine ⟨55126408269098729171550161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36750938846065819447700107 55126408269098729171550161)
      ·
        refine ⟨41344806201824046878662621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55126408269098729171550161 41344806201824046878662621)
        ·
          refine ⟨15504302325684017579498483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41344806201824046878662621 15504302325684017579498483)
          ·
            refine ⟨23256453488526026369247725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15504302325684017579498483 23256453488526026369247725)
            ·
              refine ⟨8721170058197259888467897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23256453488526026369247725 8721170058197259888467897)
              ·
                refine ⟨6540877543647944916350923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721170058197259888467897 6540877543647944916350923)
                ·
                  refine ⟨9811316315471917374526385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540877543647944916350923 9811316315471917374526385)
                  ·
                    refine ⟨7358487236603938030894789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9811316315471917374526385 7358487236603938030894789)
                    ·
                      refine ⟨1379716356863238380792773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7358487236603938030894789 1379716356863238380792773)
                      ·
                        rfl

theorem cell23_2686988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2686988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686988 prefixEnd_2686988 := by exact prefixLift 2686988
  have htrace : WordTrace (prefixWord ++ tailWord_2686988) baseStart_2686988 baseEnd_2686988 := by
    simpa [prefixWord, tailWord_2686988, baseEnd_2686988] using wordTrace_append hprefix tailTrace_2686988
  have hstable : (prefixWord ++ tailWord_2686988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686988).length < 2 ^ (prefixWord ++ tailWord_2686988).sum := by decide
  have hdescent : baseEnd_2686988 < baseStart_2686988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687011 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 1, 9]
def baseStart_2687011 : Nat := 118140960795 + 2687011 * 2 ^ 59
def prefixEnd_2687011 : Nat := 4983230072969 + 3 ^ 40 * 2687011 * 2
def baseEnd_2687011 : Nat := 459909388972763930268389

theorem tailTrace_2687011 : CollatzResearch.WordTrace tailWord_2687011 prefixEnd_2687011 459909388972763930268389 := by
  unfold tailWord_2687011
  simp only [CollatzResearch.WordTrace]
  refine ⟨98003342468425526788620887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65335561645617017859080591 98003342468425526788620887)
  ·
    refine ⟨147005013702638290182931331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98003342468425526788620887 147005013702638290182931331)
    ·
      refine ⟨220507520553957435274396997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147005013702638290182931331 220507520553957435274396997)
      ·
        refine ⟨41345160103867019113949437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220507520553957435274396997 41345160103867019113949437)
        ·
          refine ⟨15504435038950132167731039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41345160103867019113949437 15504435038950132167731039)
          ·
            refine ⟨23256652558425198251596559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15504435038950132167731039 23256652558425198251596559)
            ·
              refine ⟨34884978837637797377394839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23256652558425198251596559 34884978837637797377394839)
              ·
                refine ⟨52327468256456696066092259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34884978837637797377394839 52327468256456696066092259)
                ·
                  refine ⟨78491202384685044099138389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52327468256456696066092259 78491202384685044099138389)
                  ·
                    refine ⟨459909388972763930268389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78491202384685044099138389 459909388972763930268389)
                    ·
                      rfl

theorem cell23_2687011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_2687011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687011 prefixEnd_2687011 := by exact prefixLift 2687011
  have htrace : WordTrace (prefixWord ++ tailWord_2687011) baseStart_2687011 baseEnd_2687011 := by
    simpa [prefixWord, tailWord_2687011, baseEnd_2687011] using wordTrace_append hprefix tailTrace_2687011
  have hstable : (prefixWord ++ tailWord_2687011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687011).length < 2 ^ (prefixWord ++ tailWord_2687011).sum := by decide
  have hdescent : baseEnd_2687011 < baseStart_2687011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687025 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2687025 : Nat := 118140960795 + 2687025 * 2 ^ 59
def prefixEnd_2687025 : Nat := 4983230072969 + 3 ^ 40 * 2687025 * 2
def baseEnd_2687025 : Nat := 1379735355647454736030103

theorem tailTrace_2687025 : CollatzResearch.WordTrace tailWord_2687025 prefixEnd_2687025 1379735355647454736030103 := by
  unfold tailWord_2687025
  simp only [CollatzResearch.WordTrace]
  refine ⟨98003853090374807179630529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65335902060249871453087019 98003853090374807179630529)
  ·
    refine ⟨73502889817781105384722897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98003853090374807179630529 73502889817781105384722897)
    ·
      refine ⟨55127167363335829038542173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73502889817781105384722897 55127167363335829038542173)
      ·
        refine ⟨20672687761250935889453315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55127167363335829038542173 20672687761250935889453315)
        ·
          refine ⟨31009031641876403834179973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20672687761250935889453315 31009031641876403834179973)
          ·
            refine ⟨5814193432851825718908745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31009031641876403834179973 5814193432851825718908745)
            ·
              refine ⟨4360645074638869289181559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5814193432851825718908745 4360645074638869289181559)
              ·
                refine ⟨6540967611958303933772339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360645074638869289181559 6540967611958303933772339)
                ·
                  refine ⟨9811451417937455900658509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540967611958303933772339 9811451417937455900658509)
                  ·
                    refine ⟨3679294281726545962746941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9811451417937455900658509 3679294281726545962746941)
                    ·
                      refine ⟨1379735355647454736030103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3679294281726545962746941 1379735355647454736030103)
                      ·
                        rfl

theorem cell23_2687025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2687025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687025 prefixEnd_2687025 := by exact prefixLift 2687025
  have htrace : WordTrace (prefixWord ++ tailWord_2687025) baseStart_2687025 baseEnd_2687025 := by
    simpa [prefixWord, tailWord_2687025, baseEnd_2687025] using wordTrace_append hprefix tailTrace_2687025
  have hstable : (prefixWord ++ tailWord_2687025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687025).length < 2 ^ (prefixWord ++ tailWord_2687025).sum := by decide
  have hdescent : baseEnd_2687025 < baseStart_2687025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687088 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 7]
def baseStart_2687088 : Nat := 118140960795 + 2687088 * 2 ^ 59
def prefixEnd_2687088 : Nat := 4983230072969 + 3 ^ 40 * 2687088 * 2
def baseEnd_2687088 : Nat := 153307522769854221060257

theorem tailTrace_2687088 : CollatzResearch.WordTrace tailWord_2687088 prefixEnd_2687088 153307522769854221060257 := by
  unfold tailWord_2687088
  simp only [CollatzResearch.WordTrace]
  refine ⟨49003075444573284469586959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65337433926097712626115945 49003075444573284469586959)
  ·
    refine ⟨73504613166859926704380439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49003075444573284469586959 73504613166859926704380439)
    ·
      refine ⟨110256919750289890056570659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73504613166859926704380439 110256919750289890056570659)
      ·
        refine ⟨165385379625434835084855989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110256919750289890056570659 165385379625434835084855989)
        ·
          refine ⟨15504879339884515789205249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165385379625434835084855989 15504879339884515789205249)
          ·
            refine ⟨11628659504913386841903937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15504879339884515789205249 11628659504913386841903937)
            ·
              refine ⟨8721494628685040131427953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11628659504913386841903937 8721494628685040131427953)
              ·
                refine ⟨6541120971513780098570965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721494628685040131427953 6541120971513780098570965)
                ·
                  refine ⟨153307522769854221060257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6541120971513780098570965 153307522769854221060257)
                  ·
                    rfl

theorem cell23_2687088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_2687088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687088 prefixEnd_2687088 := by exact prefixLift 2687088
  have htrace : WordTrace (prefixWord ++ tailWord_2687088) baseStart_2687088 baseEnd_2687088 := by
    simpa [prefixWord, tailWord_2687088, baseEnd_2687088] using wordTrace_append hprefix tailTrace_2687088
  have hstable : (prefixWord ++ tailWord_2687088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687088).length < 2 ^ (prefixWord ++ tailWord_2687088).sum := by decide
  have hdescent : baseEnd_2687088 < baseStart_2687088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687125 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_2687125 : Nat := 118140960795 + 2687125 * 2 ^ 59
def prefixEnd_2687125 : Nat := 4983230072969 + 3 ^ 40 * 2687125 * 2
def baseEnd_2687125 : Nat := 1379786703712904344779643

theorem tailTrace_2687125 : CollatzResearch.WordTrace tailWord_2687125 prefixEnd_2687125 1379786703712904344779643 := by
  unfold tailWord_2687125
  simp only [CollatzResearch.WordTrace]
  refine ⟨98007500390012524258270829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65338333593341682838847219 98007500390012524258270829)
  ·
    refine ⟨36752812646254696596851561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98007500390012524258270829 36752812646254696596851561)
    ·
      refine ⟨27564609484691022447638671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36752812646254696596851561 27564609484691022447638671)
      ·
        refine ⟨41346914227036533671458007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27564609484691022447638671 41346914227036533671458007)
        ·
          refine ⟨62020371340554800507187011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41346914227036533671458007 62020371340554800507187011)
          ·
            refine ⟨93030557010832200760780517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62020371340554800507187011 93030557010832200760780517)
            ·
              refine ⟨17443229439531037642646347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93030557010832200760780517 17443229439531037642646347)
              ·
                refine ⟨26164844159296556463969521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17443229439531037642646347 26164844159296556463969521)
                ·
                  refine ⟨19623633119472417347977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26164844159296556463969521 19623633119472417347977141)
                  ·
                    refine ⟨1839715604950539126372857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19623633119472417347977141 1839715604950539126372857)
                    ·
                      refine ⟨1379786703712904344779643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839715604950539126372857 1379786703712904344779643)
                      ·
                        rfl

theorem cell23_2687125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_2687125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687125 prefixEnd_2687125 := by exact prefixLift 2687125
  have htrace : WordTrace (prefixWord ++ tailWord_2687125) baseStart_2687125 baseEnd_2687125 := by
    simpa [prefixWord, tailWord_2687125, baseEnd_2687125] using wordTrace_append hprefix tailTrace_2687125
  have hstable : (prefixWord ++ tailWord_2687125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687125).length < 2 ^ (prefixWord ++ tailWord_2687125).sum := by decide
  have hdescent : baseEnd_2687125 < baseStart_2687125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 4, 2]
def baseStart_2687155 : Nat := 118140960795 + 2687155 * 2 ^ 59
def prefixEnd_2687155 : Nat := 4983230072969 + 3 ^ 40 * 2687155 * 2
def baseEnd_2687155 : Nat := 1379802108132539227404505

theorem tailTrace_2687155 : CollatzResearch.WordTrace tailWord_2687155 prefixEnd_2687155 1379802108132539227404505 := by
  unfold tailWord_2687155
  simp only [CollatzResearch.WordTrace]
  refine ⟨98008594579903839381862919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65339063053269226254575279 98008594579903839381862919)
  ·
    refine ⟨147012891869855759072794379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98008594579903839381862919 147012891869855759072794379)
    ·
      refine ⟨220519337804783638609191569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147012891869855759072794379 220519337804783638609191569)
      ·
        refine ⟨165389503353587728956893677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220519337804783638609191569 165389503353587728956893677)
        ·
          refine ⟨62021063757595398358835129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165389503353587728956893677 62021063757595398358835129)
          ·
            refine ⟨46515797818196548769126347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62021063757595398358835129 46515797818196548769126347)
            ·
              refine ⟨69773696727294823153689521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46515797818196548769126347 69773696727294823153689521)
              ·
                refine ⟨52330272545471117365267141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69773696727294823153689521 52330272545471117365267141)
                ·
                  refine ⟨9811926102275834505987589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52330272545471117365267141 9811926102275834505987589)
                  ·
                    refine ⟨1839736144176718969872673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9811926102275834505987589 1839736144176718969872673)
                    ·
                      refine ⟨1379802108132539227404505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839736144176718969872673 1379802108132539227404505)
                      ·
                        rfl

theorem cell23_2687155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4, 2].length) (baseStart_2687155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687155 prefixEnd_2687155 := by exact prefixLift 2687155
  have htrace : WordTrace (prefixWord ++ tailWord_2687155) baseStart_2687155 baseEnd_2687155 := by
    simpa [prefixWord, tailWord_2687155, baseEnd_2687155] using wordTrace_append hprefix tailTrace_2687155
  have hstable : (prefixWord ++ tailWord_2687155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687155).length < 2 ^ (prefixWord ++ tailWord_2687155).sum := by decide
  have hdescent : baseEnd_2687155 < baseStart_2687155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687172 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2687172 : Nat := 118140960795 + 2687172 * 2 ^ 59
def prefixEnd_2687172 : Nat := 4983230072969 + 3 ^ 40 * 2687172 * 2
def baseEnd_2687172 : Nat := 1379810837303665660891927

theorem tailTrace_2687172 : CollatzResearch.WordTrace tailWord_2687172 prefixEnd_2687172 1379810837303665660891927 := by
  unfold tailWord_2687172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49004607310421125642615885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65339476413894834190154513 49004607310421125642615885)
  ·
    refine ⟨18376727741407922115980957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49004607310421125642615885 18376727741407922115980957)
    ·
      refine ⟨6891272903027970793492859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18376727741407922115980957 6891272903027970793492859)
      ·
        refine ⟨10336909354541956190239289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6891272903027970793492859 10336909354541956190239289)
        ·
          refine ⟨7752682015906467142679467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336909354541956190239289 7752682015906467142679467)
          ·
            refine ⟨11629023023859700714019201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752682015906467142679467 11629023023859700714019201)
            ·
              refine ⟨8721767267894775535514401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11629023023859700714019201 8721767267894775535514401)
              ·
                refine ⟨6541325450921081651635801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721767267894775535514401 6541325450921081651635801)
                ·
                  refine ⟨4905994088190811238726851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6541325450921081651635801 4905994088190811238726851)
                  ·
                    refine ⟨7358991132286216858090277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4905994088190811238726851 7358991132286216858090277)
                    ·
                      refine ⟨1379810837303665660891927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7358991132286216858090277 1379810837303665660891927)
                      ·
                        rfl

theorem cell23_2687172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2687172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687172 prefixEnd_2687172 := by exact prefixLift 2687172
  have htrace : WordTrace (prefixWord ++ tailWord_2687172) baseStart_2687172 baseEnd_2687172 := by
    simpa [prefixWord, tailWord_2687172, baseEnd_2687172] using wordTrace_append hprefix tailTrace_2687172
  have hstable : (prefixWord ++ tailWord_2687172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687172).length < 2 ^ (prefixWord ++ tailWord_2687172).sum := by decide
  have hdescent : baseEnd_2687172 < baseStart_2687172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687189 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2687189 : Nat := 118140960795 + 2687189 * 2 ^ 59
def prefixEnd_2687189 : Nat := 4983230072969 + 3 ^ 40 * 2687189 * 2
def baseEnd_2687189 : Nat := 1379819566474792094379349

theorem tailTrace_2687189 : CollatzResearch.WordTrace tailWord_2687189 prefixEnd_2687189 1379819566474792094379349 := by
  unfold tailWord_2687189
  simp only [CollatzResearch.WordTrace]
  refine ⟨98009834661780663188600621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65339889774520442125733747 98009834661780663188600621)
  ·
    refine ⟨36753687998167748695725233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98009834661780663188600621 36753687998167748695725233)
    ·
      refine ⟨27565265998625811521793925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36753687998167748695725233 27565265998625811521793925)
      ·
        refine ⟨5168487374742339660336361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27565265998625811521793925 5168487374742339660336361)
        ·
          refine ⟨3876365531056754745252271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5168487374742339660336361 3876365531056754745252271)
          ·
            refine ⟨5814548296585132117878407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876365531056754745252271 5814548296585132117878407)
            ·
              refine ⟨8721822444877698176817611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5814548296585132117878407 8721822444877698176817611)
              ·
                refine ⟨13082733667316547265226417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8721822444877698176817611 13082733667316547265226417)
                ·
                  refine ⟨9812050250487410448919813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13082733667316547265226417 9812050250487410448919813)
                  ·
                    refine ⟨1839759421966389459172465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9812050250487410448919813 1839759421966389459172465)
                    ·
                      refine ⟨1379819566474792094379349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839759421966389459172465 1379819566474792094379349)
                      ·
                        rfl

theorem cell23_2687189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2687189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687189 prefixEnd_2687189 := by exact prefixLift 2687189
  have htrace : WordTrace (prefixWord ++ tailWord_2687189) baseStart_2687189 baseEnd_2687189 := by
    simpa [prefixWord, tailWord_2687189, baseEnd_2687189] using wordTrace_append hprefix tailTrace_2687189
  have hstable : (prefixWord ++ tailWord_2687189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687189).length < 2 ^ (prefixWord ++ tailWord_2687189).sum := by decide
  have hdescent : baseEnd_2687189 < baseStart_2687189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687232 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2]
def baseStart_2687232 : Nat := 118140960795 + 2687232 * 2 ^ 59
def prefixEnd_2687232 : Nat := 4983230072969 + 3 ^ 40 * 2687232 * 2
def baseEnd_2687232 : Nat := 1379841646142935426141651

theorem tailTrace_2687232 : CollatzResearch.WordTrace tailWord_2687232 prefixEnd_2687232 1379841646142935426141651 := by
  unfold tailWord_2687232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49005701500312440766207975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65340935333749921021610633 49005701500312440766207975)
  ·
    refine ⟨73508552250468661149311963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49005701500312440766207975 73508552250468661149311963)
    ·
      refine ⟨110262828375702991723967945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73508552250468661149311963 110262828375702991723967945)
      ·
        refine ⟨82697121281777243792975959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110262828375702991723967945 82697121281777243792975959)
        ·
          refine ⟨124045681922665865689463939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82697121281777243792975959 124045681922665865689463939)
          ·
            refine ⟨186068522883998798534195909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124045681922665865689463939 186068522883998798534195909)
            ·
              refine ⟨34887848040749774725161733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186068522883998798534195909 34887848040749774725161733)
              ·
                refine ⟨6541471507640582760967825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34887848040749774725161733 6541471507640582760967825)
                ·
                  refine ⟨4906103630730437070725869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6541471507640582760967825 4906103630730437070725869)
                  ·
                    refine ⟨1839788861523913901522201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4906103630730437070725869 1839788861523913901522201)
                    ·
                      refine ⟨1379841646142935426141651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839788861523913901522201 1379841646142935426141651)
                      ·
                        rfl

theorem cell23_2687232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_2687232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687232 prefixEnd_2687232 := by exact prefixLift 2687232
  have htrace : WordTrace (prefixWord ++ tailWord_2687232) baseStart_2687232 baseEnd_2687232 := by
    simpa [prefixWord, tailWord_2687232, baseEnd_2687232] using wordTrace_append hprefix tailTrace_2687232
  have hstable : (prefixWord ++ tailWord_2687232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687232).length < 2 ^ (prefixWord ++ tailWord_2687232).sum := by decide
  have hdescent : baseEnd_2687232 < baseStart_2687232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687316 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_2687316 : Nat := 118140960795 + 2687316 * 2 ^ 59
def prefixEnd_2687316 : Nat := 4983230072969 + 3 ^ 40 * 2687316 * 2
def baseEnd_2687316 : Nat := 1379884778517913097491265

theorem tailTrace_2687316 : CollatzResearch.WordTrace tailWord_2687316 prefixEnd_2687316 1379884778517913097491265 := by
  unfold tailWord_2687316
  simp only [CollatzResearch.WordTrace]
  refine ⟨49007233366160281939236901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65342977821547042585649201 49007233366160281939236901)
  ·
    refine ⟨9188856256155052863606919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49007233366160281939236901 9188856256155052863606919)
    ·
      refine ⟨13783284384232579295410379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9188856256155052863606919 13783284384232579295410379)
      ·
        refine ⟨20674926576348868943115569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783284384232579295410379 20674926576348868943115569)
        ·
          refine ⟨15506194932261651707336677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20674926576348868943115569 15506194932261651707336677)
          ·
            refine ⟨2907411549799059695125627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15506194932261651707336677 2907411549799059695125627)
            ·
              refine ⟨4361117324698589542688441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907411549799059695125627 4361117324698589542688441)
              ·
                refine ⟨3270837993523942157016331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361117324698589542688441 3270837993523942157016331)
                ·
                  refine ⟨4906256990285913235524497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270837993523942157016331 4906256990285913235524497)
                  ·
                    refine ⟨3679692742714434926643373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4906256990285913235524497 3679692742714434926643373)
                    ·
                      refine ⟨1379884778517913097491265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3679692742714434926643373 1379884778517913097491265)
                      ·
                        rfl

theorem cell23_2687316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_2687316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687316 prefixEnd_2687316 := by exact prefixLift 2687316
  have htrace : WordTrace (prefixWord ++ tailWord_2687316) baseStart_2687316 baseEnd_2687316 := by
    simpa [prefixWord, tailWord_2687316, baseEnd_2687316] using wordTrace_append hprefix tailTrace_2687316
  have hstable : (prefixWord ++ tailWord_2687316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687316).length < 2 ^ (prefixWord ++ tailWord_2687316).sum := by decide
  have hdescent : baseEnd_2687316 < baseStart_2687316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687345 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2687345 : Nat := 118140960795 + 2687345 * 2 ^ 59
def prefixEnd_2687345 : Nat := 4983230072969 + 3 ^ 40 * 2687345 * 2
def baseEnd_2687345 : Nat := 459966556485631161342877

theorem tailTrace_2687345 : CollatzResearch.WordTrace tailWord_2687345 prefixEnd_2687345 459966556485631161342877 := by
  unfold tailWord_2687345
  simp only [CollatzResearch.WordTrace]
  refine ⟨98015524449215501831279489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65343682966143667887519659 98015524449215501831279489)
  ·
    refine ⟨73511643336911626373459617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98015524449215501831279489 73511643336911626373459617)
    ·
      refine ⟨55133732502683719780094713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73511643336911626373459617 55133732502683719780094713)
      ·
        refine ⟨41350299377012789835071035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55133732502683719780094713 41350299377012789835071035)
        ·
          refine ⟨62025449065519184752606553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41350299377012789835071035 62025449065519184752606553)
          ·
            refine ⟨46519086799139388564454915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62025449065519184752606553 46519086799139388564454915)
            ·
              refine ⟨69778630198709082846682373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46519086799139388564454915 69778630198709082846682373)
              ·
                refine ⟨13083493162257953033752945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69778630198709082846682373 13083493162257953033752945)
                ·
                  refine ⟨9812619871693464775314709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13083493162257953033752945 9812619871693464775314709)
                  ·
                    refine ⟨459966556485631161342877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9812619871693464775314709 459966556485631161342877)
                    ·
                      rfl

theorem cell23_2687345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2687345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687345 prefixEnd_2687345 := by exact prefixLift 2687345
  have htrace : WordTrace (prefixWord ++ tailWord_2687345) baseStart_2687345 baseEnd_2687345 := by
    simpa [prefixWord, tailWord_2687345, baseEnd_2687345] using wordTrace_append hprefix tailTrace_2687345
  have hstable : (prefixWord ++ tailWord_2687345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687345).length < 2 ^ (prefixWord ++ tailWord_2687345).sum := by decide
  have hdescent : baseEnd_2687345 < baseStart_2687345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687346 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_2687346 : Nat := 118140960795 + 2687346 * 2 ^ 59
def prefixEnd_2687346 : Nat := 4983230072969 + 3 ^ 40 * 2687346 * 2
def baseEnd_2687346 : Nat := 1379900182937547980116127

theorem tailTrace_2687346 : CollatzResearch.WordTrace tailWord_2687346 prefixEnd_2687346 1379900182937547980116127 := by
  unfold tailWord_2687346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24503890230552969750516473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65343707281474586001377261 24503890230552969750516473)
  ·
    refine ⟨18377917672914727312887355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24503890230552969750516473 18377917672914727312887355)
    ·
      refine ⟨27566876509372090969331033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18377917672914727312887355 27566876509372090969331033)
      ·
        refine ⟨20675157382029068226998275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27566876509372090969331033 20675157382029068226998275)
        ·
          refine ⟨31012736073043602340497413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20675157382029068226998275 31012736073043602340497413)
          ·
            refine ⟨5814888013695675438843265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31012736073043602340497413 5814888013695675438843265)
            ·
              refine ⟨4361166010271756579132449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5814888013695675438843265 4361166010271756579132449)
              ·
                refine ⟨3270874507703817434349337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361166010271756579132449 3270874507703817434349337)
                ·
                  refine ⟨2453155880777863075762003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270874507703817434349337 2453155880777863075762003)
                  ·
                    refine ⟨3679733821166794613643005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453155880777863075762003 3679733821166794613643005)
                    ·
                      refine ⟨1379900182937547980116127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3679733821166794613643005 1379900182937547980116127)
                      ·
                        rfl

theorem cell23_2687346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_2687346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687346 prefixEnd_2687346 := by exact prefixLift 2687346
  have htrace : WordTrace (prefixWord ++ tailWord_2687346) baseStart_2687346 baseEnd_2687346 := by
    simpa [prefixWord, tailWord_2687346, baseEnd_2687346] using wordTrace_append hprefix tailTrace_2687346
  have hstable : (prefixWord ++ tailWord_2687346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687346).length < 2 ^ (prefixWord ++ tailWord_2687346).sum := by decide
  have hdescent : baseEnd_2687346 < baseStart_2687346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687369 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 4, 2]
def baseStart_2687369 : Nat := 118140960795 + 2687369 * 2 ^ 59
def prefixEnd_2687369 : Nat := 4983230072969 + 3 ^ 40 * 2687369 * 2
def baseEnd_2687369 : Nat := 1379911992992601390128521

theorem tailTrace_2687369 : CollatzResearch.WordTrace tailWord_2687369 prefixEnd_2687369 1379911992992601390128521 := by
  unfold tailWord_2687369
  simp only [CollatzResearch.WordTrace]
  refine ⟨98016399801128553930153161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65344266534085702620102107 98016399801128553930153161)
  ·
    refine ⟨73512299850846415447614871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98016399801128553930153161 73512299850846415447614871)
    ·
      refine ⟨110268449776269623171422307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73512299850846415447614871 110268449776269623171422307)
      ·
        refine ⟨165402674664404434757133461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110268449776269623171422307 165402674664404434757133461)
        ·
          refine ⟨7753250374893957879240631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165402674664404434757133461 7753250374893957879240631)
          ·
            refine ⟨11629875562340936818860947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7753250374893957879240631 11629875562340936818860947)
            ·
              refine ⟨17444813343511405228291421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629875562340936818860947 17444813343511405228291421)
              ·
                refine ⟨6541805003816776960609283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17444813343511405228291421 6541805003816776960609283)
                ·
                  refine ⟨9812707505725165440913925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541805003816776960609283 9812707505725165440913925)
                  ·
                    refine ⟨1839882657323468520171361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9812707505725165440913925 1839882657323468520171361)
                    ·
                      refine ⟨1379911992992601390128521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839882657323468520171361 1379911992992601390128521)
                      ·
                        rfl

theorem cell23_2687369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 4, 2].length) (baseStart_2687369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687369 prefixEnd_2687369 := by exact prefixLift 2687369
  have htrace : WordTrace (prefixWord ++ tailWord_2687369) baseStart_2687369 baseEnd_2687369 := by
    simpa [prefixWord, tailWord_2687369, baseEnd_2687369] using wordTrace_append hprefix tailTrace_2687369
  have hstable : (prefixWord ++ tailWord_2687369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687369).length < 2 ^ (prefixWord ++ tailWord_2687369).sum := by decide
  have hdescent : baseEnd_2687369 < baseStart_2687369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687390 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2687390 : Nat := 118140960795 + 2687390 * 2 ^ 59
def prefixEnd_2687390 : Nat := 4983230072969 + 3 ^ 40 * 2687390 * 2
def baseEnd_2687390 : Nat := 1379922776086345807965925

theorem tailTrace_2687390 : CollatzResearch.WordTrace tailWord_2687390 prefixEnd_2687390 1379922776086345807965925 := by
  unfold tailWord_2687390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252145716756559314583453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65344777156034983011111749 12252145716756559314583453)
  ·
    refine ⟨4594554643783709742968795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12252145716756559314583453 4594554643783709742968795)
    ·
      refine ⟨6891831965675564614453193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594554643783709742968795 6891831965675564614453193)
      ·
        refine ⟨5168873974256673460839895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6891831965675564614453193 5168873974256673460839895)
        ·
          refine ⟨7753310961385010191259843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168873974256673460839895 7753310961385010191259843)
          ·
            refine ⟨11629966442077515286889765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7753310961385010191259843 11629966442077515286889765)
            ·
              refine ⟨2180618707889534116291831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11629966442077515286889765 2180618707889534116291831)
              ·
                refine ⟨3270928061834301174437747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180618707889534116291831 3270928061834301174437747)
                ·
                  refine ⟨4906392092751451761656621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270928061834301174437747 4906392092751451761656621)
                  ·
                    refine ⟨1839897034781794410621233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4906392092751451761656621 1839897034781794410621233)
                    ·
                      refine ⟨1379922776086345807965925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839897034781794410621233 1379922776086345807965925)
                      ·
                        rfl

theorem cell23_2687390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2687390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687390 prefixEnd_2687390 := by exact prefixLift 2687390
  have htrace : WordTrace (prefixWord ++ tailWord_2687390) baseStart_2687390 baseEnd_2687390 := by
    simpa [prefixWord, tailWord_2687390, baseEnd_2687390] using wordTrace_append hprefix tailTrace_2687390
  have hstable : (prefixWord ++ tailWord_2687390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687390).length < 2 ^ (prefixWord ++ tailWord_2687390).sum := by decide
  have hdescent : baseEnd_2687390 < baseStart_2687390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687409 : List Nat := [1, 2, 2, 4, 1, 2, 2, 4, 5]
def baseStart_2687409 : Nat := 118140960795 + 2687409 * 2 ^ 59
def prefixEnd_2687409 : Nat := 4983230072969 + 3 ^ 40 * 2687409 * 2
def baseEnd_2687409 : Nat := 153325836913197914847593

theorem tailTrace_2687409 : CollatzResearch.WordTrace tailWord_2687409 prefixEnd_2687409 153325836913197914847593 := by
  unfold tailWord_2687409
  simp only [CollatzResearch.WordTrace]
  refine ⟨98017858720983640761609281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65345239147322427174406187 98017858720983640761609281)
  ·
    refine ⟨73513394040737730571206961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98017858720983640761609281 73513394040737730571206961)
    ·
      refine ⟨55135045530553297928405221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73513394040737730571206961 55135045530553297928405221)
      ·
        refine ⟨10337821036978743361575979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55135045530553297928405221 10337821036978743361575979)
        ·
          refine ⟨15506731555468115042363969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337821036978743361575979 15506731555468115042363969)
          ·
            refine ⟨11630048666601086281772977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15506731555468115042363969 11630048666601086281772977)
            ·
              refine ⟨8722536499950814711329733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11630048666601086281772977 8722536499950814711329733)
              ·
                refine ⟨1635475593740777758374325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8722536499950814711329733 1635475593740777758374325)
                ·
                  refine ⟨153325836913197914847593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1635475593740777758374325 153325836913197914847593)
                  ·
                    rfl

theorem cell23_2687409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 5].length) (baseStart_2687409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687409 prefixEnd_2687409 := by exact prefixLift 2687409
  have htrace : WordTrace (prefixWord ++ tailWord_2687409) baseStart_2687409 baseEnd_2687409 := by
    simpa [prefixWord, tailWord_2687409, baseEnd_2687409] using wordTrace_append hprefix tailTrace_2687409
  have hstable : (prefixWord ++ tailWord_2687409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687409).length < 2 ^ (prefixWord ++ tailWord_2687409).sum := by decide
  have hdescent : baseEnd_2687409 < baseStart_2687409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687420 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2687420 : Nat := 118140960795 + 2687420 * 2 ^ 59
def prefixEnd_2687420 : Nat := 4983230072969 + 3 ^ 40 * 2687420 * 2
def baseEnd_2687420 : Nat := 1379938180505980690590787

theorem tailTrace_2687420 : CollatzResearch.WordTrace tailWord_2687420 prefixEnd_2687420 1379938180505980690590787 := by
  unfold tailWord_2687420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49009129961971894820129857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65345506615962526426839809 49009129961971894820129857)
  ·
    refine ⟨36756847471478921115097393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49009129961971894820129857 36756847471478921115097393)
    ·
      refine ⟨27567635603609190836323045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36756847471478921115097393 27567635603609190836323045)
      ·
        refine ⟨5168931675676723281810571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27567635603609190836323045 5168931675676723281810571)
        ·
          refine ⟨7753397513515084922715857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168931675676723281810571 7753397513515084922715857)
          ·
            refine ⟨5815048135136313692036893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7753397513515084922715857 5815048135136313692036893)
            ·
              refine ⟨2180643050676117634513835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5815048135136313692036893 2180643050676117634513835)
              ·
                refine ⟨3270964576014176451770753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180643050676117634513835 3270964576014176451770753)
                ·
                  refine ⟨2453223432010632338828065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270964576014176451770753 2453223432010632338828065)
                  ·
                    refine ⟨1839917574007974254121049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2453223432010632338828065 1839917574007974254121049)
                    ·
                      refine ⟨1379938180505980690590787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839917574007974254121049 1379938180505980690590787)
                      ·
                        rfl

theorem cell23_2687420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2687420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687420 prefixEnd_2687420 := by exact prefixLift 2687420
  have htrace : WordTrace (prefixWord ++ tailWord_2687420) baseStart_2687420 baseEnd_2687420 := by
    simpa [prefixWord, tailWord_2687420, baseEnd_2687420] using wordTrace_append hprefix tailTrace_2687420
  have hstable : (prefixWord ++ tailWord_2687420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687420).length < 2 ^ (prefixWord ++ tailWord_2687420).sum := by decide
  have hdescent : baseEnd_2687420 < baseStart_2687420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687422 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2687422 : Nat := 118140960795 + 2687422 * 2 ^ 59
def prefixEnd_2687422 : Nat := 4983230072969 + 3 ^ 40 * 2687422 * 2
def baseEnd_2687422 : Nat := 459979735822429894255259

theorem tailTrace_2687422 : CollatzResearch.WordTrace tailWord_2687422 prefixEnd_2687422 459979735822429894255259 := by
  unfold tailWord_2687422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252291608742067997729065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65345555246624362654555013 12252291608742067997729065)
  ·
    refine ⟨9189218706556550998296799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12252291608742067997729065 9189218706556550998296799)
    ·
      refine ⟨13783828059834826497445199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189218706556550998296799 13783828059834826497445199)
      ·
        refine ⟨20675742089752239746167799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783828059834826497445199 20675742089752239746167799)
        ·
          refine ⟨31013613134628359619251699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20675742089752239746167799 31013613134628359619251699)
          ·
            refine ⟨46520419701942539428877549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31013613134628359619251699 46520419701942539428877549)
            ·
              refine ⟨17445157388228452285829081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46520419701942539428877549 17445157388228452285829081)
              ·
                refine ⟨13083868041171339214371811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17445157388228452285829081 13083868041171339214371811)
                ·
                  refine ⟨19625802061757008821557717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13083868041171339214371811 19625802061757008821557717)
                  ·
                    refine ⟨459979735822429894255259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19625802061757008821557717 459979735822429894255259)
                    ·
                      rfl

theorem cell23_2687422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2687422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687422 prefixEnd_2687422 := by exact prefixLift 2687422
  have htrace : WordTrace (prefixWord ++ tailWord_2687422) baseStart_2687422 baseEnd_2687422 := by
    simpa [prefixWord, tailWord_2687422, baseEnd_2687422] using wordTrace_append hprefix tailTrace_2687422
  have hstable : (prefixWord ++ tailWord_2687422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687422).length < 2 ^ (prefixWord ++ tailWord_2687422).sum := by decide
  have hdescent : baseEnd_2687422 < baseStart_2687422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687435 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 1, 10]
def baseStart_2687435 : Nat := 118140960795 + 2687435 * 2 ^ 59
def prefixEnd_2687435 : Nat := 4983230072969 + 3 ^ 40 * 2687435 * 2
def baseEnd_2687435 : Nat := 459981960905266043967739

theorem tailTrace_2687435 : CollatzResearch.WordTrace tailWord_2687435 prefixEnd_2687435 459981960905266043967739 := by
  unfold tailWord_2687435
  simp only [CollatzResearch.WordTrace]
  refine ⟨98018807018889447202055759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65345871345926298134703839 98018807018889447202055759)
  ·
    refine ⟨147028210528334170803083639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98018807018889447202055759 147028210528334170803083639)
    ·
      refine ⟨220542315792501256204625459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147028210528334170803083639 220542315792501256204625459)
      ·
        refine ⟨330813473688751884306938189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220542315792501256204625459 330813473688751884306938189)
        ·
          refine ⟨124055052633281956615101821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330813473688751884306938189 124055052633281956615101821)
          ·
            refine ⟨46520644737480733730663183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124055052633281956615101821 46520644737480733730663183)
            ·
              refine ⟨69780967106221100595994775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46520644737480733730663183 69780967106221100595994775)
              ·
                refine ⟨104671450659331650893992163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69780967106221100595994775 104671450659331650893992163)
                ·
                  refine ⟨157007175988997476340988245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104671450659331650893992163 157007175988997476340988245)
                  ·
                    refine ⟨459981960905266043967739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 157007175988997476340988245 459981960905266043967739)
                    ·
                      rfl

theorem cell23_2687435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_2687435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687435 prefixEnd_2687435 := by exact prefixLift 2687435
  have htrace : WordTrace (prefixWord ++ tailWord_2687435) baseStart_2687435 baseEnd_2687435 := by
    simpa [prefixWord, tailWord_2687435, baseEnd_2687435] using wordTrace_append hprefix tailTrace_2687435
  have hstable : (prefixWord ++ tailWord_2687435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687435).length < 2 ^ (prefixWord ++ tailWord_2687435).sum := by decide
  have hdescent : baseEnd_2687435 < baseStart_2687435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687519 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 5, 2]
def baseStart_2687519 : Nat := 118140960795 + 2687519 * 2 ^ 59
def prefixEnd_2687519 : Nat := 4983230072969 + 3 ^ 40 * 2687519 * 2
def baseEnd_2687519 : Nat := 1379989015090775803252831

theorem tailTrace_2687519 : CollatzResearch.WordTrace tailWord_2687519 prefixEnd_2687519 1379989015090775803252831 := by
  unfold tailWord_2687519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98021870750585129548113611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65347913833723419698742407 98021870750585129548113611)
  ·
    refine ⟨147032806125877694322170417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98021870750585129548113611 147032806125877694322170417)
    ·
      refine ⟨110274604594408270741627813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147032806125877694322170417 110274604594408270741627813)
      ·
        refine ⟨20676488361451550764055215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110274604594408270741627813 20676488361451550764055215)
        ·
          refine ⟨31014732542177326146082823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20676488361451550764055215 31014732542177326146082823)
          ·
            refine ⟨46522098813265989219124235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31014732542177326146082823 46522098813265989219124235)
            ·
              refine ⟨69783148219898983828686353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46522098813265989219124235 69783148219898983828686353)
              ·
                refine ⟨52337361164924237871514765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69783148219898983828686353 52337361164924237871514765)
                ·
                  refine ⟨19626510436846589201818037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52337361164924237871514765 19626510436846589201818037)
                  ·
                    refine ⟨1839985353454367737670441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19626510436846589201818037 1839985353454367737670441)
                    ·
                      refine ⟨1379989015090775803252831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839985353454367737670441 1379989015090775803252831)
                      ·
                        rfl

theorem cell23_2687519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_2687519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687519 prefixEnd_2687519 := by exact prefixLift 2687519
  have htrace : WordTrace (prefixWord ++ tailWord_2687519) baseStart_2687519 baseEnd_2687519 := by
    simpa [prefixWord, tailWord_2687519, baseEnd_2687519] using wordTrace_append hprefix tailTrace_2687519
  have hstable : (prefixWord ++ tailWord_2687519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687519).length < 2 ^ (prefixWord ++ tailWord_2687519).sum := by decide
  have hdescent : baseEnd_2687519 < baseStart_2687519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687553 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2687553 : Nat := 118140960795 + 2687553 * 2 ^ 59
def prefixEnd_2687553 : Nat := 4983230072969 + 3 ^ 40 * 2687553 * 2
def baseEnd_2687553 : Nat := 1380006473433028670227675

theorem tailTrace_2687553 : CollatzResearch.WordTrace tailWord_2687553 prefixEnd_2687553 1380006473433028670227675 := by
  unfold tailWord_2687553
  simp only [CollatzResearch.WordTrace]
  refine ⟨98023110832461953354851313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65348740554974635569900875 98023110832461953354851313)
  ·
    refine ⟨73517333124346465016138485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98023110832461953354851313 73517333124346465016138485)
    ·
      refine ⟨6892249980407481095262983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73517333124346465016138485 6892249980407481095262983)
      ·
        refine ⟨10338374970611221642894475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892249980407481095262983 10338374970611221642894475)
        ·
          refine ⟨15507562455916832464341713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338374970611221642894475 15507562455916832464341713)
          ·
            refine ⟨11630671841937624348256285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15507562455916832464341713 11630671841937624348256285)
            ·
              refine ⟨4361501940726609130596107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11630671841937624348256285 4361501940726609130596107)
              ·
                refine ⟨6542252911089913695894161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361501940726609130596107 6542252911089913695894161)
                ·
                  refine ⟨4906689683317435271920621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542252911089913695894161 4906689683317435271920621)
                  ·
                    refine ⟨1840008631244038226970233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4906689683317435271920621 1840008631244038226970233)
                    ·
                      refine ⟨1380006473433028670227675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840008631244038226970233 1380006473433028670227675)
                      ·
                        rfl

theorem cell23_2687553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2687553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687553 prefixEnd_2687553 := by exact prefixLift 2687553
  have htrace : WordTrace (prefixWord ++ tailWord_2687553) baseStart_2687553 baseEnd_2687553 := by
    simpa [prefixWord, tailWord_2687553, baseEnd_2687553] using wordTrace_append hprefix tailTrace_2687553
  have hstable : (prefixWord ++ tailWord_2687553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687553).length < 2 ^ (prefixWord ++ tailWord_2687553).sum := by decide
  have hdescent : baseEnd_2687553 < baseStart_2687553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687559 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2687559 : Nat := 118140960795 + 2687559 * 2 ^ 59
def prefixEnd_2687559 : Nat := 4983230072969 + 3 ^ 40 * 2687559 * 2
def baseEnd_2687559 : Nat := 460003184772318548917549

theorem tailTrace_2687559 : CollatzResearch.WordTrace tailWord_2687559 prefixEnd_2687559 460003184772318548917549 := by
  unfold tailWord_2687559
  simp only [CollatzResearch.WordTrace]
  refine ⟨98023329670440216379569731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65348886446960144253046487 98023329670440216379569731)
  ·
    refine ⟨147034994505660324569354597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98023329670440216379569731 147034994505660324569354597)
    ·
      refine ⟨27569061469811310856753987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147034994505660324569354597 27569061469811310856753987)
      ·
        refine ⟨41353592204716966285130981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27569061469811310856753987 41353592204716966285130981)
        ·
          refine ⟨7753798538384431178462059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41353592204716966285130981 7753798538384431178462059)
          ·
            refine ⟨11630697807576646767693089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7753798538384431178462059 11630697807576646767693089)
            ·
              refine ⟨8723023355682485075769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11630697807576646767693089 8723023355682485075769817)
              ·
                refine ⟨6542267516761863806827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723023355682485075769817 6542267516761863806827363)
                ·
                  refine ⟨9813401275142795710241045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542267516761863806827363 9813401275142795710241045)
                  ·
                    refine ⟨460003184772318548917549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9813401275142795710241045 460003184772318548917549)
                    ·
                      rfl

theorem cell23_2687559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2687559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687559 prefixEnd_2687559 := by exact prefixLift 2687559
  have htrace : WordTrace (prefixWord ++ tailWord_2687559) baseStart_2687559 baseEnd_2687559 := by
    simpa [prefixWord, tailWord_2687559, baseEnd_2687559] using wordTrace_append hprefix tailTrace_2687559
  have hstable : (prefixWord ++ tailWord_2687559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687559).length < 2 ^ (prefixWord ++ tailWord_2687559).sum := by decide
  have hdescent : baseEnd_2687559 < baseStart_2687559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687576 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_2687576 : Nat := 118140960795 + 2687576 * 2 ^ 59
def prefixEnd_2687576 : Nat := 4983230072969 + 3 ^ 40 * 2687576 * 2
def baseEnd_2687576 : Nat := 460006094496027360080023

theorem tailTrace_2687576 : CollatzResearch.WordTrace tailWord_2687576 prefixEnd_2687576 460006094496027360080023 := by
  unfold tailWord_2687576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49011974855689314141469291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65349299807585752188625721 49011974855689314141469291)
  ·
    refine ⟨73517962283533971212203937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49011974855689314141469291 73517962283533971212203937)
    ·
      refine ⟨55138471712650478409152953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73517962283533971212203937 55138471712650478409152953)
      ·
        refine ⟨41353853784487858806864715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55138471712650478409152953 41353853784487858806864715)
        ·
          refine ⟨62030780676731788210297073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41353853784487858806864715 62030780676731788210297073)
          ·
            refine ⟨46523085507548841157722805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62030780676731788210297073 46523085507548841157722805)
            ·
              refine ⟨4361539266332703858536513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46523085507548841157722805 4361539266332703858536513)
              ·
                refine ⟨3271154449749527893902385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361539266332703858536513 3271154449749527893902385)
                ·
                  refine ⟨2453365837312145920426789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271154449749527893902385 2453365837312145920426789)
                  ·
                    refine ⟨460006094496027360080023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453365837312145920426789 460006094496027360080023)
                    ·
                      rfl

theorem cell23_2687576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_2687576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687576 prefixEnd_2687576 := by exact prefixLift 2687576
  have htrace : WordTrace (prefixWord ++ tailWord_2687576) baseStart_2687576 baseEnd_2687576 := by
    simpa [prefixWord, tailWord_2687576, baseEnd_2687576] using wordTrace_append hprefix tailTrace_2687576
  have hstable : (prefixWord ++ tailWord_2687576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687576).length < 2 ^ (prefixWord ++ tailWord_2687576).sum := by decide
  have hdescent : baseEnd_2687576 < baseStart_2687576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687606 : List Nat := [5, 1, 1, 2, 3, 1, 1, 9]
def baseStart_2687606 : Nat := 118140960795 + 2687606 * 2 ^ 59
def prefixEnd_2687606 : Nat := 4983230072969 + 3 ^ 40 * 2687606 * 2
def baseEnd_2687606 : Nat := 51112358811396924550553

theorem tailTrace_2687606 : CollatzResearch.WordTrace tailWord_2687606 prefixEnd_2687606 51112358811396924550553 := by
  unfold tailWord_2687606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126565243829371462908167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65350029267513295604353781 6126565243829371462908167)
  ·
    refine ⟨9189847865744057194362251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6126565243829371462908167 9189847865744057194362251)
    ·
      refine ⟨13784771798616085791543377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189847865744057194362251 13784771798616085791543377)
      ·
        refine ⟨10338578848962064343657533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13784771798616085791543377 10338578848962064343657533)
        ·
          refine ⟨3876967068360774128871575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10338578848962064343657533 3876967068360774128871575)
          ·
            refine ⟨5815450602541161193307363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876967068360774128871575 5815450602541161193307363)
            ·
              refine ⟨8723175903811741789961045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815450602541161193307363 8723175903811741789961045)
              ·
                refine ⟨51112358811396924550553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8723175903811741789961045 51112358811396924550553)
                ·
                  rfl

theorem cell23_2687606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_2687606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687606 prefixEnd_2687606 := by exact prefixLift 2687606
  have htrace : WordTrace (prefixWord ++ tailWord_2687606) baseStart_2687606 baseEnd_2687606 := by
    simpa [prefixWord, tailWord_2687606, baseEnd_2687606] using wordTrace_append hprefix tailTrace_2687606
  have hstable : (prefixWord ++ tailWord_2687606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687606).length < 2 ^ (prefixWord ++ tailWord_2687606).sum := by decide
  have hdescent : baseEnd_2687606 < baseStart_2687606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687616 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_2687616 : Nat := 118140960795 + 2687616 * 2 ^ 59
def prefixEnd_2687616 : Nat := 4983230072969 + 3 ^ 40 * 2687616 * 2
def baseEnd_2687616 : Nat := 1380038822714261923739885

theorem tailTrace_2687616 : CollatzResearch.WordTrace tailWord_2687616 prefixEnd_2687616 1380038822714261923739885 := by
  unfold tailWord_2687616
  simp only [CollatzResearch.WordTrace]
  refine ⟨49012704315616857557197351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65350272420822476742929801 49012704315616857557197351)
  ·
    refine ⟨73519056473425286335796027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49012704315616857557197351 73519056473425286335796027)
    ·
      refine ⟨110278584710137929503694041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73519056473425286335796027 110278584710137929503694041)
      ·
        refine ⟨82708938532603447127770531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110278584710137929503694041 82708938532603447127770531)
        ·
          refine ⟨124063407798905170691655797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82708938532603447127770531 124063407798905170691655797)
          ·
            refine ⟨11630944481147359752342731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124063407798905170691655797 11630944481147359752342731)
            ·
              refine ⟨17446416721721039628514097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11630944481147359752342731 17446416721721039628514097)
              ·
                refine ⟨13084812541290779721385573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17446416721721039628514097 13084812541290779721385573)
                ·
                  refine ⟨2453402351492021197759795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13084812541290779721385573 2453402351492021197759795)
                  ·
                    refine ⟨3680103527238031796639693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453402351492021197759795 3680103527238031796639693)
                    ·
                      refine ⟨1380038822714261923739885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680103527238031796639693 1380038822714261923739885)
                      ·
                        rfl

theorem cell23_2687616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_2687616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687616 prefixEnd_2687616 := by exact prefixLift 2687616
  have htrace : WordTrace (prefixWord ++ tailWord_2687616) baseStart_2687616 baseEnd_2687616 := by
    simpa [prefixWord, tailWord_2687616, baseEnd_2687616] using wordTrace_append hprefix tailTrace_2687616
  have hstable : (prefixWord ++ tailWord_2687616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687616).length < 2 ^ (prefixWord ++ tailWord_2687616).sum := by decide
  have hdescent : baseEnd_2687616 < baseStart_2687616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687634 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_2687634 : Nat := 118140960795 + 2687634 * 2 ^ 59
def prefixEnd_2687634 : Nat := 4983230072969 + 3 ^ 40 * 2687634 * 2
def baseEnd_2687634 : Nat := 1380048065366042853314803

theorem tailTrace_2687634 : CollatzResearch.WordTrace tailWord_2687634 prefixEnd_2687634 1380048065366042853314803 := by
  unfold tailWord_2687634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506516286292126047137489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65350710096779002792366637 24506516286292126047137489)
  ·
    refine ⟨18379887214719094535353117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24506516286292126047137489 18379887214719094535353117)
    ·
      refine ⟨6892457705519660450757419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18379887214719094535353117 6892457705519660450757419)
      ·
        refine ⟨10338686558279490676136129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892457705519660450757419 10338686558279490676136129)
        ·
          refine ⟨7754014918709618007102097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10338686558279490676136129 7754014918709618007102097)
          ·
            refine ⟨5815511189032213505326573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7754014918709618007102097 5815511189032213505326573)
            ·
              refine ⟨2180816695887080064497465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5815511189032213505326573 2180816695887080064497465)
              ·
                refine ⟨1635612521915310048373099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180816695887080064497465 1635612521915310048373099)
                ·
                  refine ⟨2453418782872965072559649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635612521915310048373099 2453418782872965072559649)
                  ·
                    refine ⟨1840064087154723804419737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2453418782872965072559649 1840064087154723804419737)
                    ·
                      refine ⟨1380048065366042853314803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840064087154723804419737 1380048065366042853314803)
                      ·
                        rfl

theorem cell23_2687634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_2687634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687634 prefixEnd_2687634 := by exact prefixLift 2687634
  have htrace : WordTrace (prefixWord ++ tailWord_2687634) baseStart_2687634 baseEnd_2687634 := by
    simpa [prefixWord, tailWord_2687634, baseEnd_2687634] using wordTrace_append hprefix tailTrace_2687634
  have hstable : (prefixWord ++ tailWord_2687634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687634).length < 2 ^ (prefixWord ++ tailWord_2687634).sum := by decide
  have hdescent : baseEnd_2687634 < baseStart_2687634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687639 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2687639 : Nat := 118140960795 + 2687639 * 2 ^ 59
def prefixEnd_2687639 : Nat := 4983230072969 + 3 ^ 40 * 2687639 * 2
def baseEnd_2687639 : Nat := 1380050632769315333752279

theorem tailTrace_2687639 : CollatzResearch.WordTrace tailWord_2687639 prefixEnd_2687639 1380050632769315333752279 := by
  unfold tailWord_2687639
  simp only [CollatzResearch.WordTrace]
  refine ⟨98026247510150390042481971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65350831673433593361654647 98026247510150390042481971)
  ·
    refine ⟨147039371265225585063722957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98026247510150390042481971 147039371265225585063722957)
    ·
      refine ⟨55139764224459594398896109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147039371265225585063722957 55139764224459594398896109)
      ·
        refine ⟨20677411584172347899586041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55139764224459594398896109 20677411584172347899586041)
        ·
          refine ⟨15508058688129260924689531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20677411584172347899586041 15508058688129260924689531)
          ·
            refine ⟨23262088032193891387034297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15508058688129260924689531 23262088032193891387034297)
            ·
              refine ⟨17446566024145418540275723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23262088032193891387034297 17446566024145418540275723)
              ·
                refine ⟨26169849036218127810413585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17446566024145418540275723 26169849036218127810413585)
                ·
                  refine ⟨19627386777163595857810189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26169849036218127810413585 19627386777163595857810189)
                  ·
                    refine ⟨7360270041436348446678821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19627386777163595857810189 7360270041436348446678821)
                    ·
                      refine ⟨1380050632769315333752279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7360270041436348446678821 1380050632769315333752279)
                      ·
                        rfl

theorem cell23_2687639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2687639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687639 prefixEnd_2687639 := by exact prefixLift 2687639
  have htrace : WordTrace (prefixWord ++ tailWord_2687639) baseStart_2687639 baseEnd_2687639 := by
    simpa [prefixWord, tailWord_2687639, baseEnd_2687639] using wordTrace_append hprefix tailTrace_2687639
  have hstable : (prefixWord ++ tailWord_2687639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687639).length < 2 ^ (prefixWord ++ tailWord_2687639).sum := by decide
  have hdescent : baseEnd_2687639 < baseStart_2687639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687689 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_2687689 : Nat := 118140960795 + 2687689 * 2 ^ 59
def prefixEnd_2687689 : Nat := 4983230072969 + 3 ^ 40 * 2687689 * 2
def baseEnd_2687689 : Nat := 1380076306802040138127049

theorem tailTrace_2687689 : CollatzResearch.WordTrace tailWord_2687689 prefixEnd_2687689 1380076306802040138127049 := by
  unfold tailWord_2687689
  simp only [CollatzResearch.WordTrace]
  refine ⟨98028071159969248581802121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65352047439979499054534747 98028071159969248581802121)
  ·
    refine ⟨73521053369976936436351591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98028071159969248581802121 73521053369976936436351591)
    ·
      refine ⟨110281580054965404654527387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73521053369976936436351591 110281580054965404654527387)
      ·
        refine ⟨165422370082448106981791081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110281580054965404654527387 165422370082448106981791081)
        ·
          refine ⟨124066777561836080236343311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165422370082448106981791081 124066777561836080236343311)
          ·
            refine ⟨186100166342754120354514967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124066777561836080236343311 186100166342754120354514967)
            ·
              refine ⟨279150249514131180531772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186100166342754120354514967 279150249514131180531772451)
              ·
                refine ⟨418725374271196770797658677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279150249514131180531772451 418725374271196770797658677)
                ·
                  refine ⟨39255503837924697262280501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418725374271196770797658677 39255503837924697262280501)
                  ·
                    refine ⟨3680203484805440368338797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39255503837924697262280501 3680203484805440368338797)
                    ·
                      refine ⟨1380076306802040138127049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680203484805440368338797 1380076306802040138127049)
                      ·
                        rfl

theorem cell23_2687689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_2687689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687689 prefixEnd_2687689 := by exact prefixLift 2687689
  have htrace : WordTrace (prefixWord ++ tailWord_2687689) baseStart_2687689 baseEnd_2687689 := by
    simpa [prefixWord, tailWord_2687689, baseEnd_2687689] using wordTrace_append hprefix tailTrace_2687689
  have hstable : (prefixWord ++ tailWord_2687689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687689).length < 2 ^ (prefixWord ++ tailWord_2687689).sum := by decide
  have hdescent : baseEnd_2687689 < baseStart_2687689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687690 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_2687690 : Nat := 118140960795 + 2687690 * 2 ^ 59
def prefixEnd_2687690 : Nat := 4983230072969 + 3 ^ 40 * 2687690 * 2
def baseEnd_2687690 : Nat := 1380076820282694634214545

theorem tailTrace_2687690 : CollatzResearch.WordTrace tailWord_2687690 prefixEnd_2687690 1380076820282694634214545 := by
  unfold tailWord_2687690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24507026908241406438147131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65352071755310417168392349 24507026908241406438147131)
  ·
    refine ⟨36760540362362109657220697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24507026908241406438147131 36760540362362109657220697)
    ·
      refine ⟨27570405271771582242915523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36760540362362109657220697 27570405271771582242915523)
      ·
        refine ⟨41355607907657373364373285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27570405271771582242915523 41355607907657373364373285)
        ·
          refine ⟨7754176482685757505819991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41355607907657373364373285 7754176482685757505819991)
          ·
            refine ⟨11631264724028636258729987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754176482685757505819991 11631264724028636258729987)
            ·
              refine ⟨17446897086042954388094981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11631264724028636258729987 17446897086042954388094981)
              ·
                refine ⟨3271293203633053947767809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17446897086042954388094981 3271293203633053947767809)
                ·
                  refine ⟨2453469902724790460825857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271293203633053947767809 2453469902724790460825857)
                  ·
                    refine ⟨1840102427043592845619393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2453469902724790460825857 1840102427043592845619393)
                    ·
                      refine ⟨1380076820282694634214545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840102427043592845619393 1380076820282694634214545)
                      ·
                        rfl

theorem cell23_2687690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_2687690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687690 prefixEnd_2687690 := by exact prefixLift 2687690
  have htrace : WordTrace (prefixWord ++ tailWord_2687690) baseStart_2687690 baseEnd_2687690 := by
    simpa [prefixWord, tailWord_2687690, baseEnd_2687690] using wordTrace_append hprefix tailTrace_2687690
  have hstable : (prefixWord ++ tailWord_2687690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687690).length < 2 ^ (prefixWord ++ tailWord_2687690).sum := by decide
  have hdescent : baseEnd_2687690 < baseStart_2687690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687706 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_2687706 : Nat := 118140960795 + 2687706 * 2 ^ 59
def prefixEnd_2687706 : Nat := 4983230072969 + 3 ^ 40 * 2687706 * 2
def baseEnd_2687706 : Nat := 1380085035973166571614471

theorem tailTrace_2687706 : CollatzResearch.WordTrace tailWord_2687706 prefixEnd_2687706 1380085035973166571614471 := by
  unfold tailWord_2687706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24507172800226915121292743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65352460800605106990113981 24507172800226915121292743)
  ·
    refine ⟨36760759200340372681939115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24507172800226915121292743 36760759200340372681939115)
    ·
      refine ⟨55141138800510559022908673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36760759200340372681939115 55141138800510559022908673)
      ·
        refine ⟨41355854100382919267181505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55141138800510559022908673 41355854100382919267181505)
        ·
          refine ⟨31016890575287189450386129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41355854100382919267181505 31016890575287189450386129)
          ·
            refine ⟨23262667931465392087789597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31016890575287189450386129 23262667931465392087789597)
            ·
              refine ⟨8723500474299522032921099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23262667931465392087789597 8723500474299522032921099)
              ·
                refine ⟨13085250711449283049381649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8723500474299522032921099 13085250711449283049381649)
                ·
                  refine ⟨9813938033586962287036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13085250711449283049381649 9813938033586962287036237)
                  ·
                    refine ⟨3680226762595110857638589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9813938033586962287036237 3680226762595110857638589)
                    ·
                      refine ⟨1380085035973166571614471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680226762595110857638589 1380085035973166571614471)
                      ·
                        rfl

theorem cell23_2687706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_2687706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687706 prefixEnd_2687706 := by exact prefixLift 2687706
  have htrace : WordTrace (prefixWord ++ tailWord_2687706) baseStart_2687706 baseEnd_2687706 := by
    simpa [prefixWord, tailWord_2687706, baseEnd_2687706] using wordTrace_append hprefix tailTrace_2687706
  have hstable : (prefixWord ++ tailWord_2687706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687706).length < 2 ^ (prefixWord ++ tailWord_2687706).sum := by decide
  have hdescent : baseEnd_2687706 < baseStart_2687706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687726 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2687726 : Nat := 118140960795 + 2687726 * 2 ^ 59
def prefixEnd_2687726 : Nat := 4983230072969 + 3 ^ 40 * 2687726 * 2
def baseEnd_2687726 : Nat := 460031768528752164454793

theorem tailTrace_2687726 : CollatzResearch.WordTrace tailWord_2687726 prefixEnd_2687726 460031768528752164454793 := by
  unfold tailWord_2687726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253677582604400487612379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65352947107223469267266021 12253677582604400487612379)
  ·
    refine ⟨18380516373906600731418569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12253677582604400487612379 18380516373906600731418569)
    ·
      refine ⟨13785387280429950548563927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18380516373906600731418569 13785387280429950548563927)
      ·
        refine ⟨20678080920644925822845891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13785387280429950548563927 20678080920644925822845891)
        ·
          refine ⟨31017121380967388734268837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20678080920644925822845891 31017121380967388734268837)
          ·
            refine ⟨5815710258931385387675407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31017121380967388734268837 5815710258931385387675407)
            ·
              refine ⟨8723565388397078081513111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815710258931385387675407 8723565388397078081513111)
              ·
                refine ⟨13085348082595617122269667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8723565388397078081513111 13085348082595617122269667)
                ·
                  refine ⟨19628022123893425683404501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13085348082595617122269667 19628022123893425683404501)
                  ·
                    refine ⟨460031768528752164454793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19628022123893425683404501 460031768528752164454793)
                    ·
                      rfl

theorem cell23_2687726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2687726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687726 prefixEnd_2687726 := by exact prefixLift 2687726
  have htrace : WordTrace (prefixWord ++ tailWord_2687726) baseStart_2687726 baseEnd_2687726 := by
    simpa [prefixWord, tailWord_2687726, baseEnd_2687726] using wordTrace_append hprefix tailTrace_2687726
  have hstable : (prefixWord ++ tailWord_2687726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687726).length < 2 ^ (prefixWord ++ tailWord_2687726).sum := by decide
  have hdescent : baseEnd_2687726 < baseStart_2687726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687749 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_2687749 : Nat := 118140960795 + 2687749 * 2 ^ 59
def prefixEnd_2687749 : Nat := 4983230072969 + 3 ^ 40 * 2687749 * 2
def baseEnd_2687749 : Nat := 1380107115641309903376773

theorem tailTrace_2687749 : CollatzResearch.WordTrace tailWord_2687749 prefixEnd_2687749 1380107115641309903376773 := by
  unfold tailWord_2687749
  simp only [CollatzResearch.WordTrace]
  refine ⟨98030259539751878828986301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65353506359834585885990867 98030259539751878828986301)
  ·
    refine ⟨36761347327406954560869863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98030259539751878828986301 36761347327406954560869863)
    ·
      refine ⟨55142020991110431841304795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36761347327406954560869863 55142020991110431841304795)
      ·
        refine ⟨82713031486665647761957193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55142020991110431841304795 82713031486665647761957193)
        ·
          refine ⟨62034773614999235821467895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82713031486665647761957193 62034773614999235821467895)
          ·
            refine ⟨93052160422498853732201843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62034773614999235821467895 93052160422498853732201843)
            ·
              refine ⟨139578240633748280598302765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93052160422498853732201843 139578240633748280598302765)
              ·
                refine ⟨52341840237655605224363537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139578240633748280598302765 52341840237655605224363537)
                ·
                  refine ⟨39256380178241703918272653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52341840237655605224363537 39256380178241703918272653)
                  ·
                    refine ⟨14721142566840638969352245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39256380178241703918272653 14721142566840638969352245)
                    ·
                      refine ⟨1380107115641309903376773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14721142566840638969352245 1380107115641309903376773)
                      ·
                        rfl

theorem cell23_2687749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_2687749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687749 prefixEnd_2687749 := by exact prefixLift 2687749
  have htrace : WordTrace (prefixWord ++ tailWord_2687749) baseStart_2687749 baseEnd_2687749 := by
    simpa [prefixWord, tailWord_2687749, baseEnd_2687749] using wordTrace_append hprefix tailTrace_2687749
  have hstable : (prefixWord ++ tailWord_2687749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687749).length < 2 ^ (prefixWord ++ tailWord_2687749).sum := by decide
  have hdescent : baseEnd_2687749 < baseStart_2687749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687759 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_2687759 : Nat := 118140960795 + 2687759 * 2 ^ 59
def prefixEnd_2687759 : Nat := 4983230072969 + 3 ^ 40 * 2687759 * 2
def baseEnd_2687759 : Nat := 1380112250447854864251727

theorem tailTrace_2687759 : CollatzResearch.WordTrace tailWord_2687759 prefixEnd_2687759 1380112250447854864251727 := by
  unfold tailWord_2687759
  simp only [CollatzResearch.WordTrace]
  refine ⟨98030624269715650536850331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65353749513143767024566887 98030624269715650536850331)
  ·
    refine ⟨147045936404573475805275497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98030624269715650536850331 147045936404573475805275497)
    ·
      refine ⟨110284452303430106853956623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147045936404573475805275497 110284452303430106853956623)
      ·
        refine ⟨165426678455145160280934935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110284452303430106853956623 165426678455145160280934935)
        ·
          refine ⟨248140017682717740421402403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165426678455145160280934935 248140017682717740421402403)
          ·
            refine ⟨372210026524076610632103605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248140017682717740421402403 372210026524076610632103605)
            ·
              refine ⟨34894689986632182246759713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372210026524076610632103605 34894689986632182246759713)
              ·
                refine ⟨26171017489974136685069785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34894689986632182246759713 26171017489974136685069785)
                ·
                  refine ⟨19628263117480602513802339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26171017489974136685069785 19628263117480602513802339)
                  ·
                    refine ⟨29442394676220903770703509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19628263117480602513802339 29442394676220903770703509)
                    ·
                      refine ⟨1380112250447854864251727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29442394676220903770703509 1380112250447854864251727)
                      ·
                        rfl

theorem cell23_2687759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_2687759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687759 prefixEnd_2687759 := by exact prefixLift 2687759
  have htrace : WordTrace (prefixWord ++ tailWord_2687759) baseStart_2687759 baseEnd_2687759 := by
    simpa [prefixWord, tailWord_2687759, baseEnd_2687759] using wordTrace_append hprefix tailTrace_2687759
  have hstable : (prefixWord ++ tailWord_2687759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687759).length < 2 ^ (prefixWord ++ tailWord_2687759).sum := by decide
  have hdescent : baseEnd_2687759 < baseStart_2687759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687807 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 1, 4]
def baseStart_2687807 : Nat := 118140960795 + 2687807 * 2 ^ 59
def prefixEnd_2687807 : Nat := 4983230072969 + 3 ^ 40 * 2687807 * 2
def baseEnd_2687807 : Nat := 460045632506423558817169

theorem tailTrace_2687807 : CollatzResearch.WordTrace tailWord_2687807 prefixEnd_2687807 460045632506423558817169 := by
  unfold tailWord_2687807
  simp only [CollatzResearch.WordTrace]
  refine ⟨98032374973541754734597675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65354916649027836489731783 98032374973541754734597675)
  ·
    refine ⟨147048562460312632101896513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98032374973541754734597675 147048562460312632101896513)
    ·
      refine ⟨110286421845234474076422385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147048562460312632101896513 110286421845234474076422385)
      ·
        refine ⟨82714816383925855557316789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110286421845234474076422385 82714816383925855557316789)
        ·
          refine ⟨7754514035993048958498449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82714816383925855557316789 7754514035993048958498449)
          ·
            refine ⟨5815885526994786718873837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7754514035993048958498449 5815885526994786718873837)
            ·
              refine ⟨2180957072623045019577689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5815885526994786718873837 2180957072623045019577689)
              ·
                refine ⟨1635717804467283764683267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180957072623045019577689 1635717804467283764683267)
                ·
                  refine ⟨2453576706700925647024901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635717804467283764683267 2453576706700925647024901)
                  ·
                    refine ⟨460045632506423558817169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453576706700925647024901 460045632506423558817169)
                    ·
                      rfl

theorem cell23_2687807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_2687807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687807 prefixEnd_2687807 := by exact prefixLift 2687807
  have htrace : WordTrace (prefixWord ++ tailWord_2687807) baseStart_2687807 baseEnd_2687807 := by
    simpa [prefixWord, tailWord_2687807, baseEnd_2687807] using wordTrace_append hprefix tailTrace_2687807
  have hstable : (prefixWord ++ tailWord_2687807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687807).length < 2 ^ (prefixWord ++ tailWord_2687807).sum := by decide
  have hdescent : baseEnd_2687807 < baseStart_2687807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687813 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_2687813 : Nat := 118140960795 + 2687813 * 2 ^ 59
def prefixEnd_2687813 : Nat := 4983230072969 + 3 ^ 40 * 2687813 * 2
def baseEnd_2687813 : Nat := 1380139978403197652976479

theorem tailTrace_2687813 : CollatzResearch.WordTrace tailWord_2687813 prefixEnd_2687813 1380139978403197652976479 := by
  unfold tailWord_2687813
  simp only [CollatzResearch.WordTrace]
  refine ⟨98032593811520017759316093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65355062541013345172877395 98032593811520017759316093)
  ·
    refine ⟨36762222679320006659743535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98032593811520017759316093 36762222679320006659743535)
    ·
      refine ⟨55143334018980009989615303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36762222679320006659743535 55143334018980009989615303)
      ·
        refine ⟨82715001028470014984422955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55143334018980009989615303 82715001028470014984422955)
        ·
          refine ⟨124072501542705022476634433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82715001028470014984422955 124072501542705022476634433)
          ·
            refine ⟨93054376157028766857475825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124072501542705022476634433 93054376157028766857475825)
            ·
              refine ⟨69790782117771575143106869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93054376157028766857475825 69790782117771575143106869)
              ·
                refine ⟨6542885823541085169666269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69790782117771575143106869 6542885823541085169666269)
                ·
                  refine ⟨2453582183827906938624851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6542885823541085169666269 2453582183827906938624851)
                  ·
                    refine ⟨3680373275741860407937277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453582183827906938624851 3680373275741860407937277)
                    ·
                      refine ⟨1380139978403197652976479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680373275741860407937277 1380139978403197652976479)
                      ·
                        rfl

theorem cell23_2687813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_2687813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687813 prefixEnd_2687813 := by exact prefixLift 2687813
  have htrace : WordTrace (prefixWord ++ tailWord_2687813) baseStart_2687813 baseEnd_2687813 := by
    simpa [prefixWord, tailWord_2687813, baseEnd_2687813] using wordTrace_append hprefix tailTrace_2687813
  have hstable : (prefixWord ++ tailWord_2687813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687813).length < 2 ^ (prefixWord ++ tailWord_2687813).sum := by decide
  have hdescent : baseEnd_2687813 < baseStart_2687813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687816 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_2687816 : Nat := 118140960795 + 2687816 * 2 ^ 59
def prefixEnd_2687816 : Nat := 4983230072969 + 3 ^ 40 * 2687816 * 2
def baseEnd_2687816 : Nat := 460047172948387047079655

theorem tailTrace_2687816 : CollatzResearch.WordTrace tailWord_2687816 prefixEnd_2687816 460047172948387047079655 := by
  unfold tailWord_2687816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016351615254574635837651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65355135487006099514450201 49016351615254574635837651)
  ·
    refine ⟨73524527422881861953756477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49016351615254574635837651 73524527422881861953756477)
    ·
      refine ⟨27571697783580698232658679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73524527422881861953756477 27571697783580698232658679)
      ·
        refine ⟨41357546675371047348988019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27571697783580698232658679 41357546675371047348988019)
        ·
          refine ⟨62036320013056571023482029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41357546675371047348988019 62036320013056571023482029)
          ·
            refine ⟨23263620004896214133805761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62036320013056571023482029 23263620004896214133805761)
            ·
              refine ⟨17447715003672160600354321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23263620004896214133805761 17447715003672160600354321)
              ·
                refine ⟨13085786252754120450265741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17447715003672160600354321 13085786252754120450265741)
                ·
                  refine ⟨4907169844782795168849653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13085786252754120450265741 4907169844782795168849653)
                  ·
                    refine ⟨460047172948387047079655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4907169844782795168849653 460047172948387047079655)
                    ·
                      rfl

theorem cell23_2687816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_2687816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687816 prefixEnd_2687816 := by exact prefixLift 2687816
  have htrace : WordTrace (prefixWord ++ tailWord_2687816) baseStart_2687816 baseEnd_2687816 := by
    simpa [prefixWord, tailWord_2687816, baseEnd_2687816] using wordTrace_append hprefix tailTrace_2687816
  have hstable : (prefixWord ++ tailWord_2687816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687816).length < 2 ^ (prefixWord ++ tailWord_2687816).sum := by decide
  have hdescent : baseEnd_2687816 < baseStart_2687816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687819 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_2687819 : Nat := 118140960795 + 2687819 * 2 ^ 59
def prefixEnd_2687819 : Nat := 4983230072969 + 3 ^ 40 * 2687819 * 2
def baseEnd_2687819 : Nat := 1380143059287124629501451

theorem tailTrace_2687819 : CollatzResearch.WordTrace tailWord_2687819 prefixEnd_2687819 1380143059287124629501451 := by
  unfold tailWord_2687819
  simp only [CollatzResearch.WordTrace]
  refine ⟨98032812649498280784034511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65355208432998853856023007 98032812649498280784034511)
  ·
    refine ⟨147049218974247421176051767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98032812649498280784034511 147049218974247421176051767)
    ·
      refine ⟨220573828461371131764077651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147049218974247421176051767 220573828461371131764077651)
      ·
        refine ⟨330860742692056697646116477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220573828461371131764077651 330860742692056697646116477)
        ·
          refine ⟨124072778509521261617293679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330860742692056697646116477 124072778509521261617293679)
          ·
            refine ⟨186109167764281892425940519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124072778509521261617293679 186109167764281892425940519)
            ·
              refine ⟨279163751646422838638910779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186109167764281892425940519 279163751646422838638910779)
              ·
                refine ⟨418745627469634257958366169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279163751646422838638910779 418745627469634257958366169)
                ·
                  refine ⟨314059220602225693468774627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418745627469634257958366169 314059220602225693468774627)
                  ·
                    refine ⟨471088830903338540203161941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314059220602225693468774627 471088830903338540203161941)
                    ·
                      refine ⟨1380143059287124629501451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 471088830903338540203161941 1380143059287124629501451)
                      ·
                        rfl

theorem cell23_2687819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_2687819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687819 prefixEnd_2687819 := by exact prefixLift 2687819
  have htrace : WordTrace (prefixWord ++ tailWord_2687819) baseStart_2687819 baseEnd_2687819 := by
    simpa [prefixWord, tailWord_2687819, baseEnd_2687819] using wordTrace_append hprefix tailTrace_2687819
  have hstable : (prefixWord ++ tailWord_2687819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687819).length < 2 ^ (prefixWord ++ tailWord_2687819).sum := by decide
  have hdescent : baseEnd_2687819 < baseStart_2687819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687820 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 6]
def baseStart_2687820 : Nat := 118140960795 + 2687820 * 2 ^ 59
def prefixEnd_2687820 : Nat := 4983230072969 + 3 ^ 40 * 2687820 * 2
def baseEnd_2687820 : Nat := 153349285863086569509883

theorem tailTrace_2687820 : CollatzResearch.WordTrace tailWord_2687820 prefixEnd_2687820 153349285863086569509883 := by
  unfold tailWord_2687820
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016424561247328977410457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65355232748329771969880609 49016424561247328977410457)
  ·
    refine ⟨36762318420935496733057843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49016424561247328977410457 36762318420935496733057843)
    ·
      refine ⟨55143477631403245099586765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36762318420935496733057843 55143477631403245099586765)
      ·
        refine ⟨20678804111776216912345037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55143477631403245099586765 20678804111776216912345037)
        ·
          refine ⟨7754551541916081342129389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20678804111776216912345037 7754551541916081342129389)
          ·
            refine ⟨2907956828218530503298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7754551541916081342129389 2907956828218530503298521)
            ·
              refine ⟨2180967621163897877473891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907956828218530503298521 2180967621163897877473891)
              ·
                refine ⟨3271451431745846816210837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180967621163897877473891 3271451431745846816210837)
                ·
                  refine ⟨153349285863086569509883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3271451431745846816210837 153349285863086569509883)
                  ·
                    rfl

theorem cell23_2687820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_2687820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687820 prefixEnd_2687820 := by exact prefixLift 2687820
  have htrace : WordTrace (prefixWord ++ tailWord_2687820) baseStart_2687820 baseEnd_2687820 := by
    simpa [prefixWord, tailWord_2687820, baseEnd_2687820] using wordTrace_append hprefix tailTrace_2687820
  have hstable : (prefixWord ++ tailWord_2687820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687820).length < 2 ^ (prefixWord ++ tailWord_2687820).sum := by decide
  have hdescent : baseEnd_2687820 < baseStart_2687820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687833 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 1, 5]
def baseStart_2687833 : Nat := 118140960795 + 2687833 * 2 ^ 59
def prefixEnd_2687833 : Nat := 4983230072969 + 3 ^ 40 * 2687833 * 2
def baseEnd_2687833 : Nat := 460050082672095858242129

theorem tailTrace_2687833 : CollatzResearch.WordTrace tailWord_2687833 prefixEnd_2687833 460050082672095858242129 := by
  unfold tailWord_2687833
  simp only [CollatzResearch.WordTrace]
  refine ⟨98033323271447561175044153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65355548847631707450029435 98033323271447561175044153)
  ·
    refine ⟨73524992453585670881283115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98033323271447561175044153 73524992453585670881283115)
    ·
      refine ⟨110287488680378506321924673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73524992453585670881283115 110287488680378506321924673)
      ·
        refine ⟨82715616510283879741443505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110287488680378506321924673 82715616510283879741443505)
        ·
          refine ⟨62036712382712909806082629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82715616510283879741443505 62036712382712909806082629)
          ·
            refine ⟨11631883571758670588640493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62036712382712909806082629 11631883571758670588640493)
            ·
              refine ⟨4361956339409501470740185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11631883571758670588640493 4361956339409501470740185)
              ·
                refine ⟨3271467254557126103055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361956339409501470740185 3271467254557126103055139)
                ·
                  refine ⟨4907200881835689154582709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271467254557126103055139 4907200881835689154582709)
                  ·
                    refine ⟨460050082672095858242129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4907200881835689154582709 460050082672095858242129)
                    ·
                      rfl

theorem cell23_2687833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_2687833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687833 prefixEnd_2687833 := by exact prefixLift 2687833
  have htrace : WordTrace (prefixWord ++ tailWord_2687833) baseStart_2687833 baseEnd_2687833 := by
    simpa [prefixWord, tailWord_2687833, baseEnd_2687833] using wordTrace_append hprefix tailTrace_2687833
  have hstable : (prefixWord ++ tailWord_2687833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687833).length < 2 ^ (prefixWord ++ tailWord_2687833).sum := by decide
  have hdescent : baseEnd_2687833 < baseStart_2687833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687840 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2]
def baseStart_2687840 : Nat := 118140960795 + 2687840 * 2 ^ 59
def prefixEnd_2687840 : Nat := 4983230072969 + 3 ^ 40 * 2687840 * 2
def baseEnd_2687840 : Nat := 1380153842380869047338855

theorem tailTrace_2687840 : CollatzResearch.WordTrace tailWord_2687840 prefixEnd_2687840 1380153842380869047338855 := by
  unfold tailWord_2687840
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016789291211100685274487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65355719054948134247032649 49016789291211100685274487)
  ·
    refine ⟨73525183936816651027911731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49016789291211100685274487 73525183936816651027911731)
    ·
      refine ⟨110287775905224976541867597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73525183936816651027911731 110287775905224976541867597)
      ·
        refine ⟨41357915964459366203200349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110287775905224976541867597 41357915964459366203200349)
        ·
          refine ⟨15509218486672262326200131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41357915964459366203200349 15509218486672262326200131)
          ·
            refine ⟨23263827730008393489300197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15509218486672262326200131 23263827730008393489300197)
            ·
              refine ⟨4361967699376573779243787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23263827730008393489300197 4361967699376573779243787)
              ·
                refine ⟨6542951549064860668865681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361967699376573779243787 6542951549064860668865681)
                ·
                  refine ⟨4907213661798645501649261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542951549064860668865681 4907213661798645501649261)
                  ·
                    refine ⟨1840205123174492063118473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4907213661798645501649261 1840205123174492063118473)
                    ·
                      refine ⟨1380153842380869047338855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840205123174492063118473 1380153842380869047338855)
                      ·
                        rfl

theorem cell23_2687840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_2687840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687840 prefixEnd_2687840 := by exact prefixLift 2687840
  have htrace : WordTrace (prefixWord ++ tailWord_2687840) baseStart_2687840 baseEnd_2687840 := by
    simpa [prefixWord, tailWord_2687840, baseEnd_2687840] using wordTrace_append hprefix tailTrace_2687840
  have hstable : (prefixWord ++ tailWord_2687840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687840).length < 2 ^ (prefixWord ++ tailWord_2687840).sum := by decide
  have hdescent : baseEnd_2687840 < baseStart_2687840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687866 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_2687866 : Nat := 118140960795 + 2687866 * 2 ^ 59
def prefixEnd_2687866 : Nat := 4983230072969 + 3 ^ 40 * 2687866 * 2
def baseEnd_2687866 : Nat := 1380167192877885945613735

theorem tailTrace_2687866 : CollatzResearch.WordTrace tailWord_2687866 prefixEnd_2687866 1380167192877885945613735 := by
  unfold tailWord_2687866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508631720082001952748863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65356351253552005207330301 24508631720082001952748863)
  ·
    refine ⟨36762947580123002929123295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24508631720082001952748863 36762947580123002929123295)
    ·
      refine ⟨55144421370184504393684943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36762947580123002929123295 55144421370184504393684943)
      ·
        refine ⟨82716632055276756590527415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55144421370184504393684943 82716632055276756590527415)
        ·
          refine ⟨124074948082915134885791123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82716632055276756590527415 124074948082915134885791123)
          ·
            refine ⟨186112422124372702328686685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124074948082915134885791123 186112422124372702328686685)
            ·
              refine ⟨69792158296639763373257507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186112422124372702328686685 69792158296639763373257507)
              ·
                refine ⟨104688237444959645059886261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69792158296639763373257507 104688237444959645059886261)
                ·
                  refine ⟨9814522260464966724364337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104688237444959645059886261 9814522260464966724364337)
                  ·
                    refine ⟨7360891695348725043273253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9814522260464966724364337 7360891695348725043273253)
                    ·
                      refine ⟨1380167192877885945613735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7360891695348725043273253 1380167192877885945613735)
                      ·
                        rfl

theorem cell23_2687866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_2687866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687866 prefixEnd_2687866 := by exact prefixLift 2687866
  have htrace : WordTrace (prefixWord ++ tailWord_2687866) baseStart_2687866 baseEnd_2687866 := by
    simpa [prefixWord, tailWord_2687866, baseEnd_2687866] using wordTrace_append hprefix tailTrace_2687866
  have hstable : (prefixWord ++ tailWord_2687866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687866).length < 2 ^ (prefixWord ++ tailWord_2687866).sum := by decide
  have hdescent : baseEnd_2687866 < baseStart_2687866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687880 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_2687880 : Nat := 118140960795 + 2687880 * 2 ^ 59
def prefixEnd_2687880 : Nat := 4983230072969 + 3 ^ 40 * 2687880 * 2
def baseEnd_2687880 : Nat := 460058127202349630279557

theorem tailTrace_2687880 : CollatzResearch.WordTrace tailWord_2687880 prefixEnd_2687880 460058127202349630279557 := by
  unfold tailWord_2687880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49017518751138644101002547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65356691668184858801336729 49017518751138644101002547)
  ·
    refine ⟨73526278126707966151503821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49017518751138644101002547 73526278126707966151503821)
    ·
      refine ⟨27572354297515487306813933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73526278126707966151503821 27572354297515487306813933)
      ·
        refine ⟨10339632861568307740055225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27572354297515487306813933 10339632861568307740055225)
        ·
          refine ⟨7754724646176230805041419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10339632861568307740055225 7754724646176230805041419)
          ·
            refine ⟨11632086969264346207562129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754724646176230805041419 11632086969264346207562129)
            ·
              refine ⟨8724065226948259655671597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11632086969264346207562129 8724065226948259655671597)
              ·
                refine ⟨3271524460105597370876849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8724065226948259655671597 3271524460105597370876849)
                ·
                  refine ⟨2453643345079198028157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271524460105597370876849 2453643345079198028157637)
                  ·
                    refine ⟨460058127202349630279557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453643345079198028157637 460058127202349630279557)
                    ·
                      rfl

theorem cell23_2687880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_2687880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687880 prefixEnd_2687880 := by exact prefixLift 2687880
  have htrace : WordTrace (prefixWord ++ tailWord_2687880) baseStart_2687880 baseEnd_2687880 := by
    simpa [prefixWord, tailWord_2687880, baseEnd_2687880] using wordTrace_append hprefix tailTrace_2687880
  have hstable : (prefixWord ++ tailWord_2687880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687880).length < 2 ^ (prefixWord ++ tailWord_2687880).sum := by decide
  have hdescent : baseEnd_2687880 < baseStart_2687880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687893 : List Nat := [1, 3, 2, 1, 1, 5, 3, 7]
def baseStart_2687893 : Nat := 118140960795 + 2687893 * 2 ^ 59
def prefixEnd_2687893 : Nat := 4983230072969 + 3 ^ 40 * 2687893 * 2
def baseEnd_2687893 : Nat := 51117816920576197776893

theorem tailTrace_2687893 : CollatzResearch.WordTrace tailWord_2687893 prefixEnd_2687893 51117816920576197776893 := by
  unfold tailWord_2687893
  simp only [CollatzResearch.WordTrace]
  refine ⟨98035511651230191422228333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65357007767486794281485555 98035511651230191422228333)
  ·
    refine ⟨36763316869211321783335625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98035511651230191422228333 36763316869211321783335625)
    ·
      refine ⟨27572487651908491337501719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36763316869211321783335625 27572487651908491337501719)
      ·
        refine ⟨41358731477862737006252579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27572487651908491337501719 41358731477862737006252579)
        ·
          refine ⟨62038097216794105509378869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41358731477862737006252579 62038097216794105509378869)
          ·
            refine ⟨5816071614074447391504269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62038097216794105509378869 5816071614074447391504269)
            ·
              refine ⟨2181026855277917771814101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5816071614074447391504269 2181026855277917771814101)
              ·
                refine ⟨51117816920576197776893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2181026855277917771814101 51117816920576197776893)
                ·
                  rfl

theorem cell23_2687893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 7].length) (baseStart_2687893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687893 prefixEnd_2687893 := by exact prefixLift 2687893
  have htrace : WordTrace (prefixWord ++ tailWord_2687893) baseStart_2687893 baseEnd_2687893 := by
    simpa [prefixWord, tailWord_2687893, baseEnd_2687893] using wordTrace_append hprefix tailTrace_2687893
  have hstable : (prefixWord ++ tailWord_2687893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687893).length < 2 ^ (prefixWord ++ tailWord_2687893).sum := by decide
  have hdescent : baseEnd_2687893 < baseStart_2687893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687916 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2687916 : Nat := 118140960795 + 2687916 * 2 ^ 59
def prefixEnd_2687916 : Nat := 4983230072969 + 3 ^ 40 * 2687916 * 2
def baseEnd_2687916 : Nat := 1380192866910610749988505

theorem tailTrace_2687916 : CollatzResearch.WordTrace tailWord_2687916 prefixEnd_2687916 1380192866910610749988505 := by
  unfold tailWord_2687916
  simp only [CollatzResearch.WordTrace]
  refine ⟨49018175265073433175157801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65357567020097910900210401 49018175265073433175157801)
  ·
    refine ⟨36763631448805074881368351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49018175265073433175157801 36763631448805074881368351)
    ·
      refine ⟨55145447173207612322052527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36763631448805074881368351 55145447173207612322052527)
      ·
        refine ⟨82718170759811418483078791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55145447173207612322052527 82718170759811418483078791)
        ·
          refine ⟨124077256139717127724618187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82718170759811418483078791 124077256139717127724618187)
          ·
            refine ⟨186115884209575691586927281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124077256139717127724618187 186115884209575691586927281)
            ·
              refine ⟨139586913157181768690195461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186115884209575691586927281 139586913157181768690195461)
              ·
                refine ⟨26172546216971581629411649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139586913157181768690195461 26172546216971581629411649)
                ·
                  refine ⟨19629409662728686222058737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26172546216971581629411649 19629409662728686222058737)
                  ·
                    refine ⟨14722057247046514666544053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19629409662728686222058737 14722057247046514666544053)
                    ·
                      refine ⟨1380192866910610749988505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14722057247046514666544053 1380192866910610749988505)
                      ·
                        rfl

theorem cell23_2687916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2687916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687916 prefixEnd_2687916 := by exact prefixLift 2687916
  have htrace : WordTrace (prefixWord ++ tailWord_2687916) baseStart_2687916 baseEnd_2687916 := by
    simpa [prefixWord, tailWord_2687916, baseEnd_2687916] using wordTrace_append hprefix tailTrace_2687916
  have hstable : (prefixWord ++ tailWord_2687916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687916).length < 2 ^ (prefixWord ++ tailWord_2687916).sum := by decide
  have hdescent : baseEnd_2687916 < baseStart_2687916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687947 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 1, 3, 2]
def baseStart_2687947 : Nat := 118140960795 + 2687947 * 2 ^ 59
def prefixEnd_2687947 : Nat := 4983230072969 + 3 ^ 40 * 2687947 * 2
def baseEnd_2687947 : Nat := 1380208784810900128700863

theorem tailTrace_2687947 : CollatzResearch.WordTrace tailWord_2687947 prefixEnd_2687947 1380208784810900128700863 := by
  unfold tailWord_2687947
  simp only [CollatzResearch.WordTrace]
  refine ⟨98037481193034558644694095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65358320795356372429796063 98037481193034558644694095)
  ·
    refine ⟨147056221789551837967041143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98037481193034558644694095 147056221789551837967041143)
    ·
      refine ⟨220584332684327756950561715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147056221789551837967041143 220584332684327756950561715)
      ·
        refine ⟨330876499026491635425842573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220584332684327756950561715 330876499026491635425842573)
        ·
          refine ⟨124078687134934363284690965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330876499026491635425842573 124078687134934363284690965)
          ·
            refine ⟨5816188459450048278969889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124078687134934363284690965 5816188459450048278969889)
            ·
              refine ⟨4362141344587536209227417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816188459450048278969889 4362141344587536209227417)
              ·
                refine ⟨3271606008440652156920563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4362141344587536209227417 3271606008440652156920563)
                ·
                  refine ⟨4907409012660978235380845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271606008440652156920563 4907409012660978235380845)
                  ·
                    refine ⟨1840278379747866838267817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4907409012660978235380845 1840278379747866838267817)
                    ·
                      refine ⟨1380208784810900128700863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840278379747866838267817 1380208784810900128700863)
                      ·
                        rfl

theorem cell23_2687947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 3, 2].length) (baseStart_2687947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687947 prefixEnd_2687947 := by exact prefixLift 2687947
  have htrace : WordTrace (prefixWord ++ tailWord_2687947) baseStart_2687947 baseEnd_2687947 := by
    simpa [prefixWord, tailWord_2687947, baseEnd_2687947] using wordTrace_append hprefix tailTrace_2687947
  have hstable : (prefixWord ++ tailWord_2687947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687947).length < 2 ^ (prefixWord ++ tailWord_2687947).sum := by decide
  have hdescent : baseEnd_2687947 < baseStart_2687947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687983 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 7]
def baseStart_2687983 : Nat := 118140960795 + 2687983 * 2 ^ 59
def prefixEnd_2687983 : Nat := 4983230072969 + 3 ^ 40 * 2687983 * 2
def baseEnd_2687983 : Nat := 153358585568273554205633

theorem tailTrace_2687983 : CollatzResearch.WordTrace tailWord_2687983 prefixEnd_2687983 153358585568273554205633 := by
  unfold tailWord_2687983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98038794220904136793004603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65359196147269424528669735 98038794220904136793004603)
  ·
    refine ⟨147058191331356205189506905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98038794220904136793004603 147058191331356205189506905)
    ·
      refine ⟨110293643498517153892130179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147058191331356205189506905 110293643498517153892130179)
      ·
        refine ⟨165440465247775730838195269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110293643498517153892130179 165440465247775730838195269)
        ·
          refine ⟨31020087233957949532161613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165440465247775730838195269 31020087233957949532161613)
          ·
            refine ⟨11632532712734231074560605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31020087233957949532161613 11632532712734231074560605)
            ·
              refine ⟨4362199767275336652960227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11632532712734231074560605 4362199767275336652960227)
              ·
                refine ⟨6543299650913004979440341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362199767275336652960227 6543299650913004979440341)
                ·
                  refine ⟨153358585568273554205633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6543299650913004979440341 153358585568273554205633)
                  ·
                    rfl

theorem cell23_2687983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 7].length) (baseStart_2687983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687983 prefixEnd_2687983 := by exact prefixLift 2687983
  have htrace : WordTrace (prefixWord ++ tailWord_2687983) baseStart_2687983 baseEnd_2687983 := by
    simpa [prefixWord, tailWord_2687983, baseEnd_2687983] using wordTrace_append hprefix tailTrace_2687983
  have hstable : (prefixWord ++ tailWord_2687983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687983).length < 2 ^ (prefixWord ++ tailWord_2687983).sum := by decide
  have hdescent : baseEnd_2687983 < baseStart_2687983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687993 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2687993 : Nat := 118140960795 + 2687993 * 2 ^ 59
def prefixEnd_2687993 : Nat := 4983230072969 + 3 ^ 40 * 2687993 * 2
def baseEnd_2687993 : Nat := 1380232404921006948725651

theorem tailTrace_2687993 : CollatzResearch.WordTrace tailWord_2687993 prefixEnd_2687993 1380232404921006948725651 := by
  unfold tailWord_2687993
  simp only [CollatzResearch.WordTrace]
  refine ⟨98039158950867908500868633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65359439300578605667245755 98039158950867908500868633)
  ·
    refine ⟨73529369213150931375651475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98039158950867908500868633 73529369213150931375651475)
    ·
      refine ⟨110294053819726397063477213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73529369213150931375651475 110294053819726397063477213)
      ·
        refine ⟨41360270182397398898803955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110294053819726397063477213 41360270182397398898803955)
        ·
          refine ⟨62040405273596098348205933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41360270182397398898803955 62040405273596098348205933)
          ·
            refine ⟨23265151977598536880577225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62040405273596098348205933 23265151977598536880577225)
            ·
              refine ⟨17448863983198902660432919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23265151977598536880577225 17448863983198902660432919)
              ·
                refine ⟨26173295974798353990649379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17448863983198902660432919 26173295974798353990649379)
                ·
                  refine ⟨39259943962197530985974069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26173295974798353990649379 39259943962197530985974069)
                  ·
                    refine ⟨3680619746456018529935069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39259943962197530985974069 3680619746456018529935069)
                    ·
                      refine ⟨1380232404921006948725651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680619746456018529935069 1380232404921006948725651)
                      ·
                        rfl

theorem cell23_2687993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2687993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687993 prefixEnd_2687993 := by exact prefixLift 2687993
  have htrace : WordTrace (prefixWord ++ tailWord_2687993) baseStart_2687993 baseEnd_2687993 := by
    simpa [prefixWord, tailWord_2687993, baseEnd_2687993] using wordTrace_append hprefix tailTrace_2687993
  have hstable : (prefixWord ++ tailWord_2687993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687993).length < 2 ^ (prefixWord ++ tailWord_2687993).sum := by decide
  have hdescent : baseEnd_2687993 < baseStart_2687993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687998 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2687998 : Nat := 118140960795 + 2687998 * 2 ^ 59
def prefixEnd_2687998 : Nat := 4983230072969 + 3 ^ 40 * 2687998 * 2
def baseEnd_2687998 : Nat := 1380234972324279429163129

theorem tailTrace_2687998 : CollatzResearch.WordTrace tailWord_2687998 prefixEnd_2687998 1380234972324279429163129 := by
  unfold tailWord_2687998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254917664481224294350081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65359560877233196236533765 12254917664481224294350081)
  ·
    refine ⟨9191188248360918220762561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254917664481224294350081 9191188248360918220762561)
    ·
      refine ⟨6893391186270688665571921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9191188248360918220762561 6893391186270688665571921)
      ·
        refine ⟨5170043389703016499178941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6893391186270688665571921 5170043389703016499178941)
        ·
          refine ⟨1938766271138631187192103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5170043389703016499178941 1938766271138631187192103)
          ·
            refine ⟨2908149406707946780788155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938766271138631187192103 2908149406707946780788155)
            ·
              refine ⟨4362224110061920171182233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908149406707946780788155 4362224110061920171182233)
              ·
                refine ⟨3271668082546440128386675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4362224110061920171182233 3271668082546440128386675)
                ·
                  refine ⟨4907502123819660192580013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271668082546440128386675 4907502123819660192580013)
                  ·
                    refine ⟨1840313296432372572217505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4907502123819660192580013 1840313296432372572217505)
                    ·
                      refine ⟨1380234972324279429163129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840313296432372572217505 1380234972324279429163129)
                      ·
                        rfl

theorem cell23_2687998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2687998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2687998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2687998 prefixEnd_2687998 := by exact prefixLift 2687998
  have htrace : WordTrace (prefixWord ++ tailWord_2687998) baseStart_2687998 baseEnd_2687998 := by
    simpa [prefixWord, tailWord_2687998, baseEnd_2687998] using wordTrace_append hprefix tailTrace_2687998
  have hstable : (prefixWord ++ tailWord_2687998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687998).length < 2 ^ (prefixWord ++ tailWord_2687998).sum := by decide
  have hdescent : baseEnd_2687998 < baseStart_2687998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688034 : List Nat := [3, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_2688034 : Nat := 118140960795 + 2688034 * 2 ^ 59
def prefixEnd_2688034 : Nat := 4983230072969 + 3 ^ 40 * 2688034 * 2
def baseEnd_2688034 : Nat := 153361495291982365368107

theorem tailTrace_2688034 : CollatzResearch.WordTrace tailWord_2688034 prefixEnd_2688034 153361495291982365368107 := by
  unfold tailWord_2688034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510163585929843125777789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65360436229146248335407437 24510163585929843125777789)
  ·
    refine ⟨9191311344723691172166671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24510163585929843125777789 9191311344723691172166671)
    ·
      refine ⟨13786967017085536758250007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191311344723691172166671 13786967017085536758250007)
      ·
        refine ⟨20680450525628305137375011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786967017085536758250007 20680450525628305137375011)
        ·
          refine ⟨31020675788442457706062517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20680450525628305137375011 31020675788442457706062517)
          ·
            refine ⟨2908188355166480409943361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31020675788442457706062517 2908188355166480409943361)
            ·
              refine ⟨2181141266374860307457521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908188355166480409943361 2181141266374860307457521)
              ·
                refine ⟨1635855949781145230593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181141266374860307457521 1635855949781145230593141)
                ·
                  refine ⟨153361495291982365368107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1635855949781145230593141 153361495291982365368107)
                  ·
                    rfl

theorem cell23_2688034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_2688034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688034 prefixEnd_2688034 := by exact prefixLift 2688034
  have htrace : WordTrace (prefixWord ++ tailWord_2688034) baseStart_2688034 baseEnd_2688034 := by
    simpa [prefixWord, tailWord_2688034, baseEnd_2688034] using wordTrace_append hprefix tailTrace_2688034
  have hstable : (prefixWord ++ tailWord_2688034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688034).length < 2 ^ (prefixWord ++ tailWord_2688034).sum := by decide
  have hdescent : baseEnd_2688034 < baseStart_2688034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688060 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_2688060 : Nat := 118140960795 + 2688060 * 2 ^ 59
def prefixEnd_2688060 : Nat := 4983230072969 + 3 ^ 40 * 2688060 * 2
def baseEnd_2688060 : Nat := 460088936041619395529281

theorem tailTrace_2688060 : CollatzResearch.WordTrace tailWord_2688060 prefixEnd_2688060 460088936041619395529281 := by
  unfold tailWord_2688060
  simp only [CollatzResearch.WordTrace]
  refine ⟨49020801320812589471778817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65361068427750119295705089 49020801320812589471778817)
  ·
    refine ⟨36765600990609442103834113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49020801320812589471778817 36765600990609442103834113)
    ·
      refine ⟨27574200742957081577875585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36765600990609442103834113 27574200742957081577875585)
      ·
        refine ⟨20680650557217811183406689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27574200742957081577875585 20680650557217811183406689)
        ·
          refine ⟨15510487917913358387555017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20680650557217811183406689 15510487917913358387555017)
          ·
            refine ⟨11632865938435018790666263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15510487917913358387555017 11632865938435018790666263)
            ·
              refine ⟨17449298907652528185999395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11632865938435018790666263 17449298907652528185999395)
              ·
                refine ⟨26173948361478792278999093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17449298907652528185999395 26173948361478792278999093)
                ·
                  refine ⟨2453807658888636776156165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26173948361478792278999093 2453807658888636776156165)
                  ·
                    refine ⟨460088936041619395529281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2453807658888636776156165 460088936041619395529281)
                    ·
                      rfl

theorem cell23_2688060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_2688060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688060 prefixEnd_2688060 := by exact prefixLift 2688060
  have htrace : WordTrace (prefixWord ++ tailWord_2688060) baseStart_2688060 baseEnd_2688060 := by
    simpa [prefixWord, tailWord_2688060, baseEnd_2688060] using wordTrace_append hprefix tailTrace_2688060
  have hstable : (prefixWord ++ tailWord_2688060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688060).length < 2 ^ (prefixWord ++ tailWord_2688060).sum := by decide
  have hdescent : baseEnd_2688060 < baseStart_2688060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688120 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_2688120 : Nat := 118140960795 + 2688120 * 2 ^ 59
def prefixEnd_2688120 : Nat := 4983230072969 + 3 ^ 40 * 2688120 * 2
def baseEnd_2688120 : Nat := 460099205654709317279189

theorem tailTrace_2688120 : CollatzResearch.WordTrace tailWord_2688120 prefixEnd_2688120 460099205654709317279189 := by
  unfold tailWord_2688120
  simp only [CollatzResearch.WordTrace]
  refine ⟨49021895510703904595370907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65362527347605206127161209 49021895510703904595370907)
  ·
    refine ⟨73532843266055856893056361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49021895510703904595370907 73532843266055856893056361)
    ·
      refine ⟨55149632449541892669792271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73532843266055856893056361 55149632449541892669792271)
      ·
        refine ⟨82724448674312839004688407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55149632449541892669792271 82724448674312839004688407)
        ·
          refine ⟨124086673011469258507032611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82724448674312839004688407 124086673011469258507032611)
          ·
            refine ⟨186130009517203887760548917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124086673011469258507032611 186130009517203887760548917)
            ·
              refine ⟨17449688392237864477551461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186130009517203887760548917 17449688392237864477551461)
              ·
                refine ⟨3271816573544599589540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17449688392237864477551461 3271816573544599589540899)
                ·
                  refine ⟨4907724860316899384311349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271816573544599589540899 4907724860316899384311349)
                  ·
                    refine ⟨460099205654709317279189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4907724860316899384311349 460099205654709317279189)
                    ·
                      rfl

theorem cell23_2688120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_2688120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688120 prefixEnd_2688120 := by exact prefixLift 2688120
  have htrace : WordTrace (prefixWord ++ tailWord_2688120) baseStart_2688120 baseEnd_2688120 := by
    simpa [prefixWord, tailWord_2688120, baseEnd_2688120] using wordTrace_append hprefix tailTrace_2688120
  have hstable : (prefixWord ++ tailWord_2688120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688120).length < 2 ^ (prefixWord ++ tailWord_2688120).sum := by decide
  have hdescent : baseEnd_2688120 < baseStart_2688120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688123 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_2688123 : Nat := 118140960795 + 2688123 * 2 ^ 59
def prefixEnd_2688123 : Nat := 4983230072969 + 3 ^ 40 * 2688123 * 2
def baseEnd_2688123 : Nat := 1380299157406091440100053

theorem tailTrace_2688123 : CollatzResearch.WordTrace tailWord_2688123 prefixEnd_2688123 1380299157406091440100053 := by
  unfold tailWord_2688123
  simp only [CollatzResearch.WordTrace]
  refine ⟨98043900440396940703101023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65362600293597960468734015 98043900440396940703101023)
  ·
    refine ⟨147065850660595411054651535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98043900440396940703101023 147065850660595411054651535)
    ·
      refine ⟨220598775990893116581977303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147065850660595411054651535 220598775990893116581977303)
      ·
        refine ⟨330898163986339674872965955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220598775990893116581977303 330898163986339674872965955)
        ·
          refine ⟨496347245979509512309448933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330898163986339674872965955 496347245979509512309448933)
          ·
            refine ⟨93065108621158033558021675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 496347245979509512309448933 93065108621158033558021675)
            ·
              refine ⟨139597662931737050337032513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93065108621158033558021675 139597662931737050337032513)
              ·
                refine ⟨104698247198802787752774385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139597662931737050337032513 104698247198802787752774385)
                ·
                  refine ⟨78523685399102090814580789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104698247198802787752774385 78523685399102090814580789)
                  ·
                    refine ⟨7361595506165821013866949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78523685399102090814580789 7361595506165821013866949)
                    ·
                      refine ⟨1380299157406091440100053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7361595506165821013866949 1380299157406091440100053)
                      ·
                        rfl

theorem cell23_2688123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_2688123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688123 prefixEnd_2688123 := by exact prefixLift 2688123
  have htrace : WordTrace (prefixWord ++ tailWord_2688123) baseStart_2688123 baseEnd_2688123 := by
    simpa [prefixWord, tailWord_2688123, baseEnd_2688123] using wordTrace_append hprefix tailTrace_2688123
  have hstable : (prefixWord ++ tailWord_2688123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688123).length < 2 ^ (prefixWord ++ tailWord_2688123).sum := by decide
  have hdescent : baseEnd_2688123 < baseStart_2688123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688160 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2688160 : Nat := 118140960795 + 2688160 * 2 ^ 59
def prefixEnd_2688160 : Nat := 4983230072969 + 3 ^ 40 * 2688160 * 2
def baseEnd_2688160 : Nat := 1380318156190307795337383

theorem tailTrace_2688160 : CollatzResearch.WordTrace tailWord_2688160 prefixEnd_2688160 1380318156190307795337383 := by
  unfold tailWord_2688160
  simp only [CollatzResearch.WordTrace]
  refine ⟨49022624970631448011098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65363499960841930681465289 49022624970631448011098967)
  ·
    refine ⟨73533937455947172016648451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49022624970631448011098967 73533937455947172016648451)
    ·
      refine ⟨110300906183920758024972677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73533937455947172016648451 110300906183920758024972677)
      ·
        refine ⟨20681419909485142129682377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110300906183920758024972677 20681419909485142129682377)
        ·
          refine ⟨15511064932113856597261783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20681419909485142129682377 15511064932113856597261783)
          ·
            refine ⟨23266597398170784895892675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511064932113856597261783 23266597398170784895892675)
            ·
              refine ⟨34899896097256177343839013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23266597398170784895892675 34899896097256177343839013)
              ·
                refine ⟨6543730518235533251969815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34899896097256177343839013 6543730518235533251969815)
                ·
                  refine ⟨9815595777353299877954723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543730518235533251969815 9815595777353299877954723)
                  ·
                    refine ⟨14723393666029949816932085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9815595777353299877954723 14723393666029949816932085)
                    ·
                      refine ⟨1380318156190307795337383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14723393666029949816932085 1380318156190307795337383)
                      ·
                        rfl

theorem cell23_2688160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2688160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688160 prefixEnd_2688160 := by exact prefixLift 2688160
  have htrace : WordTrace (prefixWord ++ tailWord_2688160) baseStart_2688160 baseEnd_2688160 := by
    simpa [prefixWord, tailWord_2688160, baseEnd_2688160] using wordTrace_append hprefix tailTrace_2688160
  have hstable : (prefixWord ++ tailWord_2688160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688160).length < 2 ^ (prefixWord ++ tailWord_2688160).sum := by decide
  have hdescent : baseEnd_2688160 < baseStart_2688160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688210 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_2688210 : Nat := 118140960795 + 2688210 * 2 ^ 59
def prefixEnd_2688210 : Nat := 4983230072969 + 3 ^ 40 * 2688210 * 2
def baseEnd_2688210 : Nat := 460114610074344199904051

theorem tailTrace_2688210 : CollatzResearch.WordTrace tailWord_2688210 prefixEnd_2688210 460114610074344199904051 := by
  unfold tailWord_2688210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24511768397770438640379521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65364715727387836374345389 24511768397770438640379521)
  ·
    refine ⟨18383826298327828980284641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24511768397770438640379521 18383826298327828980284641)
    ·
      refine ⟨13787869723745871735213481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18383826298327828980284641 13787869723745871735213481)
      ·
        refine ⟨10340902292809403801410111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13787869723745871735213481 10340902292809403801410111)
        ·
          refine ⟨15511353439214105702115167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10340902292809403801410111 15511353439214105702115167)
          ·
            refine ⟨23267030158821158553172751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511353439214105702115167 23267030158821158553172751)
            ·
              refine ⟨34900545238231737829759127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23267030158821158553172751 34900545238231737829759127)
              ·
                refine ⟨52350817857347606744638691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34900545238231737829759127 52350817857347606744638691)
                ·
                  refine ⟨78526226786021410116958037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52350817857347606744638691 78526226786021410116958037)
                  ·
                    refine ⟨460114610074344199904051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78526226786021410116958037 460114610074344199904051)
                    ·
                      rfl

theorem cell23_2688210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_2688210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688210 prefixEnd_2688210 := by exact prefixLift 2688210
  have htrace : WordTrace (prefixWord ++ tailWord_2688210) baseStart_2688210 baseEnd_2688210 := by
    simpa [prefixWord, tailWord_2688210, baseEnd_2688210] using wordTrace_append hprefix tailTrace_2688210
  have hstable : (prefixWord ++ tailWord_2688210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688210).length < 2 ^ (prefixWord ++ tailWord_2688210).sum := by decide
  have hdescent : baseEnd_2688210 < baseStart_2688210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688224 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_2688224 : Nat := 118140960795 + 2688224 * 2 ^ 59
def prefixEnd_2688224 : Nat := 4983230072969 + 3 ^ 40 * 2688224 * 2
def baseEnd_2688224 : Nat := 1380351018952195544937089

theorem tailTrace_2688224 : CollatzResearch.WordTrace tailWord_2688224 prefixEnd_2688224 1380351018952195544937089 := by
  unfold tailWord_2688224
  simp only [CollatzResearch.WordTrace]
  refine ⟨49023792106515517476263863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65365056142020689968351817 49023792106515517476263863)
  ·
    refine ⟨73535688159773276214395795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49023792106515517476263863 73535688159773276214395795)
    ·
      refine ⟨110303532239659914321593693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73535688159773276214395795 110303532239659914321593693)
      ·
        refine ⟨41363824589872467870597635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110303532239659914321593693 41363824589872467870597635)
        ·
          refine ⟨62045736884808701805896453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41363824589872467870597635 62045736884808701805896453)
          ·
            refine ⟨11633575665901631588605585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62045736884808701805896453 11633575665901631588605585)
            ·
              refine ⟨8725181749426223691454189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11633575665901631588605585 8725181749426223691454189)
              ·
                refine ⟨3271943156034833884295321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8725181749426223691454189 3271943156034833884295321)
                ·
                  refine ⟨2453957367026125413221491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271943156034833884295321 2453957367026125413221491)
                  ·
                    refine ⟨3680936050539188119832237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2453957367026125413221491 3680936050539188119832237)
                    ·
                      refine ⟨1380351018952195544937089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3680936050539188119832237 1380351018952195544937089)
                      ·
                        rfl

theorem cell23_2688224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_2688224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688224 prefixEnd_2688224 := by exact prefixLift 2688224
  have htrace : WordTrace (prefixWord ++ tailWord_2688224) baseStart_2688224 baseEnd_2688224 := by
    simpa [prefixWord, tailWord_2688224, baseEnd_2688224] using wordTrace_append hprefix tailTrace_2688224
  have hstable : (prefixWord ++ tailWord_2688224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688224).length < 2 ^ (prefixWord ++ tailWord_2688224).sum := by decide
  have hdescent : baseEnd_2688224 < baseStart_2688224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688234 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_2688234 : Nat := 118140960795 + 2688234 * 2 ^ 59
def prefixEnd_2688234 : Nat := 4983230072969 + 3 ^ 40 * 2688234 * 2
def baseEnd_2688234 : Nat := 1380356153758740505812043

theorem tailTrace_2688234 : CollatzResearch.WordTrace tailWord_2688234 prefixEnd_2688234 1380356153758740505812043 := by
  unfold tailWord_2688234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24511987235748701665097939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65365299295329871106927837 24511987235748701665097939)
  ·
    refine ⟨36767980853623052497646909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24511987235748701665097939 36767980853623052497646909)
    ·
      refine ⟨13787992820108644686617591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36767980853623052497646909 13787992820108644686617591)
      ·
        refine ⟨20681989230162967029926387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13787992820108644686617591 20681989230162967029926387)
        ·
          refine ⟨31022983845244450544889581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20681989230162967029926387 31022983845244450544889581)
          ·
            refine ⟨11633618941966668954333593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31022983845244450544889581 11633618941966668954333593)
            ·
              refine ⟨8725214206475001715750195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11633618941966668954333593 8725214206475001715750195)
              ·
                refine ⟨13087821309712502573625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8725214206475001715750195 13087821309712502573625293)
                ·
                  refine ⟨4907932991142188465109485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13087821309712502573625293 4907932991142188465109485)
                  ·
                    refine ⟨1840474871678320674416057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4907932991142188465109485 1840474871678320674416057)
                    ·
                      refine ⟨1380356153758740505812043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840474871678320674416057 1380356153758740505812043)
                      ·
                        rfl

theorem cell23_2688234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_2688234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688234 prefixEnd_2688234 := by exact prefixLift 2688234
  have htrace : WordTrace (prefixWord ++ tailWord_2688234) baseStart_2688234 baseEnd_2688234 := by
    simpa [prefixWord, tailWord_2688234, baseEnd_2688234] using wordTrace_append hprefix tailTrace_2688234
  have hstable : (prefixWord ++ tailWord_2688234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688234).length < 2 ^ (prefixWord ++ tailWord_2688234).sum := by decide
  have hdescent : baseEnd_2688234 < baseStart_2688234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688250 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_2688250 : Nat := 118140960795 + 2688250 * 2 ^ 59
def prefixEnd_2688250 : Nat := 4983230072969 + 3 ^ 40 * 2688250 * 2
def baseEnd_2688250 : Nat := 1380364369449212443211969

theorem tailTrace_2688250 : CollatzResearch.WordTrace tailWord_2688250 prefixEnd_2688250 1380364369449212443211969 := by
  unfold tailWord_2688250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24512133127734210348243551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65365688340624560928649469 24512133127734210348243551)
  ·
    refine ⟨36768199691601315522365327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24512133127734210348243551 36768199691601315522365327)
    ·
      refine ⟨55152299537401973283547991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36768199691601315522365327 55152299537401973283547991)
      ·
        refine ⟨82728449306102959925321987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55152299537401973283547991 82728449306102959925321987)
        ·
          refine ⟨124092673959154439887982981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82728449306102959925321987 124092673959154439887982981)
          ·
            refine ⟨23267376367341457478996809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124092673959154439887982981 23267376367341457478996809)
            ·
              refine ⟨17450532275506093109247607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23267376367341457478996809 17450532275506093109247607)
              ·
                refine ⟨26175798413259139663871411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17450532275506093109247607 26175798413259139663871411)
                ·
                  refine ⟨39263697619888709495807117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26175798413259139663871411 39263697619888709495807117)
                  ·
                    refine ⟨14723886607458266060927669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39263697619888709495807117 14723886607458266060927669)
                    ·
                      refine ⟨1380364369449212443211969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14723886607458266060927669 1380364369449212443211969)
                      ·
                        rfl

theorem cell23_2688250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_2688250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688250 prefixEnd_2688250 := by exact prefixLift 2688250
  have htrace : WordTrace (prefixWord ++ tailWord_2688250) baseStart_2688250 baseEnd_2688250 := by
    simpa [prefixWord, tailWord_2688250, baseEnd_2688250] using wordTrace_append hprefix tailTrace_2688250
  have hstable : (prefixWord ++ tailWord_2688250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688250).length < 2 ^ (prefixWord ++ tailWord_2688250).sum := by decide
  have hdescent : baseEnd_2688250 < baseStart_2688250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688327 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2688327 : Nat := 118140960795 + 2688327 * 2 ^ 59
def prefixEnd_2688327 : Nat := 4983230072969 + 3 ^ 40 * 2688327 * 2
def baseEnd_2688327 : Nat := 1380403907459608641949115

theorem tailTrace_2688327 : CollatzResearch.WordTrace tailWord_2688327 prefixEnd_2688327 1380403907459608641949115 := by
  unfold tailWord_2688327
  simp only [CollatzResearch.WordTrace]
  refine ⟨98051340931657883543527235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65367560621105255695684823 98051340931657883543527235)
  ·
    refine ⟨147077011397486825315290853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98051340931657883543527235 147077011397486825315290853)
    ·
      refine ⟨27576939637028779746617035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147077011397486825315290853 27576939637028779746617035)
      ·
        refine ⟨41365409455543169619925553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27576939637028779746617035 41365409455543169619925553)
        ·
          refine ⟨31024057091657377214944165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41365409455543169619925553 31024057091657377214944165)
          ·
            refine ⟨5817010704685758227802031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31024057091657377214944165 5817010704685758227802031)
            ·
              refine ⟨8725516057028637341703047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5817010704685758227802031 8725516057028637341703047)
              ·
                refine ⟨13088274085542956012554571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8725516057028637341703047 13088274085542956012554571)
                ·
                  refine ⟨19632411128314434018831857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13088274085542956012554571 19632411128314434018831857)
                  ·
                    refine ⟨14724308346235825514123893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19632411128314434018831857 14724308346235825514123893)
                    ·
                      refine ⟨1380403907459608641949115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14724308346235825514123893 1380403907459608641949115)
                      ·
                        rfl

theorem cell23_2688327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2688327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688327 prefixEnd_2688327 := by exact prefixLift 2688327
  have htrace : WordTrace (prefixWord ++ tailWord_2688327) baseStart_2688327 baseEnd_2688327 := by
    simpa [prefixWord, tailWord_2688327, baseEnd_2688327] using wordTrace_append hprefix tailTrace_2688327
  have hstable : (prefixWord ++ tailWord_2688327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688327).length < 2 ^ (prefixWord ++ tailWord_2688327).sum := by decide
  have hdescent : baseEnd_2688327 < baseStart_2688327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688337 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2688337 : Nat := 118140960795 + 2688337 * 2 ^ 59
def prefixEnd_2688337 : Nat := 4983230072969 + 3 ^ 40 * 2688337 * 2
def baseEnd_2688337 : Nat := 1380409042266153602824069

theorem tailTrace_2688337 : CollatzResearch.WordTrace tailWord_2688337 prefixEnd_2688337 1380409042266153602824069 := by
  unfold tailWord_2688337
  simp only [CollatzResearch.WordTrace]
  refine ⟨98051705661621655251391265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65367803774414436834260843 98051705661621655251391265)
  ·
    refine ⟨73538779246216241438543449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98051705661621655251391265 73538779246216241438543449)
    ·
      refine ⟨55154084434662181078907587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73538779246216241438543449 55154084434662181078907587)
      ·
        refine ⟨82731126651993271618361381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55154084434662181078907587 82731126651993271618361381)
        ·
          refine ⟨15512086247248738428442759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82731126651993271618361381 15512086247248738428442759)
          ·
            refine ⟨23268129370873107642664139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15512086247248738428442759 23268129370873107642664139)
            ·
              refine ⟨34902194056309661463996209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23268129370873107642664139 34902194056309661463996209)
              ·
                refine ⟨26176645542232246097997157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34902194056309661463996209 26176645542232246097997157)
                ·
                  refine ⟨4908121039168546143374467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26176645542232246097997157 4908121039168546143374467)
                  ·
                    refine ⟨7362181558752819215061701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4908121039168546143374467 7362181558752819215061701)
                    ·
                      refine ⟨1380409042266153602824069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7362181558752819215061701 1380409042266153602824069)
                      ·
                        rfl

theorem cell23_2688337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2688337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688337 prefixEnd_2688337 := by exact prefixLift 2688337
  have htrace : WordTrace (prefixWord ++ tailWord_2688337) baseStart_2688337 baseEnd_2688337 := by
    simpa [prefixWord, tailWord_2688337, baseEnd_2688337] using wordTrace_append hprefix tailTrace_2688337
  have hstable : (prefixWord ++ tailWord_2688337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688337).length < 2 ^ (prefixWord ++ tailWord_2688337).sum := by decide
  have hdescent : baseEnd_2688337 < baseStart_2688337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688377 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 6]
def baseStart_2688377 : Nat := 118140960795 + 2688377 * 2 ^ 59
def prefixEnd_2688377 : Nat := 4983230072969 + 3 ^ 40 * 2688377 * 2
def baseEnd_2688377 : Nat := 153381064610259271813765

theorem tailTrace_2688377 : CollatzResearch.WordTrace tailWord_2688377 prefixEnd_2688377 153381064610259271813765 := by
  unfold tailWord_2688377
  simp only [CollatzResearch.WordTrace]
  refine ⟨98053164581476742082847385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65368776387651161388564923 98053164581476742082847385)
  ·
    refine ⟨73539873436107556562135539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98053164581476742082847385 73539873436107556562135539)
    ·
      refine ⟨110309810154161334843203309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73539873436107556562135539 110309810154161334843203309)
      ·
        refine ⟨41366178807810500566201241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110309810154161334843203309 41366178807810500566201241)
        ·
          refine ⟨31024634105857875424650931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41366178807810500566201241 31024634105857875424650931)
          ·
            refine ⟨46536951158786813136976397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31024634105857875424650931 46536951158786813136976397)
            ·
              refine ⟨17451356684545054926366149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46536951158786813136976397 17451356684545054926366149)
              ·
                refine ⟨3272129378352197798693653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17451356684545054926366149 3272129378352197798693653)
                ·
                  refine ⟨153381064610259271813765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3272129378352197798693653 153381064610259271813765)
                  ·
                    rfl

theorem cell23_2688377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 6].length) (baseStart_2688377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688377 prefixEnd_2688377 := by exact prefixLift 2688377
  have htrace : WordTrace (prefixWord ++ tailWord_2688377) baseStart_2688377 baseEnd_2688377 := by
    simpa [prefixWord, tailWord_2688377, baseEnd_2688377] using wordTrace_append hprefix tailTrace_2688377
  have hstable : (prefixWord ++ tailWord_2688377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688377).length < 2 ^ (prefixWord ++ tailWord_2688377).sum := by decide
  have hdescent : baseEnd_2688377 < baseStart_2688377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688381 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2688381 : Nat := 118140960795 + 2688381 * 2 ^ 59
def prefixEnd_2688381 : Nat := 4983230072969 + 3 ^ 40 * 2688381 * 2
def baseEnd_2688381 : Nat := 460143878471650476891289

theorem tailTrace_2688381 : CollatzResearch.WordTrace tailWord_2688381 prefixEnd_2688381 460143878471650476891289 := by
  unfold tailWord_2688381
  simp only [CollatzResearch.WordTrace]
  refine ⟨98053310473462250765992997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65368873648974833843995331 98053310473462250765992997)
  ·
    refine ⟨18384995713774172018623687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98053310473462250765992997 18384995713774172018623687)
    ·
      refine ⟨27577493570661258027935531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18384995713774172018623687 27577493570661258027935531)
      ·
        refine ⟨41366240355991887041903297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27577493570661258027935531 41366240355991887041903297)
        ·
          refine ⟨31024680266993915281427473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41366240355991887041903297 31024680266993915281427473)
          ·
            refine ⟨23268510200245436461070605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31024680266993915281427473 23268510200245436461070605)
            ·
              refine ⟨8725691325092038672901477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23268510200245436461070605 8725691325092038672901477)
              ·
                refine ⟨1636067123454757251169027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8725691325092038672901477 1636067123454757251169027)
                ·
                  refine ⟨2454100685182135876753541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636067123454757251169027 2454100685182135876753541)
                  ·
                    refine ⟨460143878471650476891289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454100685182135876753541 460143878471650476891289)
                    ·
                      rfl

theorem cell23_2688381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2688381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688381 prefixEnd_2688381 := by exact prefixLift 2688381
  have htrace : WordTrace (prefixWord ++ tailWord_2688381) baseStart_2688381 baseEnd_2688381 := by
    simpa [prefixWord, tailWord_2688381, baseEnd_2688381] using wordTrace_append hprefix tailTrace_2688381
  have hstable : (prefixWord ++ tailWord_2688381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688381).length < 2 ^ (prefixWord ++ tailWord_2688381).sum := by decide
  have hdescent : baseEnd_2688381 < baseStart_2688381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688408 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2688408 : Nat := 118140960795 + 2688408 * 2 ^ 59
def prefixEnd_2688408 : Nat := 4983230072969 + 3 ^ 40 * 2688408 * 2
def baseEnd_2688408 : Nat := 1380445499392622825036243

theorem tailTrace_2688408 : CollatzResearch.WordTrace tailWord_2688408 prefixEnd_2688408 1380445499392622825036243 := by
  unfold tailWord_2688408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49027147622182217188612939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65369530162909622918150585 49027147622182217188612939)
  ·
    refine ⟨73540721433273325782919409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49027147622182217188612939 73540721433273325782919409)
    ·
      refine ⟨55155541074954994337189557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73540721433273325782919409 55155541074954994337189557)
      ·
        refine ⟨5170831975777030719111521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55155541074954994337189557 5170831975777030719111521)
        ·
          refine ⟨3878123981832773039333641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170831975777030719111521 3878123981832773039333641)
          ·
            refine ⟨2908592986374579779500231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3878123981832773039333641 2908592986374579779500231)
            ·
              refine ⟨4362889479561869669250347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908592986374579779500231 4362889479561869669250347)
              ·
                refine ⟨6544334219342804503875521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362889479561869669250347 6544334219342804503875521)
                ·
                  refine ⟨4908250664507103377906641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544334219342804503875521 4908250664507103377906641)
                  ·
                    refine ⟨3681187998380327533429981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908250664507103377906641 3681187998380327533429981)
                    ·
                      refine ⟨1380445499392622825036243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3681187998380327533429981 1380445499392622825036243)
                      ·
                        rfl

theorem cell23_2688408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2688408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688408 prefixEnd_2688408 := by exact prefixLift 2688408
  have htrace : WordTrace (prefixWord ++ tailWord_2688408) baseStart_2688408 baseEnd_2688408 := by
    simpa [prefixWord, tailWord_2688408, baseEnd_2688408] using wordTrace_append hprefix tailTrace_2688408
  have hstable : (prefixWord ++ tailWord_2688408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688408).length < 2 ^ (prefixWord ++ tailWord_2688408).sum := by decide
  have hdescent : baseEnd_2688408 < baseStart_2688408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688481 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2688481 : Nat := 118140960795 + 2688481 * 2 ^ 59
def prefixEnd_2688481 : Nat := 4983230072969 + 3 ^ 40 * 2688481 * 2
def baseEnd_2688481 : Nat := 1380482983480401039423407

theorem tailTrace_2688481 : CollatzResearch.WordTrace tailWord_2688481 prefixEnd_2688481 1380482983480401039423407 := by
  unfold tailWord_2688481
  simp only [CollatzResearch.WordTrace]
  refine ⟨98056957773099967844633297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65371305182066645229755531 98056957773099967844633297)
  ·
    refine ⟨73542718329824975883474973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98056957773099967844633297 73542718329824975883474973)
    ·
      refine ⟨27578519373684365956303115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73542718329824975883474973 27578519373684365956303115)
      ·
        refine ⟨41367779060526548934454673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27578519373684365956303115 41367779060526548934454673)
        ·
          refine ⟨31025834295394911700841005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41367779060526548934454673 31025834295394911700841005)
          ·
            refine ⟨11634687860773091887815377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31025834295394911700841005 11634687860773091887815377)
            ·
              refine ⟨8726015895579818915861533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11634687860773091887815377 8726015895579818915861533)
              ·
                refine ⟨3272255960842432093448075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8726015895579818915861533 3272255960842432093448075)
                ·
                  refine ⟨4908383941263648140172113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272255960842432093448075 4908383941263648140172113)
                  ·
                    refine ⟨3681287955947736105129085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908383941263648140172113 3681287955947736105129085)
                    ·
                      refine ⟨1380482983480401039423407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3681287955947736105129085 1380482983480401039423407)
                      ·
                        rfl

theorem cell23_2688481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2688481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688481 prefixEnd_2688481 := by exact prefixLift 2688481
  have htrace : WordTrace (prefixWord ++ tailWord_2688481) baseStart_2688481 baseEnd_2688481 := by
    simpa [prefixWord, tailWord_2688481, baseEnd_2688481] using wordTrace_append hprefix tailTrace_2688481
  have hstable : (prefixWord ++ tailWord_2688481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688481).length < 2 ^ (prefixWord ++ tailWord_2688481).sum := by decide
  have hdescent : baseEnd_2688481 < baseStart_2688481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688501 : List Nat := [1, 3, 5, 1, 1, 2, 2, 8]
def baseStart_2688501 : Nat := 118140960795 + 2688501 * 2 ^ 59
def prefixEnd_2688501 : Nat := 4983230072969 + 3 ^ 40 * 2688501 * 2
def baseEnd_2688501 : Nat := 51129379744203368932345

theorem tailTrace_2688501 : CollatzResearch.WordTrace tailWord_2688501 prefixEnd_2688501 51129379744203368932345 := by
  unfold tailWord_2688501
  simp only [CollatzResearch.WordTrace]
  refine ⟨98057687233027511260361357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65371791488685007506907571 98057687233027511260361357)
  ·
    refine ⟨36771632712385316722635509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98057687233027511260361357 36771632712385316722635509)
    ·
      refine ⟨3447340566786123442747079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36771632712385316722635509 3447340566786123442747079)
      ·
        refine ⟨5171010850179185164120619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447340566786123442747079 5171010850179185164120619)
        ·
          refine ⟨7756516275268777746180929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5171010850179185164120619 7756516275268777746180929)
          ·
            refine ⟨5817387206451583309635697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7756516275268777746180929 5817387206451583309635697)
            ·
              refine ⟨4363040404838687482226773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817387206451583309635697 4363040404838687482226773)
              ·
                refine ⟨51129379744203368932345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4363040404838687482226773 51129379744203368932345)
                ·
                  rfl

theorem cell23_2688501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 8].length) (baseStart_2688501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688501 prefixEnd_2688501 := by exact prefixLift 2688501
  have htrace : WordTrace (prefixWord ++ tailWord_2688501) baseStart_2688501 baseEnd_2688501 := by
    simpa [prefixWord, tailWord_2688501, baseEnd_2688501] using wordTrace_append hprefix tailTrace_2688501
  have hstable : (prefixWord ++ tailWord_2688501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688501).length < 2 ^ (prefixWord ++ tailWord_2688501).sum := by decide
  have hdescent : baseEnd_2688501 < baseStart_2688501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688507 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_2688507 : Nat := 118140960795 + 2688507 * 2 ^ 59
def prefixEnd_2688507 : Nat := 4983230072969 + 3 ^ 40 * 2688507 * 2
def baseEnd_2688507 : Nat := 1380496333977417937698287

theorem tailTrace_2688507 : CollatzResearch.WordTrace tailWord_2688507 prefixEnd_2688507 1380496333977417937698287 := by
  unfold tailWord_2688507
  simp only [CollatzResearch.WordTrace]
  refine ⟨98057906071005774285079775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65371937380670516190053183 98057906071005774285079775)
  ·
    refine ⟨147086859106508661427619663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98057906071005774285079775 147086859106508661427619663)
    ·
      refine ⟨220630288659762992141429495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147086859106508661427619663 220630288659762992141429495)
      ·
        refine ⟨330945432989644488212144243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220630288659762992141429495 330945432989644488212144243)
        ·
          refine ⟨496418149484466732318216365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330945432989644488212144243 496418149484466732318216365)
          ·
            refine ⟨186156806056675024619331137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496418149484466732318216365 186156806056675024619331137)
            ·
              refine ⟨139617604542506268464498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186156806056675024619331137 139617604542506268464498353)
              ·
                refine ⟨104713203406879701348373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139617604542506268464498353 104713203406879701348373765)
                ·
                  refine ⟨19633725638789944002820081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104713203406879701348373765 19633725638789944002820081)
                  ·
                    refine ⟨14725294229092458002115061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19633725638789944002820081 14725294229092458002115061)
                    ·
                      refine ⟨1380496333977417937698287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14725294229092458002115061 1380496333977417937698287)
                      ·
                        rfl

theorem cell23_2688507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_2688507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688507 prefixEnd_2688507 := by exact prefixLift 2688507
  have htrace : WordTrace (prefixWord ++ tailWord_2688507) baseStart_2688507 baseEnd_2688507 := by
    simpa [prefixWord, tailWord_2688507, baseEnd_2688507] using wordTrace_append hprefix tailTrace_2688507
  have hstable : (prefixWord ++ tailWord_2688507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688507).length < 2 ^ (prefixWord ++ tailWord_2688507).sum := by decide
  have hdescent : baseEnd_2688507 < baseStart_2688507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688517 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_2688517 : Nat := 118140960795 + 2688517 * 2 ^ 59
def prefixEnd_2688517 : Nat := 4983230072969 + 3 ^ 40 * 2688517 * 2
def baseEnd_2688517 : Nat := 1380501468783962898573241

theorem tailTrace_2688517 : CollatzResearch.WordTrace tailWord_2688517 prefixEnd_2688517 1380501468783962898573241 := by
  unfold tailWord_2688517
  simp only [CollatzResearch.WordTrace]
  refine ⟨98058270800969545992943805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65372180533979697328629203 98058270800969545992943805)
  ·
    refine ⟨36771851550363579747353927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98058270800969545992943805 36771851550363579747353927)
    ·
      refine ⟨55157777325545369621030891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36771851550363579747353927 55157777325545369621030891)
      ·
        refine ⟨82736665988318054431546337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55157777325545369621030891 82736665988318054431546337)
        ·
          refine ⟨62052499491238540823659753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82736665988318054431546337 62052499491238540823659753)
          ·
            refine ⟨46539374618428905617744815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62052499491238540823659753 46539374618428905617744815)
            ·
              refine ⟨69809061927643358426617223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46539374618428905617744815 69809061927643358426617223)
              ·
                refine ⟨104713592891465037639925835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69809061927643358426617223 104713592891465037639925835)
                ·
                  refine ⟨157070389337197556459888753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104713592891465037639925835 157070389337197556459888753)
                  ·
                    refine ⟨117802792002898167344916565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157070389337197556459888753 117802792002898167344916565)
                    ·
                      refine ⟨1380501468783962898573241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117802792002898167344916565 1380501468783962898573241)
                      ·
                        rfl

theorem cell23_2688517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_2688517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688517 prefixEnd_2688517 := by exact prefixLift 2688517
  have htrace : WordTrace (prefixWord ++ tailWord_2688517) baseStart_2688517 baseEnd_2688517 := by
    simpa [prefixWord, tailWord_2688517, baseEnd_2688517] using wordTrace_append hprefix tailTrace_2688517
  have hstable : (prefixWord ++ tailWord_2688517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688517).length < 2 ^ (prefixWord ++ tailWord_2688517).sum := by decide
  have hdescent : baseEnd_2688517 < baseStart_2688517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688521 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 3, 3, 2]
def baseStart_2688521 : Nat := 118140960795 + 2688521 * 2 ^ 59
def prefixEnd_2688521 : Nat := 4983230072969 + 3 ^ 40 * 2688521 * 2
def baseEnd_2688521 : Nat := 1380503522706580882923223

theorem tailTrace_2688521 : CollatzResearch.WordTrace tailWord_2688521 prefixEnd_2688521 1380503522706580882923223 := by
  unfold tailWord_2688521
  simp only [CollatzResearch.WordTrace]
  refine ⟨98058416692955054676089417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65372277795303369784059611 98058416692955054676089417)
  ·
    refine ⟨73543812519716291007067063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98058416692955054676089417 73543812519716291007067063)
    ·
      refine ⟨110315718779574436510600595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73543812519716291007067063 110315718779574436510600595)
      ·
        refine ⟨165473578169361654765900893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110315718779574436510600595 165473578169361654765900893)
        ·
          refine ⟨62052591813510620537212835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165473578169361654765900893 62052591813510620537212835)
          ·
            refine ⟨93078887720265930805819253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62052591813510620537212835 93078887720265930805819253)
            ·
              refine ⟨8726145723774931013045555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93078887720265930805819253 8726145723774931013045555)
              ·
                refine ⟨13089218585662396519568333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726145723774931013045555 13089218585662396519568333)
                ·
                  refine ⟨4908456969623398694838125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13089218585662396519568333 4908456969623398694838125)
                  ·
                    refine ⟨1840671363608774510564297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4908456969623398694838125 1840671363608774510564297)
                    ·
                      refine ⟨1380503522706580882923223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840671363608774510564297 1380503522706580882923223)
                      ·
                        rfl

theorem cell23_2688521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 3, 2].length) (baseStart_2688521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688521 prefixEnd_2688521 := by exact prefixLift 2688521
  have htrace : WordTrace (prefixWord ++ tailWord_2688521) baseStart_2688521 baseEnd_2688521 := by
    simpa [prefixWord, tailWord_2688521, baseEnd_2688521] using wordTrace_append hprefix tailTrace_2688521
  have hstable : (prefixWord ++ tailWord_2688521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688521).length < 2 ^ (prefixWord ++ tailWord_2688521).sum := by decide
  have hdescent : baseEnd_2688521 < baseStart_2688521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688525 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2688525 : Nat := 118140960795 + 2688525 * 2 ^ 59
def prefixEnd_2688525 : Nat := 4983230072969 + 3 ^ 40 * 2688525 * 2
def baseEnd_2688525 : Nat := 1380505576629198867273205

theorem tailTrace_2688525 : CollatzResearch.WordTrace tailWord_2688525 prefixEnd_2688525 1380505576629198867273205 := by
  unfold tailWord_2688525
  simp only [CollatzResearch.WordTrace]
  refine ⟨98058562584940563359235029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65372375056627042239490019 98058562584940563359235029)
  ·
    refine ⟨2298247560584544453732071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 98058562584940563359235029 2298247560584544453732071)
    ·
      refine ⟨3447371340876816680598107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298247560584544453732071 3447371340876816680598107)
      ·
        refine ⟨5171057011315225020897161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447371340876816680598107 5171057011315225020897161)
        ·
          refine ⟨3878292758486418765672871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171057011315225020897161 3878292758486418765672871)
          ·
            refine ⟨5817439137729628148509307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878292758486418765672871 5817439137729628148509307)
            ·
              refine ⟨8726158706594442222763961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5817439137729628148509307 8726158706594442222763961)
              ·
                refine ⟨6544619029945831667072971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8726158706594442222763961 6544619029945831667072971)
                ·
                  refine ⟨9816928544918747500609457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544619029945831667072971 9816928544918747500609457)
                  ·
                    refine ⟨7362696408689060625457093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9816928544918747500609457 7362696408689060625457093)
                    ·
                      refine ⟨1380505576629198867273205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7362696408689060625457093 1380505576629198867273205)
                      ·
                        rfl

theorem cell23_2688525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2688525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688525 prefixEnd_2688525 := by exact prefixLift 2688525
  have htrace : WordTrace (prefixWord ++ tailWord_2688525) baseStart_2688525 baseEnd_2688525 := by
    simpa [prefixWord, tailWord_2688525, baseEnd_2688525] using wordTrace_append hprefix tailTrace_2688525
  have hstable : (prefixWord ++ tailWord_2688525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688525).length < 2 ^ (prefixWord ++ tailWord_2688525).sum := by decide
  have hdescent : baseEnd_2688525 < baseStart_2688525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688532 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2688532 : Nat := 118140960795 + 2688532 * 2 ^ 59
def prefixEnd_2688532 : Nat := 4983230072969 + 3 ^ 40 * 2688532 * 2
def baseEnd_2688532 : Nat := 1380509170993780339885673

theorem tailTrace_2688532 : CollatzResearch.WordTrace tailWord_2688532 prefixEnd_2688532 1380509170993780339885673 := by
  unfold tailWord_2688532
  simp only [CollatzResearch.WordTrace]
  refine ⟨49029408947957601777369925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65372545263943469036493233 49029408947957601777369925)
  ·
    refine ⟨9193014177742050333256861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49029408947957601777369925 9193014177742050333256861)
    ·
      refine ⟨3447380316653268874971323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9193014177742050333256861 3447380316653268874971323)
      ·
        refine ⟨5171070474979903312456985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447380316653268874971323 5171070474979903312456985)
        ·
          refine ⟨3878302856234927484342739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171070474979903312456985 3878302856234927484342739)
          ·
            refine ⟨5817454284352391226514109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878302856234927484342739 5817454284352391226514109)
            ·
              refine ⟨2181545356632146709942791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5817454284352391226514109 2181545356632146709942791)
              ·
                refine ⟨3272318034948220064914187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181545356632146709942791 3272318034948220064914187)
                ·
                  refine ⟨4908477052422330097371281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272318034948220064914187 4908477052422330097371281)
                  ·
                    refine ⟨3681357789316747573028461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908477052422330097371281 3681357789316747573028461)
                    ·
                      refine ⟨1380509170993780339885673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3681357789316747573028461 1380509170993780339885673)
                      ·
                        rfl

theorem cell23_2688532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2688532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688532 prefixEnd_2688532 := by exact prefixLift 2688532
  have htrace : WordTrace (prefixWord ++ tailWord_2688532) baseStart_2688532 baseEnd_2688532 := by
    simpa [prefixWord, tailWord_2688532, baseEnd_2688532] using wordTrace_append hprefix tailTrace_2688532
  have hstable : (prefixWord ++ tailWord_2688532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688532).length < 2 ^ (prefixWord ++ tailWord_2688532).sum := by decide
  have hdescent : baseEnd_2688532 < baseStart_2688532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688568 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_2688568 : Nat := 118140960795 + 2688568 * 2 ^ 59
def prefixEnd_2688568 : Nat := 4983230072969 + 3 ^ 40 * 2688568 * 2
def baseEnd_2688568 : Nat := 1380527656297342199035507

theorem tailTrace_2688568 : CollatzResearch.WordTrace tailWord_2688568 prefixEnd_2688568 1380527656297342199035507 := by
  unfold tailWord_2688568
  simp only [CollatzResearch.WordTrace]
  refine ⟨49030065461892390851525179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65373420615856521135366905 49030065461892390851525179)
  ·
    refine ⟨73545098192838586277287769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49030065461892390851525179 73545098192838586277287769)
    ·
      refine ⟨55158823644628939707965827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73545098192838586277287769 55158823644628939707965827)
      ·
        refine ⟨82738235466943409561948741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55158823644628939707965827 82738235466943409561948741)
        ·
          refine ⟨15513419150051889292865389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82738235466943409561948741 15513419150051889292865389)
          ·
            refine ⟨5817532181269458484824521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15513419150051889292865389 5817532181269458484824521)
            ·
              refine ⟨4363149135952093863618391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817532181269458484824521 4363149135952093863618391)
              ·
                refine ⟨6544723703928140795427587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363149135952093863618391 6544723703928140795427587)
                ·
                  refine ⟨9817085555892211193141381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544723703928140795427587 9817085555892211193141381)
                  ·
                    refine ⟨1840703541729789598714009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9817085555892211193141381 1840703541729789598714009)
                    ·
                      refine ⟨1380527656297342199035507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840703541729789598714009 1380527656297342199035507)
                      ·
                        rfl

theorem cell23_2688568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_2688568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688568 prefixEnd_2688568 := by exact prefixLift 2688568
  have htrace : WordTrace (prefixWord ++ tailWord_2688568) baseStart_2688568 baseEnd_2688568 := by
    simpa [prefixWord, tailWord_2688568, baseEnd_2688568] using wordTrace_append hprefix tailTrace_2688568
  have hstable : (prefixWord ++ tailWord_2688568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688568).length < 2 ^ (prefixWord ++ tailWord_2688568).sum := by decide
  have hdescent : baseEnd_2688568 < baseStart_2688568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688589 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_2688589 : Nat := 118140960795 + 2688589 * 2 ^ 59
def prefixEnd_2688589 : Nat := 4983230072969 + 3 ^ 40 * 2688589 * 2
def baseEnd_2688589 : Nat := 1380538439391086616872911

theorem tailTrace_2688589 : CollatzResearch.WordTrace tailWord_2688589 prefixEnd_2688589 1380538439391086616872911 := by
  unfold tailWord_2688589
  simp only [CollatzResearch.WordTrace]
  refine ⟨98060896856708702289564821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65373931237805801526376547 98060896856708702289564821)
  ·
    refine ⟨4596604540158220419823351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98060896856708702289564821 4596604540158220419823351)
    ·
      refine ⟨6894906810237330629735027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596604540158220419823351 6894906810237330629735027)
      ·
        refine ⟨10342360215355995944602541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894906810237330629735027 10342360215355995944602541)
        ·
          refine ⟨3878385080758498479225953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10342360215355995944602541 3878385080758498479225953)
          ·
            refine ⟨2908788810568873859419465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3878385080758498479225953 2908788810568873859419465)
            ·
              refine ⟨2181591607926655394564599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908788810568873859419465 2181591607926655394564599)
              ·
                refine ⟨3272387411889983091846899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181591607926655394564599 3272387411889983091846899)
                ·
                  refine ⟨4908581117834974637770349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272387411889983091846899 4908581117834974637770349)
                  ·
                    refine ⟨1840717919188115489163881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4908581117834974637770349 1840717919188115489163881)
                    ·
                      refine ⟨1380538439391086616872911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1840717919188115489163881 1380538439391086616872911)
                      ·
                        rfl

theorem cell23_2688589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_2688589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688589 prefixEnd_2688589 := by exact prefixLift 2688589
  have htrace : WordTrace (prefixWord ++ tailWord_2688589) baseStart_2688589 baseEnd_2688589 := by
    simpa [prefixWord, tailWord_2688589, baseEnd_2688589] using wordTrace_append hprefix tailTrace_2688589
  have hstable : (prefixWord ++ tailWord_2688589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688589).length < 2 ^ (prefixWord ++ tailWord_2688589).sum := by decide
  have hdescent : baseEnd_2688589 < baseStart_2688589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688641 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2688641 : Nat := 118140960795 + 2688641 * 2 ^ 59
def prefixEnd_2688641 : Nat := 4983230072969 + 3 ^ 40 * 2688641 * 2
def baseEnd_2688641 : Nat := 1380565140385120413422671

theorem tailTrace_2688641 : CollatzResearch.WordTrace tailWord_2688641 prefixEnd_2688641 1380565140385120413422671 := by
  unfold tailWord_2688641
  simp only [CollatzResearch.WordTrace]
  refine ⟨98062793452520315170457777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65375195635013543446971851 98062793452520315170457777)
  ·
    refine ⟨73547095089390236377843333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98062793452520315170457777 73547095089390236377843333)
    ·
      refine ⟨13790080329260669320845625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73547095089390236377843333 13790080329260669320845625)
      ·
        refine ⟨10342560246945501990634219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13790080329260669320845625 10342560246945501990634219)
        ·
          refine ⟨15513840370418252985951329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10342560246945501990634219 15513840370418252985951329)
          ·
            refine ⟨11635380277813689739463497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513840370418252985951329 11635380277813689739463497)
            ·
              refine ⟨8726535208360267304597623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635380277813689739463497 8726535208360267304597623)
              ·
                refine ⟨13089802812540400956896435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726535208360267304597623 13089802812540400956896435)
                ·
                  refine ⟨19634704218810601435344653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13089802812540400956896435 19634704218810601435344653)
                  ·
                    refine ⟨7363014082053975538254245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19634704218810601435344653 7363014082053975538254245)
                    ·
                      refine ⟨1380565140385120413422671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7363014082053975538254245 1380565140385120413422671)
                      ·
                        rfl

theorem cell23_2688641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2688641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688641 prefixEnd_2688641 := by exact prefixLift 2688641
  have htrace : WordTrace (prefixWord ++ tailWord_2688641) baseStart_2688641 baseEnd_2688641 := by
    simpa [prefixWord, tailWord_2688641, baseEnd_2688641] using wordTrace_append hprefix tailTrace_2688641
  have hstable : (prefixWord ++ tailWord_2688641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688641).length < 2 ^ (prefixWord ++ tailWord_2688641).sum := by decide
  have hdescent : baseEnd_2688641 < baseStart_2688641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688758 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2688758 : Nat := 118140960795 + 2688758 * 2 ^ 59
def prefixEnd_2688758 : Nat := 4983230072969 + 3 ^ 40 * 2688758 * 2
def baseEnd_2688758 : Nat := 460208405873898818553211

theorem tailTrace_2688758 : CollatzResearch.WordTrace tailWord_2688758 prefixEnd_2688758 460208405873898818553211 := by
  unfold tailWord_2688758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129191299568527759529183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65378040528730962768311285 6129191299568527759529183)
  ·
    refine ⟨9193786949352791639293775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129191299568527759529183 9193786949352791639293775)
    ·
      refine ⟨13790680424029187458940663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193786949352791639293775 13790680424029187458940663)
      ·
        refine ⟨20686020636043781188410995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13790680424029187458940663 20686020636043781188410995)
        ·
          refine ⟨31029030954065671782616493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20686020636043781188410995 31029030954065671782616493)
          ·
            refine ⟨11635886607774626918481185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31029030954065671782616493 11635886607774626918481185)
            ·
              refine ⟨8726914955830970188860889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635886607774626918481185 8726914955830970188860889)
              ·
                refine ⟨6545186216873227641645667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8726914955830970188860889 6545186216873227641645667)
                ·
                  refine ⟨9817779325309841462468501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6545186216873227641645667 9817779325309841462468501)
                  ·
                    refine ⟨460208405873898818553211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9817779325309841462468501 460208405873898818553211)
                    ·
                      rfl

theorem cell23_2688758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2688758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688758 prefixEnd_2688758 := by exact prefixLift 2688758
  have htrace : WordTrace (prefixWord ++ tailWord_2688758) baseStart_2688758 baseEnd_2688758 := by
    simpa [prefixWord, tailWord_2688758, baseEnd_2688758] using wordTrace_append hprefix tailTrace_2688758
  have hstable : (prefixWord ++ tailWord_2688758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688758).length < 2 ^ (prefixWord ++ tailWord_2688758).sum := by decide
  have hdescent : baseEnd_2688758 < baseStart_2688758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688768 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_2688768 : Nat := 118140960795 + 2688768 * 2 ^ 59
def prefixEnd_2688768 : Nat := 4983230072969 + 3 ^ 40 * 2688768 * 2
def baseEnd_2688768 : Nat := 1380630352428241416534587

theorem tailTrace_2688768 : CollatzResearch.WordTrace tailWord_2688768 prefixEnd_2688768 1380630352428241416534587 := by
  unfold tailWord_2688768
  simp only [CollatzResearch.WordTrace]
  refine ⟨49033712761530107930165479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65378283682040143906887305 49033712761530107930165479)
  ·
    refine ⟨73550569142295161895248219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49033712761530107930165479 73550569142295161895248219)
    ·
      refine ⟨110325853713442742842872329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73550569142295161895248219 110325853713442742842872329)
      ·
        refine ⟨82744390285082057132154247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110325853713442742842872329 82744390285082057132154247)
        ·
          refine ⟨124116585427623085698231371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82744390285082057132154247 124116585427623085698231371)
          ·
            refine ⟨186174878141434628547347057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124116585427623085698231371 186174878141434628547347057)
            ·
              refine ⟨139631158606075971410510293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186174878141434628547347057 139631158606075971410510293)
              ·
                refine ⟨3272605279829905579933835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139631158606075971410510293 3272605279829905579933835)
                ·
                  refine ⟨4908907919744858369900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272605279829905579933835 4908907919744858369900753)
                  ·
                    refine ⟨3681680939808643777425565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908907919744858369900753 3681680939808643777425565)
                    ·
                      refine ⟨1380630352428241416534587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3681680939808643777425565 1380630352428241416534587)
                      ·
                        rfl

theorem cell23_2688768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_2688768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688768 prefixEnd_2688768 := by exact prefixLift 2688768
  have htrace : WordTrace (prefixWord ++ tailWord_2688768) baseStart_2688768 baseEnd_2688768 := by
    simpa [prefixWord, tailWord_2688768, baseEnd_2688768] using wordTrace_append hprefix tailTrace_2688768
  have hstable : (prefixWord ++ tailWord_2688768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688768).length < 2 ^ (prefixWord ++ tailWord_2688768).sum := by decide
  have hdescent : baseEnd_2688768 < baseStart_2688768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688775 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 4, 4]
def baseStart_2688775 : Nat := 118140960795 + 2688775 * 2 ^ 59
def prefixEnd_2688775 : Nat := 4983230072969 + 3 ^ 40 * 2688775 * 2
def baseEnd_2688775 : Nat := 460211315597607629715685

theorem tailTrace_2688775 : CollatzResearch.WordTrace tailWord_2688775 prefixEnd_2688775 460211315597607629715685 := by
  unfold tailWord_2688775
  simp only [CollatzResearch.WordTrace]
  refine ⟨98067680834034856055835779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65378453889356570703890519 98067680834034856055835779)
  ·
    refine ⟨147101521251052284083753669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98067680834034856055835779 147101521251052284083753669)
    ·
      refine ⟨27581535234572303265703813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147101521251052284083753669 27581535234572303265703813)
      ·
        refine ⟨5171537856482306862319465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27581535234572303265703813 5171537856482306862319465)
        ·
          refine ⟨3878653392361730146739599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171537856482306862319465 3878653392361730146739599)
          ·
            refine ⟨5817980088542595220109399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878653392361730146739599 5817980088542595220109399)
            ·
              refine ⟨8726970132813892830164099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5817980088542595220109399 8726970132813892830164099)
              ·
                refine ⟨13090455199220839245246149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726970132813892830164099 13090455199220839245246149)
                ·
                  refine ⟨2454460349853907358483653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13090455199220839245246149 2454460349853907358483653)
                  ·
                    refine ⟨460211315597607629715685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454460349853907358483653 460211315597607629715685)
                    ·
                      rfl

theorem cell23_2688775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_2688775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688775 prefixEnd_2688775 := by exact prefixLift 2688775
  have htrace : WordTrace (prefixWord ++ tailWord_2688775) baseStart_2688775 baseEnd_2688775 := by
    simpa [prefixWord, tailWord_2688775, baseEnd_2688775] using wordTrace_append hprefix tailTrace_2688775
  have hstable : (prefixWord ++ tailWord_2688775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688775).length < 2 ^ (prefixWord ++ tailWord_2688775).sum := by decide
  have hdescent : baseEnd_2688775 < baseStart_2688775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688841 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_2688841 : Nat := 118140960795 + 2688841 * 2 ^ 59
def prefixEnd_2688841 : Nat := 4983230072969 + 3 ^ 40 * 2688841 * 2
def baseEnd_2688841 : Nat := 1380667836516019630921751

theorem tailTrace_2688841 : CollatzResearch.WordTrace tailWord_2688841 prefixEnd_2688841 1380667836516019630921751 := by
  unfold tailWord_2688841
  simp only [CollatzResearch.WordTrace]
  refine ⟨98070088051795749327738377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65380058701197166218492251 98070088051795749327738377)
  ·
    refine ⟨73552566038846811995803783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98070088051795749327738377 73552566038846811995803783)
    ·
      refine ⟨110328849058270217993705675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73552566038846811995803783 110328849058270217993705675)
      ·
        refine ⟨165493273587405326990558513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110328849058270217993705675 165493273587405326990558513)
        ·
          refine ⟨124119955190553995242918885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165493273587405326990558513 124119955190553995242918885)
          ·
            refine ⟨23272491598228874108047291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124119955190553995242918885 23272491598228874108047291)
            ·
              refine ⟨34908737397343311162070937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23272491598228874108047291 34908737397343311162070937)
              ·
                refine ⟨26181553048007483371553203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34908737397343311162070937 26181553048007483371553203)
                ·
                  refine ⟨39272329572011225057329805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26181553048007483371553203 39272329572011225057329805)
                  ·
                    refine ⟨14727123589504209396498677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39272329572011225057329805 14727123589504209396498677)
                    ·
                      refine ⟨1380667836516019630921751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14727123589504209396498677 1380667836516019630921751)
                      ·
                        rfl

theorem cell23_2688841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_2688841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688841 prefixEnd_2688841 := by exact prefixLift 2688841
  have htrace : WordTrace (prefixWord ++ tailWord_2688841) baseStart_2688841 baseEnd_2688841 := by
    simpa [prefixWord, tailWord_2688841, baseEnd_2688841] using wordTrace_append hprefix tailTrace_2688841
  have hstable : (prefixWord ++ tailWord_2688841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688841).length < 2 ^ (prefixWord ++ tailWord_2688841).sum := by decide
  have hdescent : baseEnd_2688841 < baseStart_2688841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688849 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 2, 1, 3]
def baseStart_2688849 : Nat := 118140960795 + 2688849 * 2 ^ 59
def prefixEnd_2688849 : Nat := 4983230072969 + 3 ^ 40 * 2688849 * 2
def baseEnd_2688849 : Nat := 1380671944361255599621715

theorem tailTrace_2688849 : CollatzResearch.WordTrace tailWord_2688849 prefixEnd_2688849 1380671944361255599621715 := by
  unfold tailWord_2688849
  simp only [CollatzResearch.WordTrace]
  refine ⟨98070379835766766694029601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65380253223844511129353067 98070379835766766694029601)
  ·
    refine ⟨73552784876825075020522201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98070379835766766694029601 73552784876825075020522201)
    ·
      refine ⟨55164588657618806265391651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73552784876825075020522201 55164588657618806265391651)
      ·
        refine ⟨82746882986428209398087477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55164588657618806265391651 82746882986428209398087477)
        ·
          refine ⟨7757520279977644631070701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82746882986428209398087477 7757520279977644631070701)
          ·
            refine ⟨2909070104991616736651513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7757520279977644631070701 2909070104991616736651513)
            ·
              refine ⟨2181802578743712552488635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909070104991616736651513 2181802578743712552488635)
              ·
                refine ⟨3272703868115568828732953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181802578743712552488635 3272703868115568828732953)
                ·
                  refine ⟨2454527901086676621549715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3272703868115568828732953 2454527901086676621549715)
                  ·
                    refine ⟨3681791851630014932324573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2454527901086676621549715 3681791851630014932324573)
                    ·
                      refine ⟨1380671944361255599621715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3681791851630014932324573 1380671944361255599621715)
                      ·
                        rfl

theorem cell23_2688849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 1, 3].length) (baseStart_2688849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688849 prefixEnd_2688849 := by exact prefixLift 2688849
  have htrace : WordTrace (prefixWord ++ tailWord_2688849) baseStart_2688849 baseEnd_2688849 := by
    simpa [prefixWord, tailWord_2688849, baseEnd_2688849] using wordTrace_append hprefix tailTrace_2688849
  have hstable : (prefixWord ++ tailWord_2688849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688849).length < 2 ^ (prefixWord ++ tailWord_2688849).sum := by decide
  have hdescent : baseEnd_2688849 < baseStart_2688849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688891 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 3, 7]
def baseStart_2688891 : Nat := 118140960795 + 2688891 * 2 ^ 59
def prefixEnd_2688891 : Nat := 4983230072969 + 3 ^ 40 * 2688891 * 2
def baseEnd_2688891 : Nat := 460231170182914811765507

theorem tailTrace_2688891 : CollatzResearch.WordTrace tailWord_2688891 prefixEnd_2688891 460231170182914811765507 := by
  unfold tailWord_2688891
  simp only [CollatzResearch.WordTrace]
  refine ⟨98071911701614607867058527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65381274467743071911372351 98071911701614607867058527)
  ·
    refine ⟨147107867552421911800587791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98071911701614607867058527 147107867552421911800587791)
    ·
      refine ⟨220661801328632867700881687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147107867552421911800587791 220661801328632867700881687)
      ·
        refine ⟨330992701992949301551322531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220661801328632867700881687 330992701992949301551322531)
        ·
          refine ⟨496489052989423952326983797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330992701992949301551322531 496489052989423952326983797)
          ·
            refine ⟨46545848717758495530654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 496489052989423952326983797 46545848717758495530654731)
            ·
              refine ⟨69818773076637743295982097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46545848717758495530654731 69818773076637743295982097)
              ·
                refine ⟨52364079807478307471986573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69818773076637743295982097 52364079807478307471986573)
                ·
                  refine ⟨19636529927804365301994965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52364079807478307471986573 19636529927804365301994965)
                  ·
                    refine ⟨460231170182914811765507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19636529927804365301994965 460231170182914811765507)
                    ·
                      rfl

theorem cell23_2688891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_2688891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688891 prefixEnd_2688891 := by exact prefixLift 2688891
  have htrace : WordTrace (prefixWord ++ tailWord_2688891) baseStart_2688891 baseEnd_2688891 := by
    simpa [prefixWord, tailWord_2688891, baseEnd_2688891] using wordTrace_append hprefix tailTrace_2688891
  have hstable : (prefixWord ++ tailWord_2688891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688891).length < 2 ^ (prefixWord ++ tailWord_2688891).sum := by decide
  have hdescent : baseEnd_2688891 < baseStart_2688891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688925 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2688925 : Nat := 118140960795 + 2688925 * 2 ^ 59
def prefixEnd_2688925 : Nat := 4983230072969 + 3 ^ 40 * 2688925 * 2
def baseEnd_2688925 : Nat := 460236989630332434090455

theorem tailTrace_2688925 : CollatzResearch.WordTrace tailWord_2688925 prefixEnd_2688925 460236989630332434090455 := by
  unfold tailWord_2688925
  simp only [CollatzResearch.WordTrace]
  refine ⟨98073151783491431673796229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65382101188994287782530819 98073151783491431673796229)
  ·
    refine ⟨18388715959404643438836793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98073151783491431673796229 18388715959404643438836793)
    ·
      refine ⟨13791536969553482579127595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18388715959404643438836793 13791536969553482579127595)
      ·
        refine ⟨20687305454330223868691393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13791536969553482579127595 20687305454330223868691393)
        ·
          refine ⟨15515479090747667901518545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20687305454330223868691393 15515479090747667901518545)
          ·
            refine ⟨11636609318060750926138909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15515479090747667901518545 11636609318060750926138909)
            ·
              refine ⟨4363728494272781597302091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11636609318060750926138909 4363728494272781597302091)
              ·
                refine ⟨6545592741409172395953137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363728494272781597302091 6545592741409172395953137)
                ·
                  refine ⟨4909194556056879296964853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545592741409172395953137 4909194556056879296964853)
                  ·
                    refine ⟨460236989630332434090455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4909194556056879296964853 460236989630332434090455)
                    ·
                      rfl

theorem cell23_2688925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2688925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2688925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2688925 prefixEnd_2688925 := by exact prefixLift 2688925
  have htrace : WordTrace (prefixWord ++ tailWord_2688925) baseStart_2688925 baseEnd_2688925 := by
    simpa [prefixWord, tailWord_2688925, baseEnd_2688925] using wordTrace_append hprefix tailTrace_2688925
  have hstable : (prefixWord ++ tailWord_2688925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688925).length < 2 ^ (prefixWord ++ tailWord_2688925).sum := by decide
  have hdescent : baseEnd_2688925 < baseStart_2688925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689006 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2689006 : Nat := 118140960795 + 2689006 * 2 ^ 59
def prefixEnd_2689006 : Nat := 4983230072969 + 3 ^ 40 * 2689006 * 2
def baseEnd_2689006 : Nat := 460250853608003828452831

theorem tailTrace_2689006 : CollatzResearch.WordTrace tailWord_2689006 prefixEnd_2689006 460250853608003828452831 := by
  unfold tailWord_2689006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259513262024747813436859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65384070730798655004996581 12259513262024747813436859)
  ·
    refine ⟨18389269893037121720155289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259513262024747813436859 18389269893037121720155289)
    ·
      refine ⟨13791952419777841290116467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18389269893037121720155289 13791952419777841290116467)
      ·
        refine ⟨20687928629666761935174701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13791952419777841290116467 20687928629666761935174701)
        ·
          refine ⟨7757973236125035725690513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20687928629666761935174701 7757973236125035725690513)
          ·
            refine ⟨5818479927093776794267885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757973236125035725690513 5818479927093776794267885)
            ·
              refine ⟨2181929972660166297850457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5818479927093776794267885 2181929972660166297850457)
              ·
                refine ⟨1636447479495124723387843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181929972660166297850457 1636447479495124723387843)
                ·
                  refine ⟨2454671219242687085081765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636447479495124723387843 2454671219242687085081765)
                  ·
                    refine ⟨460250853608003828452831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454671219242687085081765 460250853608003828452831)
                    ·
                      rfl

theorem cell23_2689006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2689006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689006 prefixEnd_2689006 := by exact prefixLift 2689006
  have htrace : WordTrace (prefixWord ++ tailWord_2689006) baseStart_2689006 baseEnd_2689006 := by
    simpa [prefixWord, tailWord_2689006, baseEnd_2689006] using wordTrace_append hprefix tailTrace_2689006
  have hstable : (prefixWord ++ tailWord_2689006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689006).length < 2 ^ (prefixWord ++ tailWord_2689006).sum := by decide
  have hdescent : baseEnd_2689006 < baseStart_2689006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689018 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_2689018 : Nat := 118140960795 + 2689018 * 2 ^ 59
def prefixEnd_2689018 : Nat := 4983230072969 + 3 ^ 40 * 2689018 * 2
def baseEnd_2689018 : Nat := 1380758722591865438408437

theorem tailTrace_2689018 : CollatzResearch.WordTrace tailWord_2689018 prefixEnd_2689018 1380758722591865438408437 := by
  unfold tailWord_2689018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24519135943038627139232927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65384362514769672371287805 24519135943038627139232927)
  ·
    refine ⟨36778703914557940708849391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24519135943038627139232927 36778703914557940708849391)
    ·
      refine ⟨55168055871836911063274087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36778703914557940708849391 55168055871836911063274087)
      ·
        refine ⟨82752083807755366594911131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55168055871836911063274087 82752083807755366594911131)
        ·
          refine ⟨124128125711633049892366697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82752083807755366594911131 124128125711633049892366697)
          ·
            refine ⟨93096094283724787419275023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124128125711633049892366697 93096094283724787419275023)
            ·
              refine ⟨139644141425587181128912535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93096094283724787419275023 139644141425587181128912535)
              ·
                refine ⟨209466212138380771693368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139644141425587181128912535 209466212138380771693368803)
                ·
                  refine ⟨314199318207571157540053205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209466212138380771693368803 314199318207571157540053205)
                  ·
                    refine ⟨7364046520489949004844997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 314199318207571157540053205 7364046520489949004844997)
                    ·
                      refine ⟨1380758722591865438408437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7364046520489949004844997 1380758722591865438408437)
                      ·
                        rfl

theorem cell23_2689018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_2689018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689018 prefixEnd_2689018 := by exact prefixLift 2689018
  have htrace : WordTrace (prefixWord ++ tailWord_2689018) baseStart_2689018 baseEnd_2689018 := by
    simpa [prefixWord, tailWord_2689018, baseEnd_2689018] using wordTrace_append hprefix tailTrace_2689018
  have hstable : (prefixWord ++ tailWord_2689018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689018).length < 2 ^ (prefixWord ++ tailWord_2689018).sum := by decide
  have hdescent : baseEnd_2689018 < baseStart_2689018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689035 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4]
def baseStart_2689035 : Nat := 118140960795 + 2689035 * 2 ^ 59
def prefixEnd_2689035 : Nat := 4983230072969 + 3 ^ 40 * 2689035 * 2
def baseEnd_2689035 : Nat := 1380767451762991871895859

theorem tailTrace_2689035 : CollatzResearch.WordTrace tailWord_2689035 prefixEnd_2689035 1380767451762991871895859 := by
  unfold tailWord_2689035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98077163813092920460300559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65384775875395280306867039 98077163813092920460300559)
  ·
    refine ⟨147115745719639380690450839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98077163813092920460300559 147115745719639380690450839)
    ·
      refine ⟨220673618579459071035676259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147115745719639380690450839 220673618579459071035676259)
      ·
        refine ⟨331010427869188606553514389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220673618579459071035676259 331010427869188606553514389)
        ·
          refine ⟨15516113806368215932195987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 331010427869188606553514389 15516113806368215932195987)
          ·
            refine ⟨23274170709552323898293981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15516113806368215932195987 23274170709552323898293981)
            ·
              refine ⟨8727814016082121461860243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23274170709552323898293981 8727814016082121461860243)
              ·
                refine ⟨13091721024123182192790365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8727814016082121461860243 13091721024123182192790365)
                ·
                  refine ⟨4909395384046193322296387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13091721024123182192790365 4909395384046193322296387)
                  ·
                    refine ⟨7364093076069289983444581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909395384046193322296387 7364093076069289983444581)
                    ·
                      refine ⟨1380767451762991871895859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7364093076069289983444581 1380767451762991871895859)
                      ·
                        rfl

theorem cell23_2689035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_2689035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689035 prefixEnd_2689035 := by exact prefixLift 2689035
  have htrace : WordTrace (prefixWord ++ tailWord_2689035) baseStart_2689035 baseEnd_2689035 := by
    simpa [prefixWord, tailWord_2689035, baseEnd_2689035] using wordTrace_append hprefix tailTrace_2689035
  have hstable : (prefixWord ++ tailWord_2689035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689035).length < 2 ^ (prefixWord ++ tailWord_2689035).sum := by decide
  have hdescent : baseEnd_2689035 < baseStart_2689035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689063 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2689063 : Nat := 118140960795 + 2689063 * 2 ^ 59
def prefixEnd_2689063 : Nat := 4983230072969 + 3 ^ 40 * 2689063 * 2
def baseEnd_2689063 : Nat := 1380781829221317762345731

theorem tailTrace_2689063 : CollatzResearch.WordTrace tailWord_2689063 prefixEnd_2689063 1380781829221317762345731 := by
  unfold tailWord_2689063
  simp only [CollatzResearch.WordTrace]
  refine ⟨98078185056991481242319843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65385456704660987494879895 98078185056991481242319843)
  ·
    refine ⟨147117277585487221863479765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98078185056991481242319843 147117277585487221863479765)
    ·
      refine ⟨3448061193409856762425307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 147117277585487221863479765 3448061193409856762425307)
      ·
        refine ⟨5172091790114785143637961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448061193409856762425307 5172091790114785143637961)
        ·
          refine ⟨3879068842586088857728471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5172091790114785143637961 3879068842586088857728471)
          ·
            refine ⟨5818603263879133286592707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879068842586088857728471 5818603263879133286592707)
            ·
              refine ⟨8727904895818699929889061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818603263879133286592707 8727904895818699929889061)
              ·
                refine ⟨1636482167966006236854199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8727904895818699929889061 1636482167966006236854199)
                ·
                  refine ⟨2454723251949009355281299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636482167966006236854199 2454723251949009355281299)
                  ·
                    refine ⟨3682084877923514032921949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2454723251949009355281299 3682084877923514032921949)
                    ·
                      refine ⟨1380781829221317762345731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682084877923514032921949 1380781829221317762345731)
                      ·
                        rfl

theorem cell23_2689063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2689063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689063 prefixEnd_2689063 := by exact prefixLift 2689063
  have htrace : WordTrace (prefixWord ++ tailWord_2689063) baseStart_2689063 baseEnd_2689063 := by
    simpa [prefixWord, tailWord_2689063, baseEnd_2689063] using wordTrace_append hprefix tailTrace_2689063
  have hstable : (prefixWord ++ tailWord_2689063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689063).length < 2 ^ (prefixWord ++ tailWord_2689063).sum := by decide
  have hdescent : baseEnd_2689063 < baseStart_2689063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2689068 : Nat := 118140960795 + 2689068 * 2 ^ 59
def prefixEnd_2689068 : Nat := 4983230072969 + 3 ^ 40 * 2689068 * 2
def baseEnd_2689068 : Nat := 1380784396624590242783207

theorem tailTrace_2689068 : CollatzResearch.WordTrace tailWord_2689068 prefixEnd_2689068 1380784396624590242783207 := by
  unfold tailWord_2689068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49039183710986683548125929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65385578281315578064167905 49039183710986683548125929)
  ·
    refine ⟨36779387783240012661094447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49039183710986683548125929 36779387783240012661094447)
    ·
      refine ⟨55169081674860018991641671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36779387783240012661094447 55169081674860018991641671)
      ·
        refine ⟨82753622512290028487462507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55169081674860018991641671 82753622512290028487462507)
        ·
          refine ⟨124130433768435042731193761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82753622512290028487462507 124130433768435042731193761)
          ·
            refine ⟨93097825326326282048395321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124130433768435042731193761 93097825326326282048395321)
            ·
              refine ⟨69823368994744711536296491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93097825326326282048395321 69823368994744711536296491)
              ·
                refine ⟨104735053492117067304444737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69823368994744711536296491 104735053492117067304444737)
                ·
                  refine ⟨78551290119087800478333553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104735053492117067304444737 78551290119087800478333553)
                  ·
                    refine ⟨58913467589315850358750165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78551290119087800478333553 58913467589315850358750165)
                    ·
                      refine ⟨1380784396624590242783207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58913467589315850358750165 1380784396624590242783207)
                      ·
                        rfl

theorem cell23_2689068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2689068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689068 prefixEnd_2689068 := by exact prefixLift 2689068
  have htrace : WordTrace (prefixWord ++ tailWord_2689068) baseStart_2689068 baseEnd_2689068 := by
    simpa [prefixWord, tailWord_2689068, baseEnd_2689068] using wordTrace_append hprefix tailTrace_2689068
  have hstable : (prefixWord ++ tailWord_2689068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689068).length < 2 ^ (prefixWord ++ tailWord_2689068).sum := by decide
  have hdescent : baseEnd_2689068 < baseStart_2689068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689102 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2689102 : Nat := 118140960795 + 2689102 * 2 ^ 59
def prefixEnd_2689102 : Nat := 4983230072969 + 3 ^ 40 * 2689102 * 2
def baseEnd_2689102 : Nat := 1380801854966843109758051

theorem tailTrace_2689102 : CollatzResearch.WordTrace tailWord_2689102 prefixEnd_2689102 1380801854966843109758051 := by
  unfold tailWord_2689102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259950937981273862873695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65386405002566793935326373 12259950937981273862873695)
  ·
    refine ⟨18389926406971910794310543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259950937981273862873695 18389926406971910794310543)
    ·
      refine ⟨27584889610457866191465815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389926406971910794310543 27584889610457866191465815)
      ·
        refine ⟨41377334415686799287198723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27584889610457866191465815 41377334415686799287198723)
        ·
          refine ⟨62066001623530198930798085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41377334415686799287198723 62066001623530198930798085)
          ·
            refine ⟨11637375304411912299524641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62066001623530198930798085 11637375304411912299524641)
            ·
              refine ⟨8728031478308934224643481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11637375304411912299524641 8728031478308934224643481)
              ·
                refine ⟨6546023608731700668482611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8728031478308934224643481 6546023608731700668482611)
                ·
                  refine ⟨9819035413097551002723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546023608731700668482611 9819035413097551002723917)
                  ·
                    refine ⟨3682138279911581626021469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9819035413097551002723917 3682138279911581626021469)
                    ·
                      refine ⟨1380801854966843109758051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682138279911581626021469 1380801854966843109758051)
                      ·
                        rfl

theorem cell23_2689102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2689102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689102 prefixEnd_2689102 := by exact prefixLift 2689102
  have htrace : WordTrace (prefixWord ++ tailWord_2689102) baseStart_2689102 baseEnd_2689102 := by
    simpa [prefixWord, tailWord_2689102, baseEnd_2689102] using wordTrace_append hprefix tailTrace_2689102
  have hstable : (prefixWord ++ tailWord_2689102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689102).length < 2 ^ (prefixWord ++ tailWord_2689102).sum := by decide
  have hdescent : baseEnd_2689102 < baseStart_2689102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689135 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 2, 6]
def baseStart_2689135 : Nat := 118140960795 + 2689135 * 2 ^ 59
def prefixEnd_2689135 : Nat := 4983230072969 + 3 ^ 40 * 2689135 * 2
def baseEnd_2689135 : Nat := 460272933276147160215133

theorem tailTrace_2689135 : CollatzResearch.WordTrace tailWord_2689135 prefixEnd_2689135 460272933276147160215133 := by
  unfold tailWord_2689135
  simp only [CollatzResearch.WordTrace]
  refine ⟨98080811112730637538940859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65387207408487091692627239 98080811112730637538940859)
  ·
    refine ⟨147121216669095956308411289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98080811112730637538940859 147121216669095956308411289)
    ·
      refine ⟨110340912501821967231308467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147121216669095956308411289 110340912501821967231308467)
      ·
        refine ⟨165511368752732950846962701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110340912501821967231308467 165511368752732950846962701)
        ·
          refine ⟨62066763282274856567611013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165511368752732950846962701 62066763282274856567611013)
          ·
            refine ⟨11637518115426535606427065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62066763282274856567611013 11637518115426535606427065)
            ·
              refine ⟨8728138586569901704820299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11637518115426535606427065 8728138586569901704820299)
              ·
                refine ⟨13092207879854852557230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728138586569901704820299 13092207879854852557230449)
                ·
                  refine ⟨9819155909891139417922837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13092207879854852557230449 9819155909891139417922837)
                  ·
                    refine ⟨460272933276147160215133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9819155909891139417922837 460272933276147160215133)
                    ·
                      rfl

theorem cell23_2689135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_2689135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689135 prefixEnd_2689135 := by exact prefixLift 2689135
  have htrace : WordTrace (prefixWord ++ tailWord_2689135) baseStart_2689135 baseEnd_2689135 := by
    simpa [prefixWord, tailWord_2689135, baseEnd_2689135] using wordTrace_append hprefix tailTrace_2689135
  have hstable : (prefixWord ++ tailWord_2689135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689135).length < 2 ^ (prefixWord ++ tailWord_2689135).sum := by decide
  have hdescent : baseEnd_2689135 < baseStart_2689135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689136 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3]
def baseStart_2689136 : Nat := 118140960795 + 2689136 * 2 ^ 59
def prefixEnd_2689136 : Nat := 4983230072969 + 3 ^ 40 * 2689136 * 2
def baseEnd_2689136 : Nat := 1380819313309095976732895

theorem tailTrace_2689136 : CollatzResearch.WordTrace tailWord_2689136 prefixEnd_2689136 1380819313309095976732895 := by
  unfold tailWord_2689136
  simp only [CollatzResearch.WordTrace]
  refine ⟨49040423792863507354863631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65387231723818009806484841 49040423792863507354863631)
  ·
    refine ⟨73560635689295261032295447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49040423792863507354863631 73560635689295261032295447)
    ·
      refine ⟨110340953533942891548443171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73560635689295261032295447 110340953533942891548443171)
      ·
        refine ⟨165511430300914337322664757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110340953533942891548443171 165511430300914337322664757)
        ·
          refine ⟨15516696590710719123999821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165511430300914337322664757 15516696590710719123999821)
          ·
            refine ⟨5818761221516519671499933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15516696590710719123999821 5818761221516519671499933)
            ·
              refine ⟨2182035458068694876812475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5818761221516519671499933 2182035458068694876812475)
              ·
                refine ⟨3273053187103042315218713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182035458068694876812475 3273053187103042315218713)
                ·
                  refine ⟨2454789890327281736414035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273053187103042315218713 2454789890327281736414035)
                  ·
                    refine ⟨3682184835490922604621053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2454789890327281736414035 3682184835490922604621053)
                    ·
                      refine ⟨1380819313309095976732895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682184835490922604621053 1380819313309095976732895)
                      ·
                        rfl

theorem cell23_2689136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3].length) (baseStart_2689136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689136 prefixEnd_2689136 := by exact prefixLift 2689136
  have htrace : WordTrace (prefixWord ++ tailWord_2689136) baseStart_2689136 baseEnd_2689136 := by
    simpa [prefixWord, tailWord_2689136, baseEnd_2689136] using wordTrace_append hprefix tailTrace_2689136
  have hstable : (prefixWord ++ tailWord_2689136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689136).length < 2 ^ (prefixWord ++ tailWord_2689136).sum := by decide
  have hdescent : baseEnd_2689136 < baseStart_2689136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689159 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_2689159 : Nat := 118140960795 + 2689159 * 2 ^ 59
def prefixEnd_2689159 : Nat := 4983230072969 + 3 ^ 40 * 2689159 * 2
def baseEnd_2689159 : Nat := 1380831123364149386745289

theorem tailTrace_2689159 : CollatzResearch.WordTrace tailWord_2689159 prefixEnd_2689159 1380831123364149386745289 := by
  unfold tailWord_2689159
  simp only [CollatzResearch.WordTrace]
  refine ⟨98081686464643689637814531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65387790976429126425209687 98081686464643689637814531)
  ·
    refine ⟨147122529696965534456721797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98081686464643689637814531 147122529696965534456721797)
    ·
      refine ⟨27585474318181037710635337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147122529696965534456721797 27585474318181037710635337)
      ·
        refine ⟨20689105738635778282976503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27585474318181037710635337 20689105738635778282976503)
        ·
          refine ⟨31033658607953667424464755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20689105738635778282976503 31033658607953667424464755)
          ·
            refine ⟨46550487911930501136697133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31033658607953667424464755 46550487911930501136697133)
            ·
              refine ⟨17456432966973937926261425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46550487911930501136697133 17456432966973937926261425)
              ·
                refine ⟨13092324725230453444696069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17456432966973937926261425 13092324725230453444696069)
                ·
                  refine ⟨2454810885980710020880513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13092324725230453444696069 2454810885980710020880513)
                  ·
                    refine ⟨1841108164485532515660385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2454810885980710020880513 1841108164485532515660385)
                    ·
                      refine ⟨1380831123364149386745289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841108164485532515660385 1380831123364149386745289)
                      ·
                        rfl

theorem cell23_2689159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_2689159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689159 prefixEnd_2689159 := by exact prefixLift 2689159
  have htrace : WordTrace (prefixWord ++ tailWord_2689159) baseStart_2689159 baseEnd_2689159 := by
    simpa [prefixWord, tailWord_2689159, baseEnd_2689159] using wordTrace_append hprefix tailTrace_2689159
  have hstable : (prefixWord ++ tailWord_2689159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689159).length < 2 ^ (prefixWord ++ tailWord_2689159).sum := by decide
  have hdescent : baseEnd_2689159 < baseStart_2689159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689162 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2689162 : Nat := 118140960795 + 2689162 * 2 ^ 59
def prefixEnd_2689162 : Nat := 4983230072969 + 3 ^ 40 * 2689162 * 2
def baseEnd_2689162 : Nat := 1380832663806112875007775

theorem tailTrace_2689162 : CollatzResearch.WordTrace tailWord_2689162 prefixEnd_2689162 1380832663806112875007775 := by
  unfold tailWord_2689162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24520448970908205287543435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65387863922421880766782493 24520448970908205287543435)
  ·
    refine ⟨36780673456362307931315153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24520448970908205287543435 36780673456362307931315153)
    ·
      refine ⟨27585505092271730948486365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36780673456362307931315153 27585505092271730948486365)
      ·
        refine ⟨10344564409601899105682387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27585505092271730948486365 10344564409601899105682387)
        ·
          refine ⟨15516846614402848658523581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10344564409601899105682387 15516846614402848658523581)
          ·
            refine ⟨5818817480401068246946343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15516846614402848658523581 5818817480401068246946343)
            ·
              refine ⟨8728226220601602370419515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818817480401068246946343 8728226220601602370419515)
              ·
                refine ⟨13092339330902403555629273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728226220601602370419515 13092339330902403555629273)
                ·
                  refine ⟨9819254498176802666721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13092339330902403555629273 9819254498176802666721955)
                  ·
                    refine ⟨14728881747265204000082933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9819254498176802666721955 14728881747265204000082933)
                    ·
                      refine ⟨1380832663806112875007775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14728881747265204000082933 1380832663806112875007775)
                      ·
                        rfl

theorem cell23_2689162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2689162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689162 prefixEnd_2689162 := by exact prefixLift 2689162
  have htrace : WordTrace (prefixWord ++ tailWord_2689162) baseStart_2689162 baseEnd_2689162 := by
    simpa [prefixWord, tailWord_2689162, baseEnd_2689162] using wordTrace_append hprefix tailTrace_2689162
  have hstable : (prefixWord ++ tailWord_2689162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689162).length < 2 ^ (prefixWord ++ tailWord_2689162).sum := by decide
  have hdescent : baseEnd_2689162 < baseStart_2689162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689232 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2]
def baseStart_2689232 : Nat := 118140960795 + 2689232 * 2 ^ 59
def prefixEnd_2689232 : Nat := 4983230072969 + 3 ^ 40 * 2689232 * 2
def baseEnd_2689232 : Nat := 1380868607451927601132453

theorem tailTrace_2689232 : CollatzResearch.WordTrace tailWord_2689232 prefixEnd_2689232 1380868607451927601132453 := by
  unfold tailWord_2689232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49042174496689611552610975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65389565995586148736814633 49042174496689611552610975)
  ·
    refine ⟨73563261745034417328916463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49042174496689611552610975 73563261745034417328916463)
    ·
      refine ⟨110344892617551625993374695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73563261745034417328916463 110344892617551625993374695)
      ·
        refine ⟨165517338926327438990062043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110344892617551625993374695 165517338926327438990062043)
        ·
          refine ⟨248276008389491158485093065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165517338926327438990062043 248276008389491158485093065)
          ·
            refine ⟨186207006292118368863819799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248276008389491158485093065 186207006292118368863819799)
            ·
              refine ⟨279310509438177553295729699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186207006292118368863819799 279310509438177553295729699)
              ·
                refine ⟨418965764157266329943594549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279310509438177553295729699 418965764157266329943594549)
                ·
                  refine ⟨39278040389743718432211989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418965764157266329943594549 39278040389743718432211989)
                  ·
                    refine ⟨1841158143269236801509937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39278040389743718432211989 1841158143269236801509937)
                    ·
                      refine ⟨1380868607451927601132453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841158143269236801509937 1380868607451927601132453)
                      ·
                        rfl

theorem cell23_2689232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2].length) (baseStart_2689232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689232 prefixEnd_2689232 := by exact prefixLift 2689232
  have htrace : WordTrace (prefixWord ++ tailWord_2689232) baseStart_2689232 baseEnd_2689232 := by
    simpa [prefixWord, tailWord_2689232, baseEnd_2689232] using wordTrace_append hprefix tailTrace_2689232
  have hstable : (prefixWord ++ tailWord_2689232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689232).length < 2 ^ (prefixWord ++ tailWord_2689232).sum := by decide
  have hdescent : baseEnd_2689232 < baseStart_2689232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689249 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 4, 2]
def baseStart_2689249 : Nat := 118140960795 + 2689249 * 2 ^ 59
def prefixEnd_2689249 : Nat := 4983230072969 + 3 ^ 40 * 2689249 * 2
def baseEnd_2689249 : Nat := 1380877336623054034619875

theorem tailTrace_2689249 : CollatzResearch.WordTrace tailWord_2689249 prefixEnd_2689249 1380877336623054034619875 := by
  unfold tailWord_2689249
  simp only [CollatzResearch.WordTrace]
  refine ⟨98084969034317635008590801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65389979356211756672393867 98084969034317635008590801)
  ·
    refine ⟨73563726775738226256443101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98084969034317635008590801 73563726775738226256443101)
    ·
      refine ⟨27586397540901834846166163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73563726775738226256443101 27586397540901834846166163)
      ·
        refine ⟨41379596311352752269249245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27586397540901834846166163 41379596311352752269249245)
        ·
          refine ⟨15517348616757282100968467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41379596311352752269249245 15517348616757282100968467)
          ·
            refine ⟨23276022925135923151452701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15517348616757282100968467 23276022925135923151452701)
            ·
              refine ⟨8728508596925971181794763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23276022925135923151452701 8728508596925971181794763)
              ·
                refine ⟨13092762895388956772692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728508596925971181794763 13092762895388956772692145)
                ·
                  refine ⟨9819572171541717579519109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13092762895388956772692145 9819572171541717579519109)
                  ·
                    refine ⟨1841169782164072046159833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9819572171541717579519109 1841169782164072046159833)
                    ·
                      refine ⟨1380877336623054034619875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841169782164072046159833 1380877336623054034619875)
                      ·
                        rfl

theorem cell23_2689249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_2689249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689249 prefixEnd_2689249 := by exact prefixLift 2689249
  have htrace : WordTrace (prefixWord ++ tailWord_2689249) baseStart_2689249 baseEnd_2689249 := by
    simpa [prefixWord, tailWord_2689249, baseEnd_2689249] using wordTrace_append hprefix tailTrace_2689249
  have hstable : (prefixWord ++ tailWord_2689249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689249).length < 2 ^ (prefixWord ++ tailWord_2689249).sum := by decide
  have hdescent : baseEnd_2689249 < baseStart_2689249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689252 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_2689252 : Nat := 118140960795 + 2689252 * 2 ^ 59
def prefixEnd_2689252 : Nat := 4983230072969 + 3 ^ 40 * 2689252 * 2
def baseEnd_2689252 : Nat := 1380878877065017522882361

theorem tailTrace_2689252 : CollatzResearch.WordTrace tailWord_2689252 prefixEnd_2689252 1380878877065017522882361 := by
  unfold tailWord_2689252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49042539226653383260475005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65390052302204511013966673 49042539226653383260475005)
  ·
    refine ⟨18390952209995018722678127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49042539226653383260475005 18390952209995018722678127)
    ·
      refine ⟨27586428314992528084017191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390952209995018722678127 27586428314992528084017191)
      ·
        refine ⟨41379642472488792126025787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27586428314992528084017191 41379642472488792126025787)
        ·
          refine ⟨62069463708733188189038681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41379642472488792126025787 62069463708733188189038681)
          ·
            refine ⟨46552097781549891141779011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62069463708733188189038681 46552097781549891141779011)
            ·
              refine ⟨69828146672324836712668517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46552097781549891141779011 69828146672324836712668517)
              ·
                refine ⟨13092777501060906883625347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69828146672324836712668517 13092777501060906883625347)
                ·
                  refine ⟨19639166251591360325438021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13092777501060906883625347 19639166251591360325438021)
                  ·
                    refine ⟨3682343672173380061019629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19639166251591360325438021 3682343672173380061019629)
                    ·
                      refine ⟨1380878877065017522882361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682343672173380061019629 1380878877065017522882361)
                      ·
                        rfl

theorem cell23_2689252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_2689252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689252 prefixEnd_2689252 := by exact prefixLift 2689252
  have htrace : WordTrace (prefixWord ++ tailWord_2689252) baseStart_2689252 baseEnd_2689252 := by
    simpa [prefixWord, tailWord_2689252, baseEnd_2689252] using wordTrace_append hprefix tailTrace_2689252
  have hstable : (prefixWord ++ tailWord_2689252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689252).length < 2 ^ (prefixWord ++ tailWord_2689252).sum := by decide
  have hdescent : baseEnd_2689252 < baseStart_2689252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689266 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2689266 : Nat := 118140960795 + 2689266 * 2 ^ 59
def prefixEnd_2689266 : Nat := 4983230072969 + 3 ^ 40 * 2689266 * 2
def baseEnd_2689266 : Nat := 1380886065794180468107297

theorem tailTrace_2689266 : CollatzResearch.WordTrace tailWord_2689266 prefixEnd_2689266 1380886065794180468107297 := by
  unfold tailWord_2689266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521397268814011727989913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65390392716837364607973101 24521397268814011727989913)
  ·
    refine ⟨18391047951610508795992435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24521397268814011727989913 18391047951610508795992435)
    ·
      refine ⟨27586571927415763193988653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18391047951610508795992435 27586571927415763193988653)
      ·
        refine ⟨10344964472780911197745745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27586571927415763193988653 10344964472780911197745745)
        ·
          refine ⟨7758723354585683398309309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10344964472780911197745745 7758723354585683398309309)
          ·
            refine ⟨2909521257969631274365991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7758723354585683398309309 2909521257969631274365991)
            ·
              refine ⟨4364281886954446911548987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909521257969631274365991 4364281886954446911548987)
              ·
                refine ⟨6546422830431670367323481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364281886954446911548987 6546422830431670367323481)
                ·
                  refine ⟨4909817122823752775492611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546422830431670367323481 4909817122823752775492611)
                  ·
                    refine ⟨7364725684235629163238917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909817122823752775492611 7364725684235629163238917)
                    ·
                      refine ⟨1380886065794180468107297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7364725684235629163238917 1380886065794180468107297)
                      ·
                        rfl

theorem cell23_2689266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2689266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689266 prefixEnd_2689266 := by exact prefixLift 2689266
  have htrace : WordTrace (prefixWord ++ tailWord_2689266) baseStart_2689266 baseEnd_2689266 := by
    simpa [prefixWord, tailWord_2689266, baseEnd_2689266] using wordTrace_append hprefix tailTrace_2689266
  have hstable : (prefixWord ++ tailWord_2689266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689266).length < 2 ^ (prefixWord ++ tailWord_2689266).sum := by decide
  have hdescent : baseEnd_2689266 < baseStart_2689266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689275 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_2689275 : Nat := 118140960795 + 2689275 * 2 ^ 59
def prefixEnd_2689275 : Nat := 4983230072969 + 3 ^ 40 * 2689275 * 2
def baseEnd_2689275 : Nat := 1380890687120070932894755

theorem tailTrace_2689275 : CollatzResearch.WordTrace tailWord_2689275 prefixEnd_2689275 1380890687120070932894755 := by
  unfold tailWord_2689275
  simp only [CollatzResearch.WordTrace]
  refine ⟨98085917332223441449037279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65390611554815627632691519 98085917332223441449037279)
  ·
    refine ⟨147128875998335162173555919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98085917332223441449037279 147128875998335162173555919)
    ·
      refine ⟨220693313997502743260333879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147128875998335162173555919 220693313997502743260333879)
      ·
        refine ⟨331039970996254114890500819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220693313997502743260333879 331039970996254114890500819)
        ·
          refine ⟨496559956494381172335751229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331039970996254114890500819 496559956494381172335751229)
          ·
            refine ⟨186209983685392939625906711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496559956494381172335751229 186209983685392939625906711)
            ·
              refine ⟨279314975528089409438860067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186209983685392939625906711 279314975528089409438860067)
              ·
                refine ⟨418972463292134114158290101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279314975528089409438860067 418972463292134114158290101)
                ·
                  refine ⟨39278668433637573202339697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418972463292134114158290101 39278668433637573202339697)
                  ·
                    refine ⟨29459001325228179901754773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39278668433637573202339697 29459001325228179901754773)
                    ·
                      refine ⟨1380890687120070932894755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29459001325228179901754773 1380890687120070932894755)
                      ·
                        rfl

theorem cell23_2689275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_2689275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689275 prefixEnd_2689275 := by exact prefixLift 2689275
  have htrace : WordTrace (prefixWord ++ tailWord_2689275) baseStart_2689275 baseEnd_2689275 := by
    simpa [prefixWord, tailWord_2689275, baseEnd_2689275] using wordTrace_append hprefix tailTrace_2689275
  have hstable : (prefixWord ++ tailWord_2689275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689275).length < 2 ^ (prefixWord ++ tailWord_2689275).sum := by decide
  have hdescent : baseEnd_2689275 < baseStart_2689275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689276 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_2689276 : Nat := 118140960795 + 2689276 * 2 ^ 59
def prefixEnd_2689276 : Nat := 4983230072969 + 3 ^ 40 * 2689276 * 2
def baseEnd_2689276 : Nat := 460297066866908476327417

theorem tailTrace_2689276 : CollatzResearch.WordTrace tailWord_2689276 prefixEnd_2689276 460297066866908476327417 := by
  unfold tailWord_2689276
  simp only [CollatzResearch.WordTrace]
  refine ⟨49042976902609909309911841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65390635870146545746549121 49042976902609909309911841)
  ·
    refine ⟨36782232676957431982433881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49042976902609909309911841 36782232676957431982433881)
    ·
      refine ⟨27586674507718073986825411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36782232676957431982433881 27586674507718073986825411)
      ·
        refine ⟨41380011761577110980238117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27586674507718073986825411 41380011761577110980238117)
        ·
          refine ⟨7758752205295708308794647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41380011761577110980238117 7758752205295708308794647)
          ·
            refine ⟨11638128307943562463191971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7758752205295708308794647 11638128307943562463191971)
            ·
              refine ⟨17457192461915343694787957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638128307943562463191971 17457192461915343694787957)
              ·
                refine ⟨1636611793304563471386371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17457192461915343694787957 1636611793304563471386371)
                ·
                  refine ⟨2454917689956845207079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636611793304563471386371 2454917689956845207079557)
                  ·
                    refine ⟨460297066866908476327417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2454917689956845207079557 460297066866908476327417)
                    ·
                      rfl

theorem cell23_2689276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_2689276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689276 prefixEnd_2689276 := by exact prefixLift 2689276
  have htrace : WordTrace (prefixWord ++ tailWord_2689276) baseStart_2689276 baseEnd_2689276 := by
    simpa [prefixWord, tailWord_2689276, baseEnd_2689276] using wordTrace_append hprefix tailTrace_2689276
  have hstable : (prefixWord ++ tailWord_2689276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689276).length < 2 ^ (prefixWord ++ tailWord_2689276).sum := by decide
  have hdescent : baseEnd_2689276 < baseStart_2689276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689289 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 6]
def baseStart_2689289 : Nat := 118140960795 + 2689289 * 2 ^ 59
def prefixEnd_2689289 : Nat := 4983230072969 + 3 ^ 40 * 2689289 * 2
def baseEnd_2689289 : Nat := 153433097316581542013299

theorem tailTrace_2689289 : CollatzResearch.WordTrace tailWord_2689289 prefixEnd_2689289 153433097316581542013299 := by
  unfold tailWord_2689289
  simp only [CollatzResearch.WordTrace]
  refine ⟨98086427954172721840046921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65390951969448481226697947 98086427954172721840046921)
  ·
    refine ⟨73564820965629541380035191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98086427954172721840046921 73564820965629541380035191)
    ·
      refine ⟨110347231448444312070052787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73564820965629541380035191 110347231448444312070052787)
      ·
        refine ⟨165520847172666468105079181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110347231448444312070052787 165520847172666468105079181)
        ·
          refine ⟨62070317689749925539404693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165520847172666468105079181 62070317689749925539404693)
          ·
            refine ⟨2909546141707027759659595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62070317689749925539404693 2909546141707027759659595)
            ·
              refine ⟨4364319212560541639489393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909546141707027759659595 4364319212560541639489393)
              ·
                refine ⟨3273239409420406229617045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364319212560541639489393 3273239409420406229617045)
                ·
                  refine ⟨153433097316581542013299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3273239409420406229617045 153433097316581542013299)
                  ·
                    rfl

theorem cell23_2689289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 6].length) (baseStart_2689289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689289 prefixEnd_2689289 := by exact prefixLift 2689289
  have htrace : WordTrace (prefixWord ++ tailWord_2689289) baseStart_2689289 baseEnd_2689289 := by
    simpa [prefixWord, tailWord_2689289, baseEnd_2689289] using wordTrace_append hprefix tailTrace_2689289
  have hstable : (prefixWord ++ tailWord_2689289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689289).length < 2 ^ (prefixWord ++ tailWord_2689289).sum := by decide
  have hdescent : baseEnd_2689289 < baseStart_2689289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689306 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_2689306 : Nat := 118140960795 + 2689306 * 2 ^ 59
def prefixEnd_2689306 : Nat := 4983230072969 + 3 ^ 40 * 2689306 * 2
def baseEnd_2689306 : Nat := 153434067224484479067457

theorem tailTrace_2689306 : CollatzResearch.WordTrace tailWord_2689306 prefixEnd_2689306 153434067224484479067457 := by
  unfold tailWord_2689306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521761998777783435853943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65391365330074089162277181 24521761998777783435853943)
  ·
    refine ⟨36782642998166675153780915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24521761998777783435853943 36782642998166675153780915)
    ·
      refine ⟨55173964497250012730671373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36782642998166675153780915 55173964497250012730671373)
      ·
        refine ⟨20690236686468754774001765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55173964497250012730671373 20690236686468754774001765)
        ·
          refine ⟨3879419378712891520125331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20690236686468754774001765 3879419378712891520125331)
          ·
            refine ⟨5819129068069337280187997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879419378712891520125331 5819129068069337280187997)
            ·
              refine ⟨2182173400526001480070499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819129068069337280187997 2182173400526001480070499)
              ·
                refine ⟨3273260100789002220105749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182173400526001480070499 3273260100789002220105749)
                ·
                  refine ⟨153434067224484479067457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3273260100789002220105749 153434067224484479067457)
                  ·
                    rfl

theorem cell23_2689306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_2689306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689306 prefixEnd_2689306 := by exact prefixLift 2689306
  have htrace : WordTrace (prefixWord ++ tailWord_2689306) baseStart_2689306 baseEnd_2689306 := by
    simpa [prefixWord, tailWord_2689306, baseEnd_2689306] using wordTrace_append hprefix tailTrace_2689306
  have hstable : (prefixWord ++ tailWord_2689306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689306).length < 2 ^ (prefixWord ++ tailWord_2689306).sum := by decide
  have hdescent : baseEnd_2689306 < baseStart_2689306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689316 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2689316 : Nat := 118140960795 + 2689316 * 2 ^ 59
def prefixEnd_2689316 : Nat := 4983230072969 + 3 ^ 40 * 2689316 * 2
def baseEnd_2689316 : Nat := 1380911739826905272482067

theorem tailTrace_2689316 : CollatzResearch.WordTrace tailWord_2689316 prefixEnd_2689316 1380911739826905272482067 := by
  unfold tailWord_2689316
  simp only [CollatzResearch.WordTrace]
  refine ⟨49043706362537452725639901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65391608483383270300853201 49043706362537452725639901)
  ·
    refine ⟨18391389885951544772114963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49043706362537452725639901 18391389885951544772114963)
    ·
      refine ⟨27587084828927317158172445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18391389885951544772114963 27587084828927317158172445)
      ·
        refine ⟨10345156810847743934314667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27587084828927317158172445 10345156810847743934314667)
        ·
          refine ⟨15517735216271615901472001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345156810847743934314667 15517735216271615901472001)
          ·
            refine ⟨11638301412203711926104001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15517735216271615901472001 11638301412203711926104001)
            ·
              refine ⟨8728726059152783944578001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11638301412203711926104001 8728726059152783944578001)
              ·
                refine ⟨6546544544364587958433501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8728726059152783944578001 6546544544364587958433501)
                ·
                  refine ⟨2454954204136720484412563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6546544544364587958433501 2454954204136720484412563)
                  ·
                    refine ⟨3682431306205080726618845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2454954204136720484412563 3682431306205080726618845)
                    ·
                      refine ⟨1380911739826905272482067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682431306205080726618845 1380911739826905272482067)
                      ·
                        rfl

theorem cell23_2689316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2689316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689316 prefixEnd_2689316 := by exact prefixLift 2689316
  have htrace : WordTrace (prefixWord ++ tailWord_2689316) baseStart_2689316 baseEnd_2689316 := by
    simpa [prefixWord, tailWord_2689316, baseEnd_2689316] using wordTrace_append hprefix tailTrace_2689316
  have hstable : (prefixWord ++ tailWord_2689316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689316).length < 2 ^ (prefixWord ++ tailWord_2689316).sum := by decide
  have hdescent : baseEnd_2689316 < baseStart_2689316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689352 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2689352 : Nat := 118140960795 + 2689352 * 2 ^ 59
def prefixEnd_2689352 : Nat := 4983230072969 + 3 ^ 40 * 2689352 * 2
def baseEnd_2689352 : Nat := 1380930225130467131631901

theorem tailTrace_2689352 : CollatzResearch.WordTrace tailWord_2689352 prefixEnd_2689352 1380930225130467131631901 := by
  unfold tailWord_2689352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49044362876472241799795155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65392483835296322399726873 49044362876472241799795155)
  ·
    refine ⟨73566544314708362699692733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49044362876472241799795155 73566544314708362699692733)
    ·
      refine ⟨27587454118015636012384775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73566544314708362699692733 27587454118015636012384775)
      ·
        refine ⟨41381181177023454018577163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27587454118015636012384775 41381181177023454018577163)
        ·
          refine ⟨62071771765535181027865745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41381181177023454018577163 62071771765535181027865745)
          ·
            refine ⟨46553828824151385770899309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62071771765535181027865745 46553828824151385770899309)
            ·
              refine ⟨17457685809056769664087241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46553828824151385770899309 17457685809056769664087241)
              ·
                refine ⟨13093264356792577248065431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17457685809056769664087241 13093264356792577248065431)
                ·
                  refine ⟨19639896535188865872098147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13093264356792577248065431 19639896535188865872098147)
                  ·
                    refine ⟨29459844802783298808147221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19639896535188865872098147 29459844802783298808147221)
                    ·
                      refine ⟨1380930225130467131631901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29459844802783298808147221 1380930225130467131631901)
                      ·
                        rfl

theorem cell23_2689352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2689352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689352 prefixEnd_2689352 := by exact prefixLift 2689352
  have htrace : WordTrace (prefixWord ++ tailWord_2689352) baseStart_2689352 baseEnd_2689352 := by
    simpa [prefixWord, tailWord_2689352, baseEnd_2689352] using wordTrace_append hprefix tailTrace_2689352
  have hstable : (prefixWord ++ tailWord_2689352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689352).length < 2 ^ (prefixWord ++ tailWord_2689352).sum := by decide
  have hdescent : baseEnd_2689352 < baseStart_2689352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689362 : List Nat := [3, 2, 2, 1, 1, 1, 3, 10]
def baseStart_2689362 : Nat := 118140960795 + 2689362 * 2 ^ 59
def prefixEnd_2689362 : Nat := 4983230072969 + 3 ^ 40 * 2689362 * 2
def baseEnd_2689362 : Nat := 51145754071741188611365

theorem tailTrace_2689362 : CollatzResearch.WordTrace tailWord_2689362 prefixEnd_2689362 51145754071741188611365 := by
  unfold tailWord_2689362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522272620727063826863585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65392726988605503538302893 24522272620727063826863585)
  ·
    refine ⟨18391704465545297870147689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24522272620727063826863585 18391704465545297870147689)
    ·
      refine ⟨13793778349158973402610767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18391704465545297870147689 13793778349158973402610767)
      ·
        refine ⟨20690667523738460103916151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13793778349158973402610767 20690667523738460103916151)
        ·
          refine ⟨31036001285607690155874227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20690667523738460103916151 31036001285607690155874227)
          ·
            refine ⟨46554001928411535233811341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31036001285607690155874227 46554001928411535233811341)
            ·
              refine ⟨17457750723154325712679253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46554001928411535233811341 17457750723154325712679253)
              ·
                refine ⟨51145754071741188611365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17457750723154325712679253 51145754071741188611365)
                ·
                  rfl

theorem cell23_2689362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_2689362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689362 prefixEnd_2689362 := by exact prefixLift 2689362
  have htrace : WordTrace (prefixWord ++ tailWord_2689362) baseStart_2689362 baseEnd_2689362 := by
    simpa [prefixWord, tailWord_2689362, baseEnd_2689362] using wordTrace_append hprefix tailTrace_2689362
  have hstable : (prefixWord ++ tailWord_2689362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689362).length < 2 ^ (prefixWord ++ tailWord_2689362).sum := by decide
  have hdescent : baseEnd_2689362 < baseStart_2689362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689376 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_2689376 : Nat := 118140960795 + 2689376 * 2 ^ 59
def prefixEnd_2689376 : Nat := 4983230072969 + 3 ^ 40 * 2689376 * 2
def baseEnd_2689376 : Nat := 1380942548666175037731791

theorem tailTrace_2689376 : CollatzResearch.WordTrace tailWord_2689376 prefixEnd_2689376 1380942548666175037731791 := by
  unfold tailWord_2689376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49044800552428767849231991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65393067403238357132309321 49044800552428767849231991)
  ·
    refine ⟨73567200828643151773847987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49044800552428767849231991 73567200828643151773847987)
    ·
      refine ⟨110350801242964727660771981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73567200828643151773847987 110350801242964727660771981)
      ·
        refine ⟨41381550466111772872789493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110350801242964727660771981 41381550466111772872789493)
        ·
          refine ⟨3879520356197978706824015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41381550466111772872789493 3879520356197978706824015)
          ·
            refine ⟨5819280534296968060236023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879520356197978706824015 5819280534296968060236023)
            ·
              refine ⟨8728920801445452090354035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819280534296968060236023 8728920801445452090354035)
              ·
                refine ⟨13093381202168178135531053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728920801445452090354035 13093381202168178135531053)
                ·
                  refine ⟨4910017950813066800824145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13093381202168178135531053 4910017950813066800824145)
                  ·
                    refine ⟨3682513463109800100618109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910017950813066800824145 3682513463109800100618109)
                    ·
                      refine ⟨1380942548666175037731791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3682513463109800100618109 1380942548666175037731791)
                      ·
                        rfl

theorem cell23_2689376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_2689376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689376 prefixEnd_2689376 := by exact prefixLift 2689376
  have htrace : WordTrace (prefixWord ++ tailWord_2689376) baseStart_2689376 baseEnd_2689376 := by
    simpa [prefixWord, tailWord_2689376, baseEnd_2689376] using wordTrace_append hprefix tailTrace_2689376
  have hstable : (prefixWord ++ tailWord_2689376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689376).length < 2 ^ (prefixWord ++ tailWord_2689376).sum := by decide
  have hdescent : baseEnd_2689376 < baseStart_2689376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689386 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2689386 : Nat := 118140960795 + 2689386 * 2 ^ 59
def prefixEnd_2689386 : Nat := 4983230072969 + 3 ^ 40 * 2689386 * 2
def baseEnd_2689386 : Nat := 1380947683472719998606745

theorem tailTrace_2689386 : CollatzResearch.WordTrace tailWord_2689386 prefixEnd_2689386 1380947683472719998606745 := by
  unfold tailWord_2689386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522491458705326851582003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65393310556547538270885341 24522491458705326851582003)
  ·
    refine ⟨36783737188057990277373005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24522491458705326851582003 36783737188057990277373005)
    ·
      refine ⟨13793901445521746354014877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36783737188057990277373005 13793901445521746354014877)
      ·
        refine ⟨5172713042070654882755579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13793901445521746354014877 5172713042070654882755579)
        ·
          refine ⟨7759069563105982324133369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172713042070654882755579 7759069563105982324133369)
          ·
            refine ⟨5819302172329486743100027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7759069563105982324133369 5819302172329486743100027)
            ·
              refine ⟨8728953258494230114650041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819302172329486743100027 8728953258494230114650041)
              ·
                refine ⟨6546714943870672585987531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8728953258494230114650041 6546714943870672585987531)
                ·
                  refine ⟨9820072415806008878981297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546714943870672585987531 9820072415806008878981297)
                  ·
                    refine ⟨7365054311854506659235973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9820072415806008878981297 7365054311854506659235973)
                    ·
                      refine ⟨1380947683472719998606745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7365054311854506659235973 1380947683472719998606745)
                      ·
                        rfl

theorem cell23_2689386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2689386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689386 prefixEnd_2689386 := by exact prefixLift 2689386
  have htrace : WordTrace (prefixWord ++ tailWord_2689386) baseStart_2689386 baseEnd_2689386 := by
    simpa [prefixWord, tailWord_2689386, baseEnd_2689386] using wordTrace_append hprefix tailTrace_2689386
  have hstable : (prefixWord ++ tailWord_2689386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689386).length < 2 ^ (prefixWord ++ tailWord_2689386).sum := by decide
  have hdescent : baseEnd_2689386 < baseStart_2689386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689409 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2689409 : Nat := 118140960795 + 2689409 * 2 ^ 59
def prefixEnd_2689409 : Nat := 4983230072969 + 3 ^ 40 * 2689409 * 2
def baseEnd_2689409 : Nat := 460319831175924469539713

theorem tailTrace_2689409 : CollatzResearch.WordTrace tailWord_2689409 prefixEnd_2689409 460319831175924469539713 := by
  unfold tailWord_2689409
  simp only [CollatzResearch.WordTrace]
  refine ⟨98090804713737982334415281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65393869809158654889610187 98090804713737982334415281)
  ·
    refine ⟨73568103535303486750811461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98090804713737982334415281 73568103535303486750811461)
    ·
      refine ⟨13794019412869403765777149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73568103535303486750811461 13794019412869403765777149)
      ·
        refine ⟨5172757279826026412166431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13794019412869403765777149 5172757279826026412166431)
        ·
          refine ⟨7759135919739039618249647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172757279826026412166431 7759135919739039618249647)
          ·
            refine ⟨11638703879608559427374471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7759135919739039618249647 11638703879608559427374471)
            ·
              refine ⟨17458055819412839141061707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638703879608559427374471 17458055819412839141061707)
              ·
                refine ⟨26187083729119258711592561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17458055819412839141061707 26187083729119258711592561)
                ·
                  refine ⟨19640312796839444033694421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26187083729119258711592561 19640312796839444033694421)
                  ·
                    refine ⟨460319831175924469539713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19640312796839444033694421 460319831175924469539713)
                    ·
                      rfl

theorem cell23_2689409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2689409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689409 prefixEnd_2689409 := by exact prefixLift 2689409
  have htrace : WordTrace (prefixWord ++ tailWord_2689409) baseStart_2689409 baseEnd_2689409 := by
    simpa [prefixWord, tailWord_2689409, baseEnd_2689409] using wordTrace_append hprefix tailTrace_2689409
  have hstable : (prefixWord ++ tailWord_2689409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689409).length < 2 ^ (prefixWord ++ tailWord_2689409).sum := by decide
  have hdescent : baseEnd_2689409 < baseStart_2689409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689416 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2689416 : Nat := 118140960795 + 2689416 * 2 ^ 59
def prefixEnd_2689416 : Nat := 4983230072969 + 3 ^ 40 * 2689416 * 2
def baseEnd_2689416 : Nat := 1380963087892354881231607

theorem tailTrace_2689416 : CollatzResearch.WordTrace tailWord_2689416 prefixEnd_2689416 1380963087892354881231607 := by
  unfold tailWord_2689416
  simp only [CollatzResearch.WordTrace]
  refine ⟨49045530012356311264960051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65394040016475081686613401 49045530012356311264960051)
  ·
    refine ⟨73568295018534466897440077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49045530012356311264960051 73568295018534466897440077)
    ·
      refine ⟨27588110631950425086540029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73568295018534466897440077 27588110631950425086540029)
      ·
        refine ⟨10345541486981409407452511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27588110631950425086540029 10345541486981409407452511)
        ·
          refine ⟨15518312230472114111178767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345541486981409407452511 15518312230472114111178767)
          ·
            refine ⟨23277468345708171166768151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518312230472114111178767 23277468345708171166768151)
            ·
              refine ⟨34916202518562256750152227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23277468345708171166768151 34916202518562256750152227)
              ·
                refine ⟨52374303777843385125228341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34916202518562256750152227 52374303777843385125228341)
                ·
                  refine ⟨4910090979172817355490157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52374303777843385125228341 4910090979172817355490157)
                  ·
                    refine ⟨1841284117189806508308809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4910090979172817355490157 1841284117189806508308809)
                    ·
                      refine ⟨1380963087892354881231607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841284117189806508308809 1380963087892354881231607)
                      ·
                        rfl

theorem cell23_2689416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2689416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689416 prefixEnd_2689416 := by exact prefixLift 2689416
  have htrace : WordTrace (prefixWord ++ tailWord_2689416) baseStart_2689416 baseEnd_2689416 := by
    simpa [prefixWord, tailWord_2689416, baseEnd_2689416] using wordTrace_append hprefix tailTrace_2689416
  have hstable : (prefixWord ++ tailWord_2689416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689416).length < 2 ^ (prefixWord ++ tailWord_2689416).sum := by decide
  have hdescent : baseEnd_2689416 < baseStart_2689416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689452 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 11]
def baseStart_2689452 : Nat := 118140960795 + 2689452 * 2 ^ 59
def prefixEnd_2689452 : Nat := 4983230072969 + 3 ^ 40 * 2689452 * 2
def baseEnd_2689452 : Nat := 153442397021768526709049

theorem tailTrace_2689452 : CollatzResearch.WordTrace tailWord_2689452 prefixEnd_2689452 153442397021768526709049 := by
  unfold tailWord_2689452
  simp only [CollatzResearch.WordTrace]
  refine ⟨49046186526291100339115305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65394915368388133785487073 49046186526291100339115305)
  ·
    refine ⟨36784639894718325254336479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49046186526291100339115305 36784639894718325254336479)
    ·
      refine ⟨55176959842077487881504719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36784639894718325254336479 55176959842077487881504719)
      ·
        refine ⟨82765439763116231822257079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55176959842077487881504719 82765439763116231822257079)
        ·
          refine ⟨124148159644674347733385619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82765439763116231822257079 124148159644674347733385619)
          ·
            refine ⟨186222239467011521600078429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124148159644674347733385619 186222239467011521600078429)
            ·
              refine ⟨69833339800129320600029411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186222239467011521600078429 69833339800129320600029411)
              ·
                refine ⟨104750009700193980900044117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69833339800129320600029411 104750009700193980900044117)
                ·
                  refine ⟨153442397021768526709049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 104750009700193980900044117 153442397021768526709049)
                  ·
                    rfl

theorem cell23_2689452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_2689452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689452 prefixEnd_2689452 := by exact prefixLift 2689452
  have htrace : WordTrace (prefixWord ++ tailWord_2689452) baseStart_2689452 baseEnd_2689452 := by
    simpa [prefixWord, tailWord_2689452, baseEnd_2689452] using wordTrace_append hprefix tailTrace_2689452
  have hstable : (prefixWord ++ tailWord_2689452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689452).length < 2 ^ (prefixWord ++ tailWord_2689452).sum := by decide
  have hdescent : baseEnd_2689452 < baseStart_2689452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689463 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 4, 2, 2]
def baseStart_2689463 : Nat := 118140960795 + 2689463 * 2 ^ 59
def prefixEnd_2689463 : Nat := 4983230072969 + 3 ^ 40 * 2689463 * 2
def baseEnd_2689463 : Nat := 1380987221483116197343891

theorem tailTrace_2689463 : CollatzResearch.WordTrace tailWord_2689463 prefixEnd_2689463 1380987221483116197343891 := by
  unfold tailWord_2689463
  simp only [CollatzResearch.WordTrace]
  refine ⟨98092774255542349556881043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65395182837028233037920695 98092774255542349556881043)
  ·
    refine ⟨147139161383313524335321565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98092774255542349556881043 147139161383313524335321565)
    ·
      refine ⟨55177185518742571625745587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147139161383313524335321565 55177185518742571625745587)
      ·
        refine ⟨82765778278113857438618381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55177185518742571625745587 82765778278113857438618381)
        ·
          refine ⟨31037166854292696539481893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82765778278113857438618381 31037166854292696539481893)
          ·
            refine ⟨5819468785179880601152855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31037166854292696539481893 5819468785179880601152855)
            ·
              refine ⟨8729203177769820901729283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819468785179880601152855 8729203177769820901729283)
              ·
                refine ⟨13093804766654731352593925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729203177769820901729283 13093804766654731352593925)
                ·
                  refine ⟨2455088393747762128611361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13093804766654731352593925 2455088393747762128611361)
                  ·
                    refine ⟨1841316295310821596458521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455088393747762128611361 1841316295310821596458521)
                    ·
                      refine ⟨1380987221483116197343891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841316295310821596458521 1380987221483116197343891)
                      ·
                        rfl

theorem cell23_2689463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 2, 2].length) (baseStart_2689463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689463 prefixEnd_2689463 := by exact prefixLift 2689463
  have htrace : WordTrace (prefixWord ++ tailWord_2689463) baseStart_2689463 baseEnd_2689463 := by
    simpa [prefixWord, tailWord_2689463, baseEnd_2689463] using wordTrace_append hprefix tailTrace_2689463
  have hstable : (prefixWord ++ tailWord_2689463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689463).length < 2 ^ (prefixWord ++ tailWord_2689463).sum := by decide
  have hdescent : baseEnd_2689463 < baseStart_2689463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689469 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 7]
def baseStart_2689469 : Nat := 118140960795 + 2689469 * 2 ^ 59
def prefixEnd_2689469 : Nat := 4983230072969 + 3 ^ 40 * 2689469 * 2
def baseEnd_2689469 : Nat := 153443366929671463763207

theorem tailTrace_2689469 : CollatzResearch.WordTrace tailWord_2689469 prefixEnd_2689469 153443366929671463763207 := by
  unfold tailWord_2689469
  simp only [CollatzResearch.WordTrace]
  refine ⟨98092993093520612581599461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65395328729013741721066307 98092993093520612581599461)
  ·
    refine ⟨18392436205035114859049899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98092993093520612581599461 18392436205035114859049899)
    ·
      refine ⟨27588654307552672288574849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392436205035114859049899 27588654307552672288574849)
      ·
        refine ⟨20691490730664504216431137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27588654307552672288574849 20691490730664504216431137)
        ·
          refine ⟨15518618047998378162323353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20691490730664504216431137 15518618047998378162323353)
          ·
            refine ⟨11638963535998783621742515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15518618047998378162323353 11638963535998783621742515)
            ·
              refine ⟨17458445303998175432613773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638963535998783621742515 17458445303998175432613773)
              ·
                refine ⟨6546916988999315787230165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17458445303998175432613773 6546916988999315787230165)
                ·
                  refine ⟨153443366929671463763207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6546916988999315787230165 153443366929671463763207)
                  ·
                    rfl

theorem cell23_2689469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_2689469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689469 prefixEnd_2689469 := by exact prefixLift 2689469
  have htrace : WordTrace (prefixWord ++ tailWord_2689469) baseStart_2689469 baseEnd_2689469 := by
    simpa [prefixWord, tailWord_2689469, baseEnd_2689469] using wordTrace_append hprefix tailTrace_2689469
  have hstable : (prefixWord ++ tailWord_2689469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689469).length < 2 ^ (prefixWord ++ tailWord_2689469).sum := by decide
  have hdescent : baseEnd_2689469 < baseStart_2689469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689503 : List Nat := [1, 1, 2, 3, 3, 4, 1, 3, 5]
def baseStart_2689503 : Nat := 118140960795 + 2689503 * 2 ^ 59
def prefixEnd_2689503 : Nat := 4983230072969 + 3 ^ 40 * 2689503 * 2
def baseEnd_2689503 : Nat := 153445306745477337871523

theorem tailTrace_2689503 : CollatzResearch.WordTrace tailWord_2689503 prefixEnd_2689503 153445306745477337871523 := by
  unfold tailWord_2689503
  simp only [CollatzResearch.WordTrace]
  refine ⟨98094233175397436388337163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65396155450264957592224775 98094233175397436388337163)
  ·
    refine ⟨147141349763096154582505745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98094233175397436388337163 147141349763096154582505745)
    ·
      refine ⟨110356012322322115936879309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147141349763096154582505745 110356012322322115936879309)
      ·
        refine ⟨41383504620870793476329741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110356012322322115936879309 41383504620870793476329741)
        ·
          refine ⟨15518814232826547553623653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41383504620870793476329741 15518814232826547553623653)
          ·
            refine ⟨2909777668654977666304435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15518814232826547553623653 2909777668654977666304435)
            ·
              refine ⟨4364666502982466499456653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909777668654977666304435 4364666502982466499456653)
              ·
                refine ⟨1636749938618424937296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364666502982466499456653 1636749938618424937296245)
                ·
                  refine ⟨153445306745477337871523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1636749938618424937296245 153445306745477337871523)
                  ·
                    rfl

theorem cell23_2689503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 5].length) (baseStart_2689503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689503 prefixEnd_2689503 := by exact prefixLift 2689503
  have htrace : WordTrace (prefixWord ++ tailWord_2689503) baseStart_2689503 baseEnd_2689503 := by
    simpa [prefixWord, tailWord_2689503, baseEnd_2689503] using wordTrace_append hprefix tailTrace_2689503
  have hstable : (prefixWord ++ tailWord_2689503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689503).length < 2 ^ (prefixWord ++ tailWord_2689503).sum := by decide
  have hdescent : baseEnd_2689503 < baseStart_2689503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689526 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2689526 : Nat := 118140960795 + 2689526 * 2 ^ 59
def prefixEnd_2689526 : Nat := 4983230072969 + 3 ^ 40 * 2689526 * 2
def baseEnd_2689526 : Nat := 1381019570764349450856101

theorem tailTrace_2689526 : CollatzResearch.WordTrace tailWord_2689526 prefixEnd_2689526 1381019570764349450856101 := by
  unfold tailWord_2689526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130942003394631957276527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65396714702876074210949621 6130942003394631957276527)
  ·
    refine ⟨9196413005091947935914791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6130942003394631957276527 9196413005091947935914791)
    ·
      refine ⟨13794619507637921903872187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9196413005091947935914791 13794619507637921903872187)
      ·
        refine ⟨20691929261456882855808281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794619507637921903872187 20691929261456882855808281)
        ·
          refine ⟨15518946946092662141856211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20691929261456882855808281 15518946946092662141856211)
          ·
            refine ⟨23278420419138993212784317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518946946092662141856211 23278420419138993212784317)
            ·
              refine ⟨8729407657177122454794119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23278420419138993212784317 8729407657177122454794119)
              ·
                refine ⟨13094111485765683682191179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729407657177122454794119 13094111485765683682191179)
                ·
                  refine ⟨19641167228648525523286769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13094111485765683682191179 19641167228648525523286769)
                  ·
                    refine ⟨14730875421486394142465077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19641167228648525523286769 14730875421486394142465077)
                    ·
                      refine ⟨1381019570764349450856101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14730875421486394142465077 1381019570764349450856101)
                      ·
                        rfl

theorem cell23_2689526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2689526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689526 prefixEnd_2689526 := by exact prefixLift 2689526
  have htrace : WordTrace (prefixWord ++ tailWord_2689526) baseStart_2689526 baseEnd_2689526 := by
    simpa [prefixWord, tailWord_2689526, baseEnd_2689526] using wordTrace_append hprefix tailTrace_2689526
  have hstable : (prefixWord ++ tailWord_2689526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689526).length < 2 ^ (prefixWord ++ tailWord_2689526).sum := by decide
  have hdescent : baseEnd_2689526 < baseStart_2689526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689546 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_2689546 : Nat := 118140960795 + 2689546 * 2 ^ 59
def prefixEnd_2689546 : Nat := 4983230072969 + 3 ^ 40 * 2689546 * 2
def baseEnd_2689546 : Nat := 460343280125813124202003

theorem tailTrace_2689546 : CollatzResearch.WordTrace tailWord_2689546 prefixEnd_2689546 460343280125813124202003 := by
  unfold tailWord_2689546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24523950378560413683038123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65397201009494436488101661 24523950378560413683038123)
  ·
    refine ⟨36785925567840620524557185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24523950378560413683038123 36785925567840620524557185)
    ·
      refine ⟨27589444175880465393417889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36785925567840620524557185 27589444175880465393417889)
      ·
        refine ⟨20692083131910349045063417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27589444175880465393417889 20692083131910349045063417)
        ·
          refine ⟨15519062348932761783797563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20692083131910349045063417 15519062348932761783797563)
          ·
            refine ⟨23278593523399142675696345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15519062348932761783797563 23278593523399142675696345)
            ·
              refine ⟨17458945142549357006772259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23278593523399142675696345 17458945142549357006772259)
              ·
                refine ⟨26188417713824035510158389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17458945142549357006772259 26188417713824035510158389)
                ·
                  refine ⟨2455164160671003329077349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26188417713824035510158389 2455164160671003329077349)
                  ·
                    refine ⟨460343280125813124202003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455164160671003329077349 460343280125813124202003)
                    ·
                      rfl

theorem cell23_2689546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_2689546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689546 prefixEnd_2689546 := by exact prefixLift 2689546
  have htrace : WordTrace (prefixWord ++ tailWord_2689546) baseStart_2689546 baseEnd_2689546 := by
    simpa [prefixWord, tailWord_2689546, baseEnd_2689546] using wordTrace_append hprefix tailTrace_2689546
  have hstable : (prefixWord ++ tailWord_2689546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689546).length < 2 ^ (prefixWord ++ tailWord_2689546).sum := by decide
  have hdescent : baseEnd_2689546 < baseStart_2689546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689599 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2689599 : Nat := 118140960795 + 2689599 * 2 ^ 59
def prefixEnd_2689599 : Nat := 4983230072969 + 3 ^ 40 * 2689599 * 2
def baseEnd_2689599 : Nat := 1381057054852127665243265

theorem tailTrace_2689599 : CollatzResearch.WordTrace tailWord_2689599 prefixEnd_2689599 1381057054852127665243265 := by
  unfold tailWord_2689599
  simp only [CollatzResearch.WordTrace]
  refine ⟨98097734583049644783831851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65398489722033096522554567 98097734583049644783831851)
  ·
    refine ⟨147146601874574467175747777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98097734583049644783831851 147146601874574467175747777)
    ·
      refine ⟨110359951405930850381810833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147146601874574467175747777 110359951405930850381810833)
      ·
        refine ⟨82769963554448137786358125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110359951405930850381810833 82769963554448137786358125)
        ·
          refine ⟨31038736332918051669884297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82769963554448137786358125 31038736332918051669884297)
          ·
            refine ⟨23279052249688538752413223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31038736332918051669884297 23279052249688538752413223)
            ·
              refine ⟨34918578374532808128619835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23279052249688538752413223 34918578374532808128619835)
              ·
                refine ⟨52377867561799212192929753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34918578374532808128619835 52377867561799212192929753)
                ·
                  refine ⟨39283400671349409144697315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52377867561799212192929753 39283400671349409144697315)
                  ·
                    refine ⟨58925101007024113717045973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39283400671349409144697315 58925101007024113717045973)
                    ·
                      refine ⟨1381057054852127665243265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58925101007024113717045973 1381057054852127665243265)
                      ·
                        rfl

theorem cell23_2689599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2689599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689599 prefixEnd_2689599 := by exact prefixLift 2689599
  have htrace : WordTrace (prefixWord ++ tailWord_2689599) baseStart_2689599 baseEnd_2689599 := by
    simpa [prefixWord, tailWord_2689599, baseEnd_2689599] using wordTrace_append hprefix tailTrace_2689599
  have hstable : (prefixWord ++ tailWord_2689599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689599).length < 2 ^ (prefixWord ++ tailWord_2689599).sum := by decide
  have hdescent : baseEnd_2689599 < baseStart_2689599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689604 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2689604 : Nat := 118140960795 + 2689604 * 2 ^ 59
def prefixEnd_2689604 : Nat := 4983230072969 + 3 ^ 40 * 2689604 * 2
def baseEnd_2689604 : Nat := 1381059622255400145680743

theorem tailTrace_2689604 : CollatzResearch.WordTrace tailWord_2689604 prefixEnd_2689604 1381059622255400145680743 := by
  unfold tailWord_2689604
  simp only [CollatzResearch.WordTrace]
  refine ⟨49048958474015765318881933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65398611298687687091842577 49048958474015765318881933)
  ·
    refine ⟨18393359427755911994580725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49048958474015765318881933 18393359427755911994580725)
    ·
      refine ⟨1724377446352116749491943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18393359427755911994580725 1724377446352116749491943)
      ·
        refine ⟨2586566169528175124237915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724377446352116749491943 2586566169528175124237915)
        ·
          refine ⟨3879849254292262686356873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586566169528175124237915 3879849254292262686356873)
          ·
            refine ⟨2909886940719197014767655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879849254292262686356873 2909886940719197014767655)
            ·
              refine ⟨4364830411078795522151483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909886940719197014767655 4364830411078795522151483)
              ·
                refine ⟨6547245616618193283227225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364830411078795522151483 6547245616618193283227225)
                ·
                  refine ⟨4910434212463644962420419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547245616618193283227225 4910434212463644962420419)
                  ·
                    refine ⟨7365651318695467443630629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910434212463644962420419 7365651318695467443630629)
                    ·
                      refine ⟨1381059622255400145680743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7365651318695467443630629 1381059622255400145680743)
                      ·
                        rfl

theorem cell23_2689604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2689604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689604 prefixEnd_2689604 := by exact prefixLift 2689604
  have htrace : WordTrace (prefixWord ++ tailWord_2689604) baseStart_2689604 baseEnd_2689604 := by
    simpa [prefixWord, tailWord_2689604, baseEnd_2689604] using wordTrace_append hprefix tailTrace_2689604
  have hstable : (prefixWord ++ tailWord_2689604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689604).length < 2 ^ (prefixWord ++ tailWord_2689604).sum := by decide
  have hdescent : baseEnd_2689604 < baseStart_2689604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689660 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_2689660 : Nat := 118140960795 + 2689660 * 2 ^ 59
def prefixEnd_2689660 : Nat := 4983230072969 + 3 ^ 40 * 2689660 * 2
def baseEnd_2689660 : Nat := 1381088377172051926580485

theorem tailTrace_2689660 : CollatzResearch.WordTrace tailWord_2689660 prefixEnd_2689660 1381088377172051926580485 := by
  unfold tailWord_2689660
  simp only [CollatzResearch.WordTrace]
  refine ⟨49049979717914326100901217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65399972957219101467868289 49049979717914326100901217)
  ·
    refine ⟨36787484788435744575675913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49049979717914326100901217 36787484788435744575675913)
    ·
      refine ⟨27590613591326808431756935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36787484788435744575675913 27590613591326808431756935)
      ·
        refine ⟨41385920386990212647635403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27590613591326808431756935 41385920386990212647635403)
        ·
          refine ⟨62078880580485318971453105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41385920386990212647635403 62078880580485318971453105)
          ·
            refine ⟨46559160435363989228589829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62078880580485318971453105 46559160435363989228589829)
            ·
              refine ⟨8729842581630747980360593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46559160435363989228589829 8729842581630747980360593)
              ·
                refine ⟨6547381936223060985270445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8729842581630747980360593 6547381936223060985270445)
                ·
                  refine ⟨2455268226083647869476417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6547381936223060985270445 2455268226083647869476417)
                  ·
                    refine ⟨1841451169562735902107313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455268226083647869476417 1841451169562735902107313)
                    ·
                      refine ⟨1381088377172051926580485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841451169562735902107313 1381088377172051926580485)
                      ·
                        rfl

theorem cell23_2689660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_2689660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689660 prefixEnd_2689660 := by exact prefixLift 2689660
  have htrace : WordTrace (prefixWord ++ tailWord_2689660) baseStart_2689660 baseEnd_2689660 := by
    simpa [prefixWord, tailWord_2689660, baseEnd_2689660] using wordTrace_append hprefix tailTrace_2689660
  have hstable : (prefixWord ++ tailWord_2689660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689660).length < 2 ^ (prefixWord ++ tailWord_2689660).sum := by decide
  have hdescent : baseEnd_2689660 < baseStart_2689660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689763 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2689763 : Nat := 118140960795 + 2689763 * 2 ^ 59
def prefixEnd_2689763 : Nat := 4983230072969 + 3 ^ 40 * 2689763 * 2
def baseEnd_2689763 : Nat := 1381141265679465023592511

theorem tailTrace_2689763 : CollatzResearch.WordTrace tailWord_2689763 prefixEnd_2689763 1381141265679465023592511 := by
  unfold tailWord_2689763
  simp only [CollatzResearch.WordTrace]
  refine ⟨98103716154455500792801943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65402477436303667195201295 98103716154455500792801943)
  ·
    refine ⟨147155574231683251189202915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98103716154455500792801943 147155574231683251189202915)
    ·
      refine ⟨220733361347524876783804373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147155574231683251189202915 220733361347524876783804373)
      ·
        refine ⟨5173438156582614299620415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 220733361347524876783804373 5173438156582614299620415)
        ·
          refine ⟨7760157234873921449430623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173438156582614299620415 7760157234873921449430623)
          ·
            refine ⟨11640235852310882174145935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760157234873921449430623 11640235852310882174145935)
            ·
              refine ⟨17460353778466323261218903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640235852310882174145935 17460353778466323261218903)
              ·
                refine ⟨26190530667699484891828355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460353778466323261218903 26190530667699484891828355)
                ·
                  refine ⟨39285796001549227337742533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26190530667699484891828355 39285796001549227337742533)
                  ·
                    refine ⟨7366086750290480125826725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39285796001549227337742533 7366086750290480125826725)
                    ·
                      refine ⟨1381141265679465023592511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7366086750290480125826725 1381141265679465023592511)
                      ·
                        rfl

theorem cell23_2689763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2689763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689763 prefixEnd_2689763 := by exact prefixLift 2689763
  have htrace : WordTrace (prefixWord ++ tailWord_2689763) baseStart_2689763 baseEnd_2689763 := by
    simpa [prefixWord, tailWord_2689763, baseEnd_2689763] using wordTrace_append hprefix tailTrace_2689763
  have hstable : (prefixWord ++ tailWord_2689763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689763).length < 2 ^ (prefixWord ++ tailWord_2689763).sum := by decide
  have hdescent : baseEnd_2689763 < baseStart_2689763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689773 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2689773 : Nat := 118140960795 + 2689773 * 2 ^ 59
def prefixEnd_2689773 : Nat := 4983230072969 + 3 ^ 40 * 2689773 * 2
def baseEnd_2689773 : Nat := 153460711165112220496385

theorem tailTrace_2689773 : CollatzResearch.WordTrace tailWord_2689773 prefixEnd_2689773 153460711165112220496385 := by
  unfold tailWord_2689773
  simp only [CollatzResearch.WordTrace]
  refine ⟨98104080884419272500665973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65402720589612848333777315 98104080884419272500665973)
  ·
    refine ⟨9197257582914306796937435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98104080884419272500665973 9197257582914306796937435)
    ·
      refine ⟨13795886374371460195406153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9197257582914306796937435 13795886374371460195406153)
      ·
        refine ⟨10346914780778595146554615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13795886374371460195406153 10346914780778595146554615)
        ·
          refine ⟨15520372171167892719831923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10346914780778595146554615 15520372171167892719831923)
          ·
            refine ⟨23280558256751839079747885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15520372171167892719831923 23280558256751839079747885)
            ·
              refine ⟨8730209346281939654905457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23280558256751839079747885 8730209346281939654905457)
              ·
                refine ⟨6547657009711454741179093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8730209346281939654905457 6547657009711454741179093)
                ·
                  refine ⟨153460711165112220496385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6547657009711454741179093 153460711165112220496385)
                  ·
                    rfl

theorem cell23_2689773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2689773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689773 prefixEnd_2689773 := by exact prefixLift 2689773
  have htrace : WordTrace (prefixWord ++ tailWord_2689773) baseStart_2689773 baseEnd_2689773 := by
    simpa [prefixWord, tailWord_2689773, baseEnd_2689773] using wordTrace_append hprefix tailTrace_2689773
  have hstable : (prefixWord ++ tailWord_2689773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689773).length < 2 ^ (prefixWord ++ tailWord_2689773).sum := by decide
  have hdescent : baseEnd_2689773 < baseStart_2689773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689823 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2689823 : Nat := 118140960795 + 2689823 * 2 ^ 59
def prefixEnd_2689823 : Nat := 4983230072969 + 3 ^ 40 * 2689823 * 2
def baseEnd_2689823 : Nat := 1381172074518734788842235

theorem tailTrace_2689823 : CollatzResearch.WordTrace tailWord_2689823 prefixEnd_2689823 1381172074518734788842235 := by
  unfold tailWord_2689823
  simp only [CollatzResearch.WordTrace]
  refine ⟨98105904534238131039986123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65403936356158754026657415 98105904534238131039986123)
  ·
    refine ⟨147158856801357196559979185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98105904534238131039986123 147158856801357196559979185)
    ·
      refine ⟨110369142601017897419984389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147158856801357196559979185 110369142601017897419984389)
      ·
        refine ⟨20694214237690855766247073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110369142601017897419984389 20694214237690855766247073)
        ·
          refine ⟨15520660678268141824685305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20694214237690855766247073 15520660678268141824685305)
          ·
            refine ⟨11640495508701106368513979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15520660678268141824685305 11640495508701106368513979)
            ·
              refine ⟨17460743263051659552770969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640495508701106368513979 17460743263051659552770969)
              ·
                refine ⟨13095557447288744664578227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17460743263051659552770969 13095557447288744664578227)
                ·
                  refine ⟨19643336170933116996867341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13095557447288744664578227 19643336170933116996867341)
                  ·
                    refine ⟨7366251064099918873825253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19643336170933116996867341 7366251064099918873825253)
                    ·
                      refine ⟨1381172074518734788842235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7366251064099918873825253 1381172074518734788842235)
                      ·
                        rfl

theorem cell23_2689823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2689823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689823 prefixEnd_2689823 := by exact prefixLift 2689823
  have htrace : WordTrace (prefixWord ++ tailWord_2689823) baseStart_2689823 baseEnd_2689823 := by
    simpa [prefixWord, tailWord_2689823, baseEnd_2689823] using wordTrace_append hprefix tailTrace_2689823
  have hstable : (prefixWord ++ tailWord_2689823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689823).length < 2 ^ (prefixWord ++ tailWord_2689823).sum := by decide
  have hdescent : baseEnd_2689823 < baseStart_2689823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689863 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 6]
def baseStart_2689863 : Nat := 118140960795 + 2689863 * 2 ^ 59
def prefixEnd_2689863 : Nat := 4983230072969 + 3 ^ 40 * 2689863 * 2
def baseEnd_2689863 : Nat := 153465845971657181371339

theorem tailTrace_2689863 : CollatzResearch.WordTrace tailWord_2689863 prefixEnd_2689863 153465845971657181371339 := by
  unfold tailWord_2689863
  simp only [CollatzResearch.WordTrace]
  refine ⟨98107363454093217871442243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65404908969395478580961495 98107363454093217871442243)
  ·
    refine ⟨147161045181139826807163365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98107363454093217871442243 147161045181139826807163365)
    ·
      refine ⟨27592695971463717526343131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147161045181139826807163365 27592695971463717526343131)
      ·
        refine ⟨41389043957195576289514697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27592695971463717526343131 41389043957195576289514697)
        ·
          refine ⟨31041782967896682217136023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41389043957195576289514697 31041782967896682217136023)
          ·
            refine ⟨46562674451845023325704035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31041782967896682217136023 46562674451845023325704035)
            ·
              refine ⟨69844011677767534988556053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46562674451845023325704035 69844011677767534988556053)
              ·
                refine ⟨3273938047395353202588565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69844011677767534988556053 3273938047395353202588565)
                ·
                  refine ⟨153465845971657181371339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3273938047395353202588565 153465845971657181371339)
                  ·
                    rfl

theorem cell23_2689863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 6].length) (baseStart_2689863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689863 prefixEnd_2689863 := by exact prefixLift 2689863
  have htrace : WordTrace (prefixWord ++ tailWord_2689863) baseStart_2689863 baseEnd_2689863 := by
    simpa [prefixWord, tailWord_2689863, baseEnd_2689863] using wordTrace_append hprefix tailTrace_2689863
  have hstable : (prefixWord ++ tailWord_2689863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689863).length < 2 ^ (prefixWord ++ tailWord_2689863).sum := by decide
  have hdescent : baseEnd_2689863 < baseStart_2689863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689917 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_2689917 : Nat := 118140960795 + 2689917 * 2 ^ 59
def prefixEnd_2689917 : Nat := 4983230072969 + 3 ^ 40 * 2689917 * 2
def baseEnd_2689917 : Nat := 1381220341700257421066803

theorem tailTrace_2689917 : CollatzResearch.WordTrace tailWord_2689917 prefixEnd_2689917 1381220341700257421066803 := by
  unfold tailWord_2689917
  simp only [CollatzResearch.WordTrace]
  refine ⟨98109332995897585093908005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65406221997265056729272003 98109332995897585093908005)
  ·
    refine ⟨18395499936730797205107751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98109332995897585093908005 18395499936730797205107751)
    ·
      refine ⟨27593249905096195807661627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395499936730797205107751 27593249905096195807661627)
      ·
        refine ⟨41389874857644293711492441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27593249905096195807661627 41389874857644293711492441)
        ·
          refine ⟨31042406143233220283619331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41389874857644293711492441 31042406143233220283619331)
          ·
            refine ⟨46563609214849830425428997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31042406143233220283619331 46563609214849830425428997)
            ·
              refine ⟨8730676727784343204767937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46563609214849830425428997 8730676727784343204767937)
              ·
                refine ⟨6548007545838257403575953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8730676727784343204767937 6548007545838257403575953)
                ·
                  refine ⟨4911005659378693052681965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548007545838257403575953 4911005659378693052681965)
                  ·
                    refine ⟨1841627122267009894755737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4911005659378693052681965 1841627122267009894755737)
                    ·
                      refine ⟨1381220341700257421066803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841627122267009894755737 1381220341700257421066803)
                      ·
                        rfl

theorem cell23_2689917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_2689917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689917 prefixEnd_2689917 := by exact prefixLift 2689917
  have htrace : WordTrace (prefixWord ++ tailWord_2689917) baseStart_2689917 baseEnd_2689917 := by
    simpa [prefixWord, tailWord_2689917, baseEnd_2689917] using wordTrace_append hprefix tailTrace_2689917
  have hstable : (prefixWord ++ tailWord_2689917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689917).length < 2 ^ (prefixWord ++ tailWord_2689917).sum := by decide
  have hdescent : baseEnd_2689917 < baseStart_2689917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689923 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 3, 6]
def baseStart_2689923 : Nat := 118140960795 + 2689923 * 2 ^ 59
def prefixEnd_2689923 : Nat := 4983230072969 + 3 ^ 40 * 2689923 * 2
def baseEnd_2689923 : Nat := 460407807528061465863925

theorem tailTrace_2689923 : CollatzResearch.WordTrace tailWord_2689923 prefixEnd_2689923 460407807528061465863925 := by
  unfold tailWord_2689923
  simp only [CollatzResearch.WordTrace]
  refine ⟨98109551833875848118626423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65406367889250565412417615 98109551833875848118626423)
  ·
    refine ⟨147164327750813772177939635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98109551833875848118626423 147164327750813772177939635)
    ·
      refine ⟨220746491626220658266909453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147164327750813772177939635 220746491626220658266909453)
      ·
        refine ⟨82779934359832746850091045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220746491626220658266909453 82779934359832746850091045)
        ·
          refine ⟨15521237692468640034392071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82779934359832746850091045 15521237692468640034392071)
          ·
            refine ⟨23281856538702960051588107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15521237692468640034392071 23281856538702960051588107)
            ·
              refine ⟨34922784808054440077382161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23281856538702960051588107 34922784808054440077382161)
              ·
                refine ⟨26192088606040830058036621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34922784808054440077382161 26192088606040830058036621)
                ·
                  refine ⟨9822033227265311271763733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26192088606040830058036621 9822033227265311271763733)
                  ·
                    refine ⟨460407807528061465863925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9822033227265311271763733 460407807528061465863925)
                    ·
                      rfl

theorem cell23_2689923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_2689923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689923 prefixEnd_2689923 := by exact prefixLift 2689923
  have htrace : WordTrace (prefixWord ++ tailWord_2689923) baseStart_2689923 baseEnd_2689923 := by
    simpa [prefixWord, tailWord_2689923, baseEnd_2689923] using wordTrace_append hprefix tailTrace_2689923
  have hstable : (prefixWord ++ tailWord_2689923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689923).length < 2 ^ (prefixWord ++ tailWord_2689923).sum := by decide
  have hdescent : baseEnd_2689923 < baseStart_2689923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689981 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2689981 : Nat := 118140960795 + 2689981 * 2 ^ 59
def prefixEnd_2689981 : Nat := 4983230072969 + 3 ^ 40 * 2689981 * 2
def baseEnd_2689981 : Nat := 1381253204462145170666509

theorem tailTrace_2689981 : CollatzResearch.WordTrace tailWord_2689981 prefixEnd_2689981 1381253204462145170666509 := by
  unfold tailWord_2689981
  simp only [CollatzResearch.WordTrace]
  refine ⟨98111667267665724024237797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65407778178443816016158531 98111667267665724024237797)
  ·
    refine ⟨18395937612687323254544587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98111667267665724024237797 18395937612687323254544587)
    ·
      refine ⟨27593906419030984881816881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395937612687323254544587 27593906419030984881816881)
      ·
        refine ⟨20695429814273238661362661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27593906419030984881816881 20695429814273238661362661)
        ·
          refine ⟨3880393090176232249005499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20695429814273238661362661 3880393090176232249005499)
          ·
            refine ⟨5820589635264348373508249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880393090176232249005499 5820589635264348373508249)
            ·
              refine ⟨4365442226448261280131187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5820589635264348373508249 4365442226448261280131187)
              ·
                refine ⟨6548163339672391920196781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365442226448261280131187 6548163339672391920196781)
                ·
                  refine ⟨2455561252377146970073793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6548163339672391920196781 2455561252377146970073793)
                  ·
                    refine ⟨1841670939282860227555345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455561252377146970073793 1841670939282860227555345)
                    ·
                      refine ⟨1381253204462145170666509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841670939282860227555345 1381253204462145170666509)
                      ·
                        rfl

theorem cell23_2689981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2689981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689981 prefixEnd_2689981 := by exact prefixLift 2689981
  have htrace : WordTrace (prefixWord ++ tailWord_2689981) baseStart_2689981 baseEnd_2689981 := by
    simpa [prefixWord, tailWord_2689981, baseEnd_2689981] using wordTrace_append hprefix tailTrace_2689981
  have hstable : (prefixWord ++ tailWord_2689981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689981).length < 2 ^ (prefixWord ++ tailWord_2689981).sum := by decide
  have hdescent : baseEnd_2689981 < baseStart_2689981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689983 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 2, 7]
def baseStart_2689983 : Nat := 118140960795 + 2689983 * 2 ^ 59
def prefixEnd_2689983 : Nat := 4983230072969 + 3 ^ 40 * 2689983 * 2
def baseEnd_2689983 : Nat := 460418077141151387613833

theorem tailTrace_2689983 : CollatzResearch.WordTrace tailWord_2689983 prefixEnd_2689983 460418077141151387613833 := by
  unfold tailWord_2689983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98111740213658478365810603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65407826809105652243873735 98111740213658478365810603)
  ·
    refine ⟨147167610320487717548715905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98111740213658478365810603 147167610320487717548715905)
    ·
      refine ⟨110375707740365788161536929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147167610320487717548715905 110375707740365788161536929)
      ·
        refine ⟨82781780805274341121152697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110375707740365788161536929 82781780805274341121152697)
        ·
          refine ⟨62086335603955755840864523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82781780805274341121152697 62086335603955755840864523)
          ·
            refine ⟨93129503405933633761296785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62086335603955755840864523 93129503405933633761296785)
            ·
              refine ⟨69847127554450225320972589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93129503405933633761296785 69847127554450225320972589)
              ·
                refine ⟨26192672832918834495364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69847127554450225320972589 26192672832918834495364721)
                ·
                  refine ⟨19644504624689125871523541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26192672832918834495364721 19644504624689125871523541)
                  ·
                    refine ⟨460418077141151387613833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19644504624689125871523541 460418077141151387613833)
                    ·
                      rfl

theorem cell23_2689983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_2689983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689983 prefixEnd_2689983 := by exact prefixLift 2689983
  have htrace : WordTrace (prefixWord ++ tailWord_2689983) baseStart_2689983 baseEnd_2689983 := by
    simpa [prefixWord, tailWord_2689983, baseEnd_2689983] using wordTrace_append hprefix tailTrace_2689983
  have hstable : (prefixWord ++ tailWord_2689983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689983).length < 2 ^ (prefixWord ++ tailWord_2689983).sum := by decide
  have hdescent : baseEnd_2689983 < baseStart_2689983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689993 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_2689993 : Nat := 118140960795 + 2689993 * 2 ^ 59
def prefixEnd_2689993 : Nat := 4983230072969 + 3 ^ 40 * 2689993 * 2
def baseEnd_2689993 : Nat := 1381259366229999123716453

theorem tailTrace_2689993 : CollatzResearch.WordTrace tailWord_2689993 prefixEnd_2689993 1381259366229999123716453 := by
  unfold tailWord_2689993
  simp only [CollatzResearch.WordTrace]
  refine ⟨98112104943622250073674633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65408069962414833382449755 98112104943622250073674633)
  ·
    refine ⟨73584078707716687555255975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98112104943622250073674633 73584078707716687555255975)
    ·
      refine ⟨110376118061575031332883963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73584078707716687555255975 110376118061575031332883963)
      ·
        refine ⟨165564177092362546999325945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110376118061575031332883963 165564177092362546999325945)
        ·
          refine ⟨124173132819271910249494459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165564177092362546999325945 124173132819271910249494459)
          ·
            refine ⟨186259699228907865374241689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124173132819271910249494459 186259699228907865374241689)
            ·
              refine ⟨139694774421680899030681267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186259699228907865374241689 139694774421680899030681267)
              ·
                refine ⟨209542161632521348546021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139694774421680899030681267 209542161632521348546021901)
                ·
                  refine ⟨78578310612195505704758213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209542161632521348546021901 78578310612195505704758213)
                  ·
                    refine ⟨14733433239786657319642165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78578310612195505704758213 14733433239786657319642165)
                    ·
                      refine ⟨1381259366229999123716453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14733433239786657319642165 1381259366229999123716453)
                      ·
                        rfl

theorem cell23_2689993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_2689993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2689993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2689993 prefixEnd_2689993 := by exact prefixLift 2689993
  have htrace : WordTrace (prefixWord ++ tailWord_2689993) baseStart_2689993 baseEnd_2689993 := by
    simpa [prefixWord, tailWord_2689993, baseEnd_2689993] using wordTrace_append hprefix tailTrace_2689993
  have hstable : (prefixWord ++ tailWord_2689993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689993).length < 2 ^ (prefixWord ++ tailWord_2689993).sum := by decide
  have hdescent : baseEnd_2689993 < baseStart_2689993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690010 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_2690010 : Nat := 118140960795 + 2690010 * 2 ^ 59
def prefixEnd_2690010 : Nat := 4983230072969 + 3 ^ 40 * 2690010 * 2
def baseEnd_2690010 : Nat := 1381268095401125557203875

theorem tailTrace_2690010 : CollatzResearch.WordTrace tailWord_2690010 prefixEnd_2690010 1381268095401125557203875 := by
  unfold tailWord_2690010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24528181246140165494260871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65408483323040441318028989 24528181246140165494260871)
  ·
    refine ⟨36792271869210248241391307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24528181246140165494260871 36792271869210248241391307)
    ·
      refine ⟨55188407803815372362086961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36792271869210248241391307 55188407803815372362086961)
      ·
        refine ⟨41391305852861529271565221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55188407803815372362086961 41391305852861529271565221)
        ·
          refine ⟨7760869847411536738418479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41391305852861529271565221 7760869847411536738418479)
          ·
            refine ⟨11641304771117305107627719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760869847411536738418479 11641304771117305107627719)
            ·
              refine ⟨17461957156675957661441579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641304771117305107627719 17461957156675957661441579)
              ·
                refine ⟨26192935735013936492162369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17461957156675957661441579 26192935735013936492162369)
                ·
                  refine ⟨19644701801260452369121777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26192935735013936492162369 19644701801260452369121777)
                  ·
                    refine ⟨14733526350945339276841333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19644701801260452369121777 14733526350945339276841333)
                    ·
                      refine ⟨1381268095401125557203875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14733526350945339276841333 1381268095401125557203875)
                      ·
                        rfl

theorem cell23_2690010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_2690010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690010 prefixEnd_2690010 := by exact prefixLift 2690010
  have htrace : WordTrace (prefixWord ++ tailWord_2690010) baseStart_2690010 baseEnd_2690010 := by
    simpa [prefixWord, tailWord_2690010, baseEnd_2690010] using wordTrace_append hprefix tailTrace_2690010
  have hstable : (prefixWord ++ tailWord_2690010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690010).length < 2 ^ (prefixWord ++ tailWord_2690010).sum := by decide
  have hdescent : baseEnd_2690010 < baseStart_2690010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690015 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 1, 2, 2]
def baseStart_2690015 : Nat := 118140960795 + 2690015 * 2 ^ 59
def prefixEnd_2690015 : Nat := 4983230072969 + 3 ^ 40 * 2690015 * 2
def baseEnd_2690015 : Nat := 1381270662804398037641353

theorem tailTrace_2690015 : CollatzResearch.WordTrace tailWord_2690015 prefixEnd_2690015 1381270662804398037641353 := by
  unfold tailWord_2690015
  simp only [CollatzResearch.WordTrace]
  refine ⟨98112907349542547830975499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65408604899695031887316999 98112907349542547830975499)
  ·
    refine ⟨147169361024313821746463249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98112907349542547830975499 147169361024313821746463249)
    ·
      refine ⟨110377020768235366309847437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147169361024313821746463249 110377020768235366309847437)
      ·
        refine ⟨41391382788088262366192789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110377020768235366309847437 41391382788088262366192789)
        ·
          refine ⟨1940221068191637298415287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41391382788088262366192789 1940221068191637298415287)
          ·
            refine ⟨2910331602287455947622931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940221068191637298415287 2910331602287455947622931)
            ·
              refine ⟨4365497403431183921434397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910331602287455947622931 4365497403431183921434397)
              ·
                refine ⟨1637061526286693970537899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4365497403431183921434397 1637061526286693970537899)
                ·
                  refine ⟨2455592289430040955806849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637061526286693970537899 2455592289430040955806849)
                  ·
                    refine ⟨1841694217072530716855137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455592289430040955806849 1841694217072530716855137)
                    ·
                      refine ⟨1381270662804398037641353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841694217072530716855137 1381270662804398037641353)
                      ·
                        rfl

theorem cell23_2690015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_2690015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690015 prefixEnd_2690015 := by exact prefixLift 2690015
  have htrace : WordTrace (prefixWord ++ tailWord_2690015) baseStart_2690015 baseEnd_2690015 := by
    simpa [prefixWord, tailWord_2690015, baseEnd_2690015] using wordTrace_append hprefix tailTrace_2690015
  have hstable : (prefixWord ++ tailWord_2690015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690015).length < 2 ^ (prefixWord ++ tailWord_2690015).sum := by decide
  have hdescent : baseEnd_2690015 < baseStart_2690015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690024 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2690024 : Nat := 118140960795 + 2690024 * 2 ^ 59
def prefixEnd_2690024 : Nat := 4983230072969 + 3 ^ 40 * 2690024 * 2
def baseEnd_2690024 : Nat := 1381275284130288502428811

theorem tailTrace_2690024 : CollatzResearch.WordTrace tailWord_2690024 prefixEnd_2690024 1381275284130288502428811 := by
  unfold tailWord_2690024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49056617803254971184026563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65408823737673294912035417 49056617803254971184026563)
  ·
    refine ⟨73584926704882456776039845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49056617803254971184026563 73584926704882456776039845)
    ·
      refine ⟨13797173757165460645507471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73584926704882456776039845 13797173757165460645507471)
      ·
        refine ⟨20695760635748190968261207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13797173757165460645507471 20695760635748190968261207)
        ·
          refine ⟨31043640953622286452391811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20695760635748190968261207 31043640953622286452391811)
          ·
            refine ⟨46565461430433429678587717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31043640953622286452391811 46565461430433429678587717)
            ·
              refine ⟨8731024018206268064735197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46565461430433429678587717 8731024018206268064735197)
              ·
                refine ⟨3274134006827350524275699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8731024018206268064735197 3274134006827350524275699)
                ·
                  refine ⟨4911201010241025786413549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274134006827350524275699 4911201010241025786413549)
                  ·
                    refine ⟨1841700378840384669905081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4911201010241025786413549 1841700378840384669905081)
                    ·
                      refine ⟨1381275284130288502428811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841700378840384669905081 1381275284130288502428811)
                      ·
                        rfl

theorem cell23_2690024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2690024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690024 prefixEnd_2690024 := by exact prefixLift 2690024
  have htrace : WordTrace (prefixWord ++ tailWord_2690024) baseStart_2690024 baseEnd_2690024 := by
    simpa [prefixWord, tailWord_2690024, baseEnd_2690024] using wordTrace_append hprefix tailTrace_2690024
  have hstable : (prefixWord ++ tailWord_2690024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690024).length < 2 ^ (prefixWord ++ tailWord_2690024).sum := by decide
  have hdescent : baseEnd_2690024 < baseStart_2690024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690040 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_2690040 : Nat := 118140960795 + 2690040 * 2 ^ 59
def prefixEnd_2690040 : Nat := 4983230072969 + 3 ^ 40 * 2690040 * 2
def baseEnd_2690040 : Nat := 1381283499820760439828737

theorem tailTrace_2690040 : CollatzResearch.WordTrace tailWord_2690040 prefixEnd_2690040 1381283499820760439828737 := by
  unfold tailWord_2690040
  simp only [CollatzResearch.WordTrace]
  refine ⟨49056909587225988550317787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65409212782967984733757049 49056909587225988550317787)
  ·
    refine ⟨73585364380838982825476681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49056909587225988550317787 73585364380838982825476681)
    ·
      refine ⟨55189023285629237119107511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73585364380838982825476681 55189023285629237119107511)
      ·
        refine ⟨82783534928443855678661267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55189023285629237119107511 82783534928443855678661267)
        ·
          refine ⟨124175302392665783517991901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82783534928443855678661267 124175302392665783517991901)
          ·
            refine ⟨46565738397249668819246963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124175302392665783517991901 46565738397249668819246963)
            ·
              refine ⟨69848607595874503228870445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46565738397249668819246963 69848607595874503228870445)
              ·
                refine ⟨26193227848452938710826417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69848607595874503228870445 26193227848452938710826417)
                ·
                  refine ⟨19644920886339704033119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26193227848452938710826417 19644920886339704033119813)
                  ·
                    refine ⟨3683422666188694506209965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19644920886339704033119813 3683422666188694506209965)
                    ·
                      refine ⟨1381283499820760439828737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683422666188694506209965 1381283499820760439828737)
                      ·
                        rfl

theorem cell23_2690040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_2690040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690040 prefixEnd_2690040 := by exact prefixLift 2690040
  have htrace : WordTrace (prefixWord ++ tailWord_2690040) baseStart_2690040 baseEnd_2690040 := by
    simpa [prefixWord, tailWord_2690040, baseEnd_2690040] using wordTrace_append hprefix tailTrace_2690040
  have hstable : (prefixWord ++ tailWord_2690040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690040).length < 2 ^ (prefixWord ++ tailWord_2690040).sum := by decide
  have hdescent : baseEnd_2690040 < baseStart_2690040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690094 : List Nat := [4, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_2690094 : Nat := 118140960795 + 2690094 * 2 ^ 59
def prefixEnd_2690094 : Nat := 4983230072969 + 3 ^ 40 * 2690094 * 2
def baseEnd_2690094 : Nat := 153479025308455914283721

theorem tailTrace_2690094 : CollatzResearch.WordTrace tailWord_2690094 prefixEnd_2690094 153479025308455914283721 := by
  unfold tailWord_2690094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12264473589532043040387667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65410525810837562882067557 12264473589532043040387667)
  ·
    refine ⟨18396710384298064560581501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12264473589532043040387667 18396710384298064560581501)
    ·
      refine ⟨6898766394111774210218063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18396710384298064560581501 6898766394111774210218063)
      ·
        refine ⟨10348149591167661315327095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898766394111774210218063 10348149591167661315327095)
        ·
          refine ⟨15522224386751491972990643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10348149591167661315327095 15522224386751491972990643)
          ·
            refine ⟨23283336580127237959485965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15522224386751491972990643 23283336580127237959485965)
            ·
              refine ⟨8731251217547714234807237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23283336580127237959485965 8731251217547714234807237)
              ·
                refine ⟨1637109603290196419026357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8731251217547714234807237 1637109603290196419026357)
                ·
                  refine ⟨153479025308455914283721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637109603290196419026357 153479025308455914283721)
                  ·
                    rfl

theorem cell23_2690094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_2690094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690094 prefixEnd_2690094 := by exact prefixLift 2690094
  have htrace : WordTrace (prefixWord ++ tailWord_2690094) baseStart_2690094 baseEnd_2690094 := by
    simpa [prefixWord, tailWord_2690094, baseEnd_2690094] using wordTrace_append hprefix tailTrace_2690094
  have hstable : (prefixWord ++ tailWord_2690094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690094).length < 2 ^ (prefixWord ++ tailWord_2690094).sum := by decide
  have hdescent : baseEnd_2690094 < baseStart_2690094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690097 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 7, 2]
def baseStart_2690097 : Nat := 118140960795 + 2690097 * 2 ^ 59
def prefixEnd_2690097 : Nat := 4983230072969 + 3 ^ 40 * 2690097 * 2
def baseEnd_2690097 : Nat := 1381312768218066716815975

theorem tailTrace_2690097 : CollatzResearch.WordTrace tailWord_2690097 prefixEnd_2690097 1381312768218066716815975 := by
  unfold tailWord_2690097
  simp only [CollatzResearch.WordTrace]
  refine ⟨98115898135245475835460545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65410598756830317223640363 98115898135245475835460545)
  ·
    refine ⟨73586923601434106876595409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98115898135245475835460545 73586923601434106876595409)
    ·
      refine ⟨55190192701075580157446557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73586923601434106876595409 55190192701075580157446557)
      ·
        refine ⟨20696322262903342559042459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55190192701075580157446557 20696322262903342559042459)
        ·
          refine ⟨31044483394355013838563689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20696322262903342559042459 31044483394355013838563689)
          ·
            refine ⟨23283362545766260378922767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31044483394355013838563689 23283362545766260378922767)
            ·
              refine ⟨34925043818649390568384151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23283362545766260378922767 34925043818649390568384151)
              ·
                refine ⟨52387565727974085852576227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34925043818649390568384151 52387565727974085852576227)
                ·
                  refine ⟨78581348591961128778864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52387565727974085852576227 78581348591961128778864341)
                  ·
                    refine ⟨1841750357624088955754633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78581348591961128778864341 1841750357624088955754633)
                    ·
                      refine ⟨1381312768218066716815975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841750357624088955754633 1381312768218066716815975)
                      ·
                        rfl

theorem cell23_2690097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_2690097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690097 prefixEnd_2690097 := by exact prefixLift 2690097
  have htrace : WordTrace (prefixWord ++ tailWord_2690097) baseStart_2690097 baseEnd_2690097 := by
    simpa [prefixWord, tailWord_2690097, baseEnd_2690097] using wordTrace_append hprefix tailTrace_2690097
  have hstable : (prefixWord ++ tailWord_2690097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690097).length < 2 ^ (prefixWord ++ tailWord_2690097).sum := by decide
  have hdescent : baseEnd_2690097 < baseStart_2690097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690127 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 4, 2]
def baseStart_2690127 : Nat := 118140960795 + 2690127 * 2 ^ 59
def prefixEnd_2690127 : Nat := 4983230072969 + 3 ^ 40 * 2690127 * 2
def baseEnd_2690127 : Nat := 1381328172637701599440837

theorem tailTrace_2690127 : CollatzResearch.WordTrace tailWord_2690127 prefixEnd_2690127 1381328172637701599440837 := by
  unfold tailWord_2690127
  simp only [CollatzResearch.WordTrace]
  refine ⟨98116992325136790959052635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65411328216757860639368423 98116992325136790959052635)
  ·
    refine ⟨147175488487705186438578953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98116992325136790959052635 147175488487705186438578953)
    ·
      refine ⟨110381616365778889828934215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147175488487705186438578953 110381616365778889828934215)
      ·
        refine ⟨165572424548668334743401323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110381616365778889828934215 165572424548668334743401323)
        ·
          refine ⟨248358636823002502115101985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165572424548668334743401323 248358636823002502115101985)
          ·
            refine ⟨186268977617251876586326489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248358636823002502115101985 186268977617251876586326489)
            ·
              refine ⟨139701733212938907439744867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186268977617251876586326489 139701733212938907439744867)
              ·
                refine ⟨209552599819408361159617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139701733212938907439744867 209552599819408361159617301)
                ·
                  refine ⟨9822778116534766929357061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209552599819408361159617301 9822778116534766929357061)
                  ·
                    refine ⟨1841770896850268799254449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9822778116534766929357061 1841770896850268799254449)
                    ·
                      refine ⟨1381328172637701599440837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841770896850268799254449 1381328172637701599440837)
                      ·
                        rfl

theorem cell23_2690127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4, 2].length) (baseStart_2690127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690127 prefixEnd_2690127 := by exact prefixLift 2690127
  have htrace : WordTrace (prefixWord ++ tailWord_2690127) baseStart_2690127 baseEnd_2690127 := by
    simpa [prefixWord, tailWord_2690127, baseEnd_2690127] using wordTrace_append hprefix tailTrace_2690127
  have hstable : (prefixWord ++ tailWord_2690127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690127).length < 2 ^ (prefixWord ++ tailWord_2690127).sum := by decide
  have hdescent : baseEnd_2690127 < baseStart_2690127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690147 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2690147 : Nat := 118140960795 + 2690147 * 2 ^ 59
def prefixEnd_2690147 : Nat := 4983230072969 + 3 ^ 40 * 2690147 * 2
def baseEnd_2690147 : Nat := 1381338442250791521190745

theorem tailTrace_2690147 : CollatzResearch.WordTrace tailWord_2690147 prefixEnd_2690147 1381338442250791521190745 := by
  unfold tailWord_2690147
  simp only [CollatzResearch.WordTrace]
  refine ⟨98117721785064334374780695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65411814523376222916520463 98117721785064334374780695)
  ·
    refine ⟨147176582677596501562171043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98117721785064334374780695 147176582677596501562171043)
    ·
      refine ⟨220764874016394752343256565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147176582677596501562171043 220764874016394752343256565)
      ·
        refine ⟨20696706939037008032180303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220764874016394752343256565 20696706939037008032180303)
        ·
          refine ⟨31045060408555512048270455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20696706939037008032180303 31045060408555512048270455)
          ·
            refine ⟨46567590612833268072405683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31045060408555512048270455 46567590612833268072405683)
            ·
              refine ⟨69851385919249902108608525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46567590612833268072405683 69851385919249902108608525)
              ·
                refine ⟨26194269719718713290728197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69851385919249902108608525 26194269719718713290728197)
                ·
                  refine ⟨4911425572447258742011537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26194269719718713290728197 4911425572447258742011537)
                  ·
                    refine ⟨3683569179335444056508653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911425572447258742011537 3683569179335444056508653)
                    ·
                      refine ⟨1381338442250791521190745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683569179335444056508653 1381338442250791521190745)
                      ·
                        rfl

theorem cell23_2690147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2690147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690147 prefixEnd_2690147 := by exact prefixLift 2690147
  have htrace : WordTrace (prefixWord ++ tailWord_2690147) baseStart_2690147 baseEnd_2690147 := by
    simpa [prefixWord, tailWord_2690147, baseEnd_2690147] using wordTrace_append hprefix tailTrace_2690147
  have hstable : (prefixWord ++ tailWord_2690147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690147).length < 2 ^ (prefixWord ++ tailWord_2690147).sum := by decide
  have hdescent : baseEnd_2690147 < baseStart_2690147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690154 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2690154 : Nat := 118140960795 + 2690154 * 2 ^ 59
def prefixEnd_2690154 : Nat := 4983230072969 + 3 ^ 40 * 2690154 * 2
def baseEnd_2690154 : Nat := 460447345538457664601071

theorem tailTrace_2690154 : CollatzResearch.WordTrace tailWord_2690154 prefixEnd_2690154 460447345538457664601071 := by
  unfold tailWord_2690154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24529494274009743642571379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65411984730692649713523677 24529494274009743642571379)
  ·
    refine ⟨36794241411014615463857069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24529494274009743642571379 36794241411014615463857069)
    ·
      refine ⟨13797840529130480798946401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36794241411014615463857069 13797840529130480798946401)
      ·
        refine ⟨10348380396847860599209801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13797840529130480798946401 10348380396847860599209801)
        ·
          refine ⟨7761285297635895449407351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10348380396847860599209801 7761285297635895449407351)
          ·
            refine ⟨11641927946453843174111027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761285297635895449407351 11641927946453843174111027)
            ·
              refine ⟨17462891919680764761166541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641927946453843174111027 17462891919680764761166541)
              ·
                refine ⟨6548584469880286785437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17462891919680764761166541 6548584469880286785437453)
                ·
                  refine ⟨2455719176205107544539045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6548584469880286785437453 2455719176205107544539045)
                  ·
                    refine ⟨460447345538457664601071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455719176205107544539045 460447345538457664601071)
                    ·
                      rfl

theorem cell23_2690154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2690154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690154 prefixEnd_2690154 := by exact prefixLift 2690154
  have htrace : WordTrace (prefixWord ++ tailWord_2690154) baseStart_2690154 baseEnd_2690154 := by
    simpa [prefixWord, tailWord_2690154, baseEnd_2690154] using wordTrace_append hprefix tailTrace_2690154
  have hstable : (prefixWord ++ tailWord_2690154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690154).length < 2 ^ (prefixWord ++ tailWord_2690154).sum := by decide
  have hdescent : baseEnd_2690154 < baseStart_2690154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 1, 1, 3]
def baseStart_2690211 : Nat := 118140960795 + 2690211 * 2 ^ 59
def prefixEnd_2690211 : Nat := 4983230072969 + 3 ^ 40 * 2690211 * 2
def baseEnd_2690211 : Nat := 1381371305012679270790451

theorem tailTrace_2690211 : CollatzResearch.WordTrace tailWord_2690211 prefixEnd_2690211 1381371305012679270790451 := by
  unfold tailWord_2690211
  simp only [CollatzResearch.WordTrace]
  refine ⟨98120056056832473305110487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65413370704554982203406991 98120056056832473305110487)
  ·
    refine ⟨147180084085248709957665731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98120056056832473305110487 147180084085248709957665731)
    ·
      refine ⟨220770126127873064936498597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147180084085248709957665731 220770126127873064936498597)
      ·
        refine ⟨41394398648976199675593487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220770126127873064936498597 41394398648976199675593487)
        ·
          refine ⟨62091597973464299513390231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41394398648976199675593487 62091597973464299513390231)
          ·
            refine ⟨93137396960196449270085347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62091597973464299513390231 93137396960196449270085347)
            ·
              refine ⟨139706095440294673905128021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93137396960196449270085347 139706095440294673905128021)
              ·
                refine ⟨1637180805940953209825719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 139706095440294673905128021 1637180805940953209825719)
                ·
                  refine ⟨2455771208911429814738579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637180805940953209825719 2455771208911429814738579)
                  ·
                    refine ⟨3683656813367144722107869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455771208911429814738579 3683656813367144722107869)
                    ·
                      refine ⟨1381371305012679270790451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683656813367144722107869 1381371305012679270790451)
                      ·
                        rfl

theorem cell23_2690211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_2690211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690211 prefixEnd_2690211 := by exact prefixLift 2690211
  have htrace : WordTrace (prefixWord ++ tailWord_2690211) baseStart_2690211 baseEnd_2690211 := by
    simpa [prefixWord, tailWord_2690211, baseEnd_2690211] using wordTrace_append hprefix tailTrace_2690211
  have hstable : (prefixWord ++ tailWord_2690211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690211).length < 2 ^ (prefixWord ++ tailWord_2690211).sum := by decide
  have hdescent : baseEnd_2690211 < baseStart_2690211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690218 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_2690218 : Nat := 118140960795 + 2690218 * 2 ^ 59
def prefixEnd_2690218 : Nat := 4983230072969 + 3 ^ 40 * 2690218 * 2
def baseEnd_2690218 : Nat := 153486099930806749266991

theorem tailTrace_2690218 : CollatzResearch.WordTrace tailWord_2690218 prefixEnd_2690218 153486099930806749266991 := by
  unfold tailWord_2690218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24530077841951778375153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65413540911871409000410205 24530077841951778375153827)
  ·
    refine ⟨36795116762927667562730741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24530077841951778375153827 36795116762927667562730741)
    ·
      refine ⟨3449542196524468834006007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36795116762927667562730741 3449542196524468834006007)
      ·
        refine ⟨5174313294786703251009011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449542196524468834006007 5174313294786703251009011)
        ·
          refine ⟨7761469942180054876513517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174313294786703251009011 7761469942180054876513517)
          ·
            refine ⟨2910551228317520578692569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7761469942180054876513517 2910551228317520578692569)
            ·
              refine ⟨2182913421238140434019427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910551228317520578692569 2182913421238140434019427)
              ·
                refine ⟨3274370131857210651029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182913421238140434019427 3274370131857210651029141)
                ·
                  refine ⟨153486099930806749266991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3274370131857210651029141 153486099930806749266991)
                  ·
                    rfl

theorem cell23_2690218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_2690218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690218 prefixEnd_2690218 := by exact prefixLift 2690218
  have htrace : WordTrace (prefixWord ++ tailWord_2690218) baseStart_2690218 baseEnd_2690218 := by
    simpa [prefixWord, tailWord_2690218, baseEnd_2690218] using wordTrace_append hprefix tailTrace_2690218
  have hstable : (prefixWord ++ tailWord_2690218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690218).length < 2 ^ (prefixWord ++ tailWord_2690218).sum := by decide
  have hdescent : baseEnd_2690218 < baseStart_2690218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690237 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2690237 : Nat := 118140960795 + 2690237 * 2 ^ 59
def prefixEnd_2690237 : Nat := 4983230072969 + 3 ^ 40 * 2690237 * 2
def baseEnd_2690237 : Nat := 1381384655509696169065331

theorem tailTrace_2690237 : CollatzResearch.WordTrace tailWord_2690237 prefixEnd_2690237 1381384655509696169065331 := by
  unfold tailWord_2690237
  simp only [CollatzResearch.WordTrace]
  refine ⟨98121004354738279745556965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65414002903158853163704643 98121004354738279745556965)
  ·
    refine ⟨18397688316513427452291931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98121004354738279745556965 18397688316513427452291931)
    ·
      refine ⟨27596532474770141178437897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18397688316513427452291931 27596532474770141178437897)
      ·
        refine ⟨20697399356077605883828423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27596532474770141178437897 20697399356077605883828423)
        ·
          refine ⟨31046099034116408825742635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697399356077605883828423 31046099034116408825742635)
          ·
            refine ⟨46569148551174613238613953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31046099034116408825742635 46569148551174613238613953)
            ·
              refine ⟨34926861413380959928960465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46569148551174613238613953 34926861413380959928960465)
              ·
                refine ⟨26195146060035719946720349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34926861413380959928960465 26195146060035719946720349)
                ·
                  refine ⟨9823179772513394980020131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26195146060035719946720349 9823179772513394980020131)
                  ·
                    refine ⟨14734769658770092470030197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9823179772513394980020131 14734769658770092470030197)
                    ·
                      refine ⟨1381384655509696169065331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14734769658770092470030197 1381384655509696169065331)
                      ·
                        rfl

theorem cell23_2690237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2690237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690237 prefixEnd_2690237 := by exact prefixLift 2690237
  have htrace : WordTrace (prefixWord ++ tailWord_2690237) baseStart_2690237 baseEnd_2690237 := by
    simpa [prefixWord, tailWord_2690237, baseEnd_2690237] using wordTrace_append hprefix tailTrace_2690237
  have hstable : (prefixWord ++ tailWord_2690237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690237).length < 2 ^ (prefixWord ++ tailWord_2690237).sum := by decide
  have hdescent : baseEnd_2690237 < baseStart_2690237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690238 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2690238 : Nat := 118140960795 + 2690238 * 2 ^ 59
def prefixEnd_2690238 : Nat := 4983230072969 + 3 ^ 40 * 2690238 * 2
def baseEnd_2690238 : Nat := 1381385168990350665152827

theorem tailTrace_2690238 : CollatzResearch.WordTrace tailWord_2690238 prefixEnd_2690238 1381385168990350665152827 := by
  unfold tailWord_2690238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265130103466832114542921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65414027218489771277562245 12265130103466832114542921)
  ·
    refine ⟨9198847577600124085907191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12265130103466832114542921 9198847577600124085907191)
    ·
      refine ⟨13798271366400186128860787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9198847577600124085907191 13798271366400186128860787)
      ·
        refine ⟨20697407049600279193291181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798271366400186128860787 20697407049600279193291181)
        ·
          refine ⟨7761527643600104697484193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20697407049600279193291181 7761527643600104697484193)
          ·
            refine ⟨5821145732700078523113145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7761527643600104697484193 5821145732700078523113145)
            ·
              refine ⟨4365859299525058892334859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821145732700078523113145 4365859299525058892334859)
              ·
                refine ⟨6548788949287588338502289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365859299525058892334859 6548788949287588338502289)
                ·
                  refine ⟨4911591711965691253876717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548788949287588338502289 4911591711965691253876717)
                  ·
                    refine ⟨1841846891987134220203769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4911591711965691253876717 1841846891987134220203769)
                    ·
                      refine ⟨1381385168990350665152827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841846891987134220203769 1381385168990350665152827)
                      ·
                        rfl

theorem cell23_2690238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2690238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690238 prefixEnd_2690238 := by exact prefixLift 2690238
  have htrace : WordTrace (prefixWord ++ tailWord_2690238) baseStart_2690238 baseEnd_2690238 := by
    simpa [prefixWord, tailWord_2690238, baseEnd_2690238] using wordTrace_append hprefix tailTrace_2690238
  have hstable : (prefixWord ++ tailWord_2690238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690238).length < 2 ^ (prefixWord ++ tailWord_2690238).sum := by decide
  have hdescent : baseEnd_2690238 < baseStart_2690238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690261 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2690261 : Nat := 118140960795 + 2690261 * 2 ^ 59
def prefixEnd_2690261 : Nat := 4983230072969 + 3 ^ 40 * 2690261 * 2
def baseEnd_2690261 : Nat := 460465659681801358388407

theorem tailTrace_2690261 : CollatzResearch.WordTrace tailWord_2690261 prefixEnd_2690261 460465659681801358388407 := by
  unfold tailWord_2690261
  simp only [CollatzResearch.WordTrace]
  refine ⟨98121879706651331844430637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65414586471100887896287091 98121879706651331844430637)
  ·
    refine ⟨36795704889994249441661489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98121879706651331844430637 36795704889994249441661489)
    ·
      refine ⟨27596778667495687081246117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36795704889994249441661489 27596778667495687081246117)
      ·
        refine ⟨5174396000155441327733647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27596778667495687081246117 5174396000155441327733647)
        ·
          refine ⟨7761594000233161991600471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174396000155441327733647 7761594000233161991600471)
          ·
            refine ⟨11642391000349742987400707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761594000233161991600471 11642391000349742987400707)
            ·
              refine ⟨17463586500524614481101061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11642391000349742987400707 17463586500524614481101061)
              ·
                refine ⟨3274422468848365215206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17463586500524614481101061 3274422468848365215206449)
                ·
                  refine ⟨2455816851636273911404837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274422468848365215206449 2455816851636273911404837)
                  ·
                    refine ⟨460465659681801358388407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2455816851636273911404837 460465659681801358388407)
                    ·
                      rfl

theorem cell23_2690261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2690261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690261 prefixEnd_2690261 := by exact prefixLift 2690261
  have htrace : WordTrace (prefixWord ++ tailWord_2690261) baseStart_2690261 baseEnd_2690261 := by
    simpa [prefixWord, tailWord_2690261, baseEnd_2690261] using wordTrace_append hprefix tailTrace_2690261
  have hstable : (prefixWord ++ tailWord_2690261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690261).length < 2 ^ (prefixWord ++ tailWord_2690261).sum := by decide
  have hdescent : baseEnd_2690261 < baseStart_2690261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690262 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2690262 : Nat := 118140960795 + 2690262 * 2 ^ 59
def prefixEnd_2690262 : Nat := 4983230072969 + 3 ^ 40 * 2690262 * 2
def baseEnd_2690262 : Nat := 1381397492526058571252717

theorem tailTrace_2690262 : CollatzResearch.WordTrace tailWord_2690262 prefixEnd_2690262 1381397492526058571252717 := by
  unfold tailWord_2690262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132619761227981813451065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65414610786431806010144693 6132619761227981813451065)
  ·
    refine ⟨4599464820920986360088299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6132619761227981813451065 4599464820920986360088299)
    ·
      refine ⟨6899197231381479540132449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599464820920986360088299 6899197231381479540132449)
      ·
        refine ⟨5174397923536109655099337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6899197231381479540132449 5174397923536109655099337)
        ·
          refine ⟨3880798442652082241324503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174397923536109655099337 3880798442652082241324503)
          ·
            refine ⟨5821197663978123361986755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880798442652082241324503 5821197663978123361986755)
            ·
              refine ⟨8731796495967185042980133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821197663978123361986755 8731796495967185042980133)
              ·
                refine ⟨1637211842993847195558775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8731796495967185042980133 1637211842993847195558775)
                ·
                  refine ⟨2455817764490770793338163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637211842993847195558775 2455817764490770793338163)
                  ·
                    refine ⟨3683726646736156190007245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455817764490770793338163 3683726646736156190007245)
                    ·
                      refine ⟨1381397492526058571252717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683726646736156190007245 1381397492526058571252717)
                      ·
                        rfl

theorem cell23_2690262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2690262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690262 prefixEnd_2690262 := by exact prefixLift 2690262
  have htrace : WordTrace (prefixWord ++ tailWord_2690262) baseStart_2690262 baseEnd_2690262 := by
    simpa [prefixWord, tailWord_2690262, baseEnd_2690262] using wordTrace_append hprefix tailTrace_2690262
  have hstable : (prefixWord ++ tailWord_2690262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690262).length < 2 ^ (prefixWord ++ tailWord_2690262).sum := by decide
  have hdescent : baseEnd_2690262 < baseStart_2690262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690284 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 3]
def baseStart_2690284 : Nat := 118140960795 + 2690284 * 2 ^ 59
def prefixEnd_2690284 : Nat := 4983230072969 + 3 ^ 40 * 2690284 * 2
def baseEnd_2690284 : Nat := 1381408789100457485177615

theorem tailTrace_2690284 : CollatzResearch.WordTrace tailWord_2690284 prefixEnd_2690284 1381408789100457485177615 := by
  unfold tailWord_2690284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49061359292784003386258953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65415145723712004515011937 49061359292784003386258953)
  ·
    refine ⟨36796019469588002539694215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49061359292784003386258953 36796019469588002539694215)
    ·
      refine ⟨55194029204382003809541323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36796019469588002539694215 55194029204382003809541323)
      ·
        refine ⟨82791043806573005714311985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55194029204382003809541323 82791043806573005714311985)
        ·
          refine ⟨62093282854929754285733989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82791043806573005714311985 62093282854929754285733989)
          ·
            refine ⟨11642490535299328928575123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62093282854929754285733989 11642490535299328928575123)
            ·
              refine ⟨17463735802948993392862685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11642490535299328928575123 17463735802948993392862685)
              ·
                refine ⟨6548900926105872522323507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17463735802948993392862685 6548900926105872522323507)
                ·
                  refine ⟨9823351389158808783485261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6548900926105872522323507 9823351389158808783485261)
                  ·
                    refine ⟨3683756770934553293806973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9823351389158808783485261 3683756770934553293806973)
                    ·
                      refine ⟨1381408789100457485177615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683756770934553293806973 1381408789100457485177615)
                      ·
                        rfl

theorem cell23_2690284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_2690284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690284 prefixEnd_2690284 := by exact prefixLift 2690284
  have htrace : WordTrace (prefixWord ++ tailWord_2690284) baseStart_2690284 baseEnd_2690284 := by
    simpa [prefixWord, tailWord_2690284, baseEnd_2690284] using wordTrace_append hprefix tailTrace_2690284
  have hstable : (prefixWord ++ tailWord_2690284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690284).length < 2 ^ (prefixWord ++ tailWord_2690284).sum := by decide
  have hdescent : baseEnd_2690284 < baseStart_2690284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690297 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2690297 : Nat := 118140960795 + 2690297 * 2 ^ 59
def prefixEnd_2690297 : Nat := 4983230072969 + 3 ^ 40 * 2690297 * 2
def baseEnd_2690297 : Nat := 1381415464348965934315055

theorem tailTrace_2690297 : CollatzResearch.WordTrace tailWord_2690297 prefixEnd_2690297 1381415464348965934315055 := by
  unfold tailWord_2690297
  simp only [CollatzResearch.WordTrace]
  refine ⟨98123192734520909992741145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65415461823013939995160763 98123192734520909992741145)
  ·
    refine ⟨73592394550890682494555859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98123192734520909992741145 73592394550890682494555859)
    ·
      refine ⟨110388591826336023741833789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73592394550890682494555859 110388591826336023741833789)
      ·
        refine ⟨41395721934876008903187671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110388591826336023741833789 41395721934876008903187671)
        ·
          refine ⟨62093582902314013354781507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41395721934876008903187671 62093582902314013354781507)
          ·
            refine ⟨93140374353471020032172261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62093582902314013354781507 93140374353471020032172261)
            ·
              refine ⟨17463820191275816256032299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93140374353471020032172261 17463820191275816256032299)
              ·
                refine ⟨26195730286913724384048449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17463820191275816256032299 26195730286913724384048449)
                ·
                  refine ⟨19646797715185293288036337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26195730286913724384048449 19646797715185293288036337)
                  ·
                    refine ⟨14735098286388969966027253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19646797715185293288036337 14735098286388969966027253)
                    ·
                      refine ⟨1381415464348965934315055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14735098286388969966027253 1381415464348965934315055)
                      ·
                        rfl

theorem cell23_2690297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2690297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690297 prefixEnd_2690297 := by exact prefixLift 2690297
  have htrace : WordTrace (prefixWord ++ tailWord_2690297) baseStart_2690297 baseEnd_2690297 := by
    simpa [prefixWord, tailWord_2690297, baseEnd_2690297] using wordTrace_append hprefix tailTrace_2690297
  have hstable : (prefixWord ++ tailWord_2690297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690297).length < 2 ^ (prefixWord ++ tailWord_2690297).sum := by decide
  have hdescent : baseEnd_2690297 < baseStart_2690297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690302 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2690302 : Nat := 118140960795 + 2690302 * 2 ^ 59
def prefixEnd_2690302 : Nat := 4983230072969 + 3 ^ 40 * 2690302 * 2
def baseEnd_2690302 : Nat := 1381418031752238414752533

theorem tailTrace_2690302 : CollatzResearch.WordTrace tailWord_2690302 prefixEnd_2690302 1381418031752238414752533 := by
  unfold tailWord_2690302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265421887437849480834145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65415583399668530564448773 12265421887437849480834145)
  ·
    refine ⟨9199066415578387110625609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12265421887437849480834145 9199066415578387110625609)
    ·
      refine ⟨6899299811683790332969207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9199066415578387110625609 6899299811683790332969207)
      ·
        refine ⟨10348949717525685499453811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6899299811683790332969207 10348949717525685499453811)
        ·
          refine ⟨15523424576288528249180717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10348949717525685499453811 15523424576288528249180717)
          ·
            refine ⟨5821284216108198093442769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15523424576288528249180717 5821284216108198093442769)
            ·
              refine ⟨4365963162081148570082077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821284216108198093442769 4365963162081148570082077)
              ·
                refine ⟨1637236185780430713780779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4365963162081148570082077 1637236185780430713780779)
                ·
                  refine ⟨2455854278670646070671169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637236185780430713780779 2455854278670646070671169)
                  ·
                    refine ⟨1841890709002984553003377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2455854278670646070671169 1841890709002984553003377)
                    ·
                      refine ⟨1381418031752238414752533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1841890709002984553003377 1381418031752238414752533)
                      ·
                        rfl

theorem cell23_2690302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2690302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690302 prefixEnd_2690302 := by exact prefixLift 2690302
  have htrace : WordTrace (prefixWord ++ tailWord_2690302) baseStart_2690302 baseEnd_2690302 := by
    simpa [prefixWord, tailWord_2690302, baseEnd_2690302] using wordTrace_append hprefix tailTrace_2690302
  have hstable : (prefixWord ++ tailWord_2690302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690302).length < 2 ^ (prefixWord ++ tailWord_2690302).sum := by decide
  have hdescent : baseEnd_2690302 < baseStart_2690302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690318 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2690318 : Nat := 118140960795 + 2690318 * 2 ^ 59
def prefixEnd_2690318 : Nat := 4983230072969 + 3 ^ 40 * 2690318 * 2
def baseEnd_2690318 : Nat := 1381426247442710352152459

theorem tailTrace_2690318 : CollatzResearch.WordTrace tailWord_2690318 prefixEnd_2690318 1381426247442710352152459 := by
  unfold tailWord_2690318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265494833430603822406951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65415972444963220386170405 12265494833430603822406951)
  ·
    refine ⟨18398242250145905733610427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12265494833430603822406951 18398242250145905733610427)
    ·
      refine ⟨27597363375218858600415641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18398242250145905733610427 27597363375218858600415641)
      ·
        refine ⟨20698022531414143950311731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27597363375218858600415641 20698022531414143950311731)
        ·
          refine ⟨31047033797121215925467597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20698022531414143950311731 31047033797121215925467597)
          ·
            refine ⟨11642637673920455972050349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31047033797121215925467597 11642637673920455972050349)
            ·
              refine ⟨4365989127720170989518881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11642637673920455972050349 4365989127720170989518881)
              ·
                refine ⟨3274491845790128242139161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365989127720170989518881 3274491845790128242139161)
                ·
                  refine ⟨2455868884342596181604371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274491845790128242139161 2455868884342596181604371)
                  ·
                    refine ⟨3683803326513894272406557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455868884342596181604371 3683803326513894272406557)
                    ·
                      refine ⟨1381426247442710352152459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683803326513894272406557 1381426247442710352152459)
                      ·
                        rfl

theorem cell23_2690318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2690318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690318 prefixEnd_2690318 := by exact prefixLift 2690318
  have htrace : WordTrace (prefixWord ++ tailWord_2690318) baseStart_2690318 baseEnd_2690318 := by
    simpa [prefixWord, tailWord_2690318, baseEnd_2690318] using wordTrace_append hprefix tailTrace_2690318
  have hstable : (prefixWord ++ tailWord_2690318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690318).length < 2 ^ (prefixWord ++ tailWord_2690318).sum := by decide
  have hdescent : baseEnd_2690318 < baseStart_2690318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690335 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 2, 1, 3]
def baseStart_2690335 : Nat := 118140960795 + 2690335 * 2 ^ 59
def prefixEnd_2690335 : Nat := 4983230072969 + 3 ^ 40 * 2690335 * 2
def baseEnd_2690335 : Nat := 1381434976613836785639881

theorem tailTrace_2690335 : CollatzResearch.WordTrace tailWord_2690335 prefixEnd_2690335 1381434976613836785639881 := by
  unfold tailWord_2690335
  simp only [CollatzResearch.WordTrace]
  refine ⟨98124578708383242482624459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65416385805588828321749639 98124578708383242482624459)
  ·
    refine ⟨147186868062574863723936689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98124578708383242482624459 147186868062574863723936689)
    ·
      refine ⟨110390151046931147792952517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147186868062574863723936689 110390151046931147792952517)
      ·
        refine ⟨20698153321299590211178597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110390151046931147792952517 20698153321299590211178597)
        ·
          refine ⟨3880903747743673164595987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20698153321299590211178597 3880903747743673164595987)
          ·
            refine ⟨5821355621615509746893981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880903747743673164595987 5821355621615509746893981)
            ·
              refine ⟨2183008358105816155085243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5821355621615509746893981 2183008358105816155085243)
              ·
                refine ⟨3274512537158724232627865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183008358105816155085243 3274512537158724232627865)
                ·
                  refine ⟨2455884402869043174470899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274512537158724232627865 2455884402869043174470899)
                  ·
                    refine ⟨3683826604303564761706349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2455884402869043174470899 3683826604303564761706349)
                    ·
                      refine ⟨1381434976613836785639881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3683826604303564761706349 1381434976613836785639881)
                      ·
                        rfl

theorem cell23_2690335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_2690335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690335 prefixEnd_2690335 := by exact prefixLift 2690335
  have htrace : WordTrace (prefixWord ++ tailWord_2690335) baseStart_2690335 baseEnd_2690335 := by
    simpa [prefixWord, tailWord_2690335, baseEnd_2690335] using wordTrace_append hprefix tailTrace_2690335
  have hstable : (prefixWord ++ tailWord_2690335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690335).length < 2 ^ (prefixWord ++ tailWord_2690335).sum := by decide
  have hdescent : baseEnd_2690335 < baseStart_2690335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690361 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2690361 : Nat := 118140960795 + 2690361 * 2 ^ 59
def prefixEnd_2690361 : Nat := 4983230072969 + 3 ^ 40 * 2690361 * 2
def baseEnd_2690361 : Nat := 1381448327110853683914761

theorem tailTrace_2690361 : CollatzResearch.WordTrace tailWord_2690361 prefixEnd_2690361 1381448327110853683914761 := by
  unfold tailWord_2690361
  simp only [CollatzResearch.WordTrace]
  refine ⟨98125527006289048923070937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65417018004192699282047291 98125527006289048923070937)
  ·
    refine ⟨73594145254716786692303203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98125527006289048923070937 73594145254716786692303203)
    ·
      refine ⟨110391217882075180038454805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73594145254716786692303203 110391217882075180038454805)
      ·
        refine ⟨5174588338222274064302569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110391217882075180038454805 5174588338222274064302569)
        ·
          refine ⟨3880941253666705548226927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174588338222274064302569 3880941253666705548226927)
          ·
            refine ⟨5821411880500058322340391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880941253666705548226927 5821411880500058322340391)
            ·
              refine ⟨8732117820750087483510587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821411880500058322340391 8732117820750087483510587)
              ·
                refine ⟨13098176731125131225265881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8732117820750087483510587 13098176731125131225265881)
                ·
                  refine ⟨9823632548343848418949411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098176731125131225265881 9823632548343848418949411)
                  ·
                    refine ⟨14735448822515772628424117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9823632548343848418949411 14735448822515772628424117)
                    ·
                      refine ⟨1381448327110853683914761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14735448822515772628424117 1381448327110853683914761)
                      ·
                        rfl

theorem cell23_2690361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2690361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690361 prefixEnd_2690361 := by exact prefixLift 2690361
  have htrace : WordTrace (prefixWord ++ tailWord_2690361) baseStart_2690361 baseEnd_2690361 := by
    simpa [prefixWord, tailWord_2690361, baseEnd_2690361] using wordTrace_append hprefix tailTrace_2690361
  have hstable : (prefixWord ++ tailWord_2690361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690361).length < 2 ^ (prefixWord ++ tailWord_2690361).sum := by decide
  have hdescent : baseEnd_2690361 < baseStart_2690361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690462 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2690462 : Nat := 118140960795 + 2690462 * 2 ^ 59
def prefixEnd_2690462 : Nat := 4983230072969 + 3 ^ 40 * 2690462 * 2
def baseEnd_2690462 : Nat := 460500062885652596250599

theorem tailTrace_2690462 : CollatzResearch.WordTrace tailWord_2690462 prefixEnd_2690462 460500062885652596250599 := by
  unfold tailWord_2690462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266151347365392896562205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65419473852615428781665093 12266151347365392896562205)
  ·
    refine ⟨4599806755262022336210827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12266151347365392896562205 4599806755262022336210827)
    ·
      refine ⟨6899710132893033504316241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599806755262022336210827 6899710132893033504316241)
      ·
        refine ⟨5174782599669775128237181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6899710132893033504316241 5174782599669775128237181)
        ·
          refine ⟨1940543474876165673088943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5174782599669775128237181 1940543474876165673088943)
          ·
            refine ⟨2910815212314248509633415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940543474876165673088943 2910815212314248509633415)
            ·
              refine ⟨4366222818471372764450123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910815212314248509633415 4366222818471372764450123)
              ·
                refine ⟨6549334227707059146675185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366222818471372764450123 6549334227707059146675185)
                ·
                  refine ⟨4912000670780294360006389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6549334227707059146675185 4912000670780294360006389)
                  ·
                    refine ⟨460500062885652596250599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4912000670780294360006389 460500062885652596250599)
                    ·
                      rfl

theorem cell23_2690462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2690462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690462 prefixEnd_2690462 := by exact prefixLift 2690462
  have htrace : WordTrace (prefixWord ++ tailWord_2690462) baseStart_2690462 baseEnd_2690462 := by
    simpa [prefixWord, tailWord_2690462, baseEnd_2690462] using wordTrace_append hprefix tailTrace_2690462
  have hstable : (prefixWord ++ tailWord_2690462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690462).length < 2 ^ (prefixWord ++ tailWord_2690462).sum := by decide
  have hdescent : baseEnd_2690462 < baseStart_2690462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690508 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 5, 2]
def baseStart_2690508 : Nat := 118140960795 + 2690508 * 2 ^ 59
def prefixEnd_2690508 : Nat := 4983230072969 + 3 ^ 40 * 2690508 * 2
def baseEnd_2690508 : Nat := 1381523808767064608776585

theorem tailTrace_2690508 : CollatzResearch.WordTrace tailWord_2690508 prefixEnd_2690508 1381523808767064608776585 := by
  unfold tailWord_2690508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49065444268378246514336089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65420592357837662019114785 49065444268378246514336089)
  ·
    refine ⟨36799083201283684885752067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49065444268378246514336089 36799083201283684885752067)
    ·
      refine ⟨55198624801925527328628101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36799083201283684885752067 55198624801925527328628101)
      ·
        refine ⟨10349742150361036374117769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55198624801925527328628101 10349742150361036374117769)
        ·
          refine ⟨7762306612770777280588327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10349742150361036374117769 7762306612770777280588327)
          ·
            refine ⟨11643459919156165920882491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762306612770777280588327 11643459919156165920882491)
            ·
              refine ⟨17465189878734248881323737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643459919156165920882491 17465189878734248881323737)
              ·
                refine ⟨13098892409050686660992803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17465189878734248881323737 13098892409050686660992803)
                ·
                  refine ⟨19648338613576029991489205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13098892409050686660992803 19648338613576029991489205)
                  ·
                    refine ⟨1842031745022752811702113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19648338613576029991489205 1842031745022752811702113)
                    ·
                      refine ⟨1381523808767064608776585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842031745022752811702113 1381523808767064608776585)
                      ·
                        rfl

theorem cell23_2690508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_2690508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690508 prefixEnd_2690508 := by exact prefixLift 2690508
  have htrace : WordTrace (prefixWord ++ tailWord_2690508) baseStart_2690508 baseEnd_2690508 := by
    simpa [prefixWord, tailWord_2690508, baseEnd_2690508] using wordTrace_append hprefix tailTrace_2690508
  have hstable : (prefixWord ++ tailWord_2690508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690508).length < 2 ^ (prefixWord ++ tailWord_2690508).sum := by decide
  have hdescent : baseEnd_2690508 < baseStart_2690508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690544 : List Nat := [2, 1, 1, 1, 3, 4, 11]
def baseStart_2690544 : Nat := 118140960795 + 2690544 * 2 ^ 59
def prefixEnd_2690544 : Nat := 4983230072969 + 3 ^ 40 * 2690544 * 2
def baseEnd_2690544 : Nat := 17056077704575635406499

theorem tailTrace_2690544 : CollatzResearch.WordTrace tailWord_2690544 prefixEnd_2690544 17056077704575635406499 := by
  unfold tailWord_2690544
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066100782313035588491343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65421467709750714117988457 49066100782313035588491343)
  ·
    refine ⟨73599151173469553382737015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49066100782313035588491343 73599151173469553382737015)
    ·
      refine ⟨110398726760204330074105523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73599151173469553382737015 110398726760204330074105523)
      ·
        refine ⟨165598090140306495111158285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110398726760204330074105523 165598090140306495111158285)
        ·
          refine ⟨62099283802614935666684357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165598090140306495111158285 62099283802614935666684357)
          ·
            refine ⟨11643615712990300437503317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62099283802614935666684357 11643615712990300437503317)
            ·
              refine ⟨17056077704575635406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11643615712990300437503317 17056077704575635406499)
              ·
                rfl

theorem cell23_2690544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 11].length) (baseStart_2690544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690544 prefixEnd_2690544 := by exact prefixLift 2690544
  have htrace : WordTrace (prefixWord ++ tailWord_2690544) baseStart_2690544 baseEnd_2690544 := by
    simpa [prefixWord, tailWord_2690544, baseEnd_2690544] using wordTrace_append hprefix tailTrace_2690544
  have hstable : (prefixWord ++ tailWord_2690544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690544).length < 2 ^ (prefixWord ++ tailWord_2690544).sum := by decide
  have hdescent : baseEnd_2690544 < baseStart_2690544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690572 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 1, 1, 4]
def baseStart_2690572 : Nat := 118140960795 + 2690572 * 2 ^ 59
def prefixEnd_2690572 : Nat := 4983230072969 + 3 ^ 40 * 2690572 * 2
def baseEnd_2690572 : Nat := 1381556671528952358376291

theorem tailTrace_2690572 : CollatzResearch.WordTrace tailWord_2690572 prefixEnd_2690572 1381556671528952358376291 := by
  unfold tailWord_2690572
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066611404262315979500985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65422148539016421306001313 49066611404262315979500985)
  ·
    refine ⟨36799958553196736984625739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49066611404262315979500985 36799958553196736984625739)
    ·
      refine ⟨55199937829795105476938609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36799958553196736984625739 55199937829795105476938609)
      ·
        refine ⟨41399953372346329107703957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55199937829795105476938609 41399953372346329107703957)
        ·
          refine ⟨1940622814328734176923623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41399953372346329107703957 1940622814328734176923623)
          ·
            refine ⟨2910934221493101265385435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940622814328734176923623 2910934221493101265385435)
            ·
              refine ⟨4366401332239651898078153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2910934221493101265385435 4366401332239651898078153)
              ·
                refine ⟨3274800999179738923558615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366401332239651898078153 3274800999179738923558615)
                ·
                  refine ⟨4912201498769608385337923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274800999179738923558615 4912201498769608385337923)
                  ·
                    refine ⟨7368302248154412578006885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4912201498769608385337923 7368302248154412578006885)
                    ·
                      refine ⟨1381556671528952358376291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7368302248154412578006885 1381556671528952358376291)
                      ·
                        rfl

theorem cell23_2690572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_2690572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690572 prefixEnd_2690572 := by exact prefixLift 2690572
  have htrace : WordTrace (prefixWord ++ tailWord_2690572) baseStart_2690572 baseEnd_2690572 := by
    simpa [prefixWord, tailWord_2690572, baseEnd_2690572] using wordTrace_append hprefix tailTrace_2690572
  have hstable : (prefixWord ++ tailWord_2690572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690572).length < 2 ^ (prefixWord ++ tailWord_2690572).sum := by decide
  have hdescent : baseEnd_2690572 < baseStart_2690572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690588 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2690588 : Nat := 118140960795 + 2690588 * 2 ^ 59
def prefixEnd_2690588 : Nat := 4983230072969 + 3 ^ 40 * 2690588 * 2
def baseEnd_2690588 : Nat := 1381564887219424295776217

theorem tailTrace_2690588 : CollatzResearch.WordTrace tailWord_2690588 prefixEnd_2690588 1381564887219424295776217 := by
  unfold tailWord_2690588
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066903188233333345792209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65422537584311111127722945 49066903188233333345792209)
  ·
    refine ⟨36800177391175000009344157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49066903188233333345792209 36800177391175000009344157)
    ·
      refine ⟨13800066521690625003504059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36800177391175000009344157 13800066521690625003504059)
      ·
        refine ⟨20700099782535937505256089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13800066521690625003504059 20700099782535937505256089)
        ·
          refine ⟨15525074836901953128942067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20700099782535937505256089 15525074836901953128942067)
          ·
            refine ⟨23287612255352929693413101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15525074836901953128942067 23287612255352929693413101)
            ·
              refine ⟨8732854595757348635029913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23287612255352929693413101 8732854595757348635029913)
              ·
                refine ⟨6549640946818011476272435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8732854595757348635029913 6549640946818011476272435)
                ·
                  refine ⟨9824461420227017214408653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6549640946818011476272435 9824461420227017214408653)
                  ·
                    refine ⟨3684173032585131455403245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9824461420227017214408653 3684173032585131455403245)
                    ·
                      refine ⟨1381564887219424295776217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684173032585131455403245 1381564887219424295776217)
                      ·
                        rfl

theorem cell23_2690588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2690588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690588 prefixEnd_2690588 := by exact prefixLift 2690588
  have htrace : WordTrace (prefixWord ++ tailWord_2690588) baseStart_2690588 baseEnd_2690588 := by
    simpa [prefixWord, tailWord_2690588, baseEnd_2690588] using wordTrace_append hprefix tailTrace_2690588
  have hstable : (prefixWord ++ tailWord_2690588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690588).length < 2 ^ (prefixWord ++ tailWord_2690588).sum := by decide
  have hdescent : baseEnd_2690588 < baseStart_2690588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690592 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2690592 : Nat := 118140960795 + 2690592 * 2 ^ 59
def prefixEnd_2690592 : Nat := 4983230072969 + 3 ^ 40 * 2690592 * 2
def baseEnd_2690592 : Nat := 1381566941142042280126199

theorem tailTrace_2690592 : CollatzResearch.WordTrace tailWord_2690592 prefixEnd_2690592 1381566941142042280126199 := by
  unfold tailWord_2690592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066976134226087687365015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65422634845634783583153353 49066976134226087687365015)
  ·
    refine ⟨73600464201339131531047523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49066976134226087687365015 73600464201339131531047523)
    ·
      refine ⟨110400696302008697296571285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73600464201339131531047523 110400696302008697296571285)
      ·
        refine ⟨5175032639156657685776779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110400696302008697296571285 5175032639156657685776779)
        ·
          refine ⟨7762548958734986528665169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175032639156657685776779 7762548958734986528665169)
          ·
            refine ⟨5821911719051239896498877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7762548958734986528665169 5821911719051239896498877)
            ·
              refine ⟨2183216894644214961187079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5821911719051239896498877 2183216894644214961187079)
              ·
                refine ⟨3274825341966322441780619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183216894644214961187079 3274825341966322441780619)
                ·
                  refine ⟨4912238012949483662670929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274825341966322441780619 4912238012949483662670929)
                  ·
                    refine ⟨3684178509712112747003197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912238012949483662670929 3684178509712112747003197)
                    ·
                      refine ⟨1381566941142042280126199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684178509712112747003197 1381566941142042280126199)
                      ·
                        rfl

theorem cell23_2690592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2690592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690592 prefixEnd_2690592 := by exact prefixLift 2690592
  have htrace : WordTrace (prefixWord ++ tailWord_2690592) baseStart_2690592 baseEnd_2690592 := by
    simpa [prefixWord, tailWord_2690592, baseEnd_2690592] using wordTrace_append hprefix tailTrace_2690592
  have hstable : (prefixWord ++ tailWord_2690592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690592).length < 2 ^ (prefixWord ++ tailWord_2690592).sum := by decide
  have hdescent : baseEnd_2690592 < baseStart_2690592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690606 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2690606 : Nat := 118140960795 + 2690606 * 2 ^ 59
def prefixEnd_2690606 : Nat := 4983230072969 + 3 ^ 40 * 2690606 * 2
def baseEnd_2690606 : Nat := 1381574129871205225351135

theorem tailTrace_2690606 : CollatzResearch.WordTrace tailWord_2690606 prefixEnd_2690606 1381574129871205225351135 := by
  unfold tailWord_2690606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266807861300181970717459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65422975260267637177159781 12266807861300181970717459)
  ·
    refine ⟨18400211791950272956076189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12266807861300181970717459 18400211791950272956076189)
    ·
      refine ⟨6900079421981352358528571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18400211791950272956076189 6900079421981352358528571)
      ·
        refine ⟨10350119132972028537792857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6900079421981352358528571 10350119132972028537792857)
        ·
          refine ⟨7762589349729021403344643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10350119132972028537792857 7762589349729021403344643)
          ·
            refine ⟨11643884024593532105016965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762589349729021403344643 11643884024593532105016965)
            ·
              refine ⟨2183228254611287269690681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11643884024593532105016965 2183228254611287269690681)
              ·
                refine ⟨1637421190958465452268011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183228254611287269690681 1637421190958465452268011)
                ·
                  refine ⟨2456131786437698178402017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637421190958465452268011 2456131786437698178402017)
                  ·
                    refine ⟨1842098839828273633801513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456131786437698178402017 1842098839828273633801513)
                    ·
                      refine ⟨1381574129871205225351135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842098839828273633801513 1381574129871205225351135)
                      ·
                        rfl

theorem cell23_2690606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2690606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690606 prefixEnd_2690606 := by exact prefixLift 2690606
  have htrace : WordTrace (prefixWord ++ tailWord_2690606) baseStart_2690606 baseEnd_2690606 := by
    simpa [prefixWord, tailWord_2690606, baseEnd_2690606] using wordTrace_append hprefix tailTrace_2690606
  have hstable : (prefixWord ++ tailWord_2690606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690606).length < 2 ^ (prefixWord ++ tailWord_2690606).sum := by decide
  have hdescent : baseEnd_2690606 < baseStart_2690606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690611 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_2690611 : Nat := 118140960795 + 2690611 * 2 ^ 59
def prefixEnd_2690611 : Nat := 4983230072969 + 3 ^ 40 * 2690611 * 2
def baseEnd_2690611 : Nat := 1381576697274477705788611

theorem tailTrace_2690611 : CollatzResearch.WordTrace tailWord_2690611 prefixEnd_2690611 1381576697274477705788611 := by
  unfold tailWord_2690611
  simp only [CollatzResearch.WordTrace]
  refine ⟨98134645255383341619671687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65423096836922227746447791 98134645255383341619671687)
  ·
    refine ⟨147201967883075012429507531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98134645255383341619671687 147201967883075012429507531)
    ·
      refine ⟨220802951824612518644261297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147201967883075012429507531 220802951824612518644261297)
      ·
        refine ⟨165602213868459388983195973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220802951824612518644261297 165602213868459388983195973)
        ·
          refine ⟨31050415100336135434349245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165602213868459388983195973 31050415100336135434349245)
          ·
            refine ⟨11643905662626050787880967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31050415100336135434349245 11643905662626050787880967)
            ·
              refine ⟨17465858493939076181821451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11643905662626050787880967 17465858493939076181821451)
              ·
                refine ⟨26198787740908614272732177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17465858493939076181821451 26198787740908614272732177)
                ·
                  refine ⟨19649090805681460704549133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26198787740908614272732177 19649090805681460704549133)
                  ·
                    refine ⟨7368409052130547764205925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19649090805681460704549133 7368409052130547764205925)
                    ·
                      refine ⟨1381576697274477705788611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7368409052130547764205925 1381576697274477705788611)
                      ·
                        rfl

theorem cell23_2690611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_2690611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690611 prefixEnd_2690611 := by exact prefixLift 2690611
  have htrace : WordTrace (prefixWord ++ tailWord_2690611) baseStart_2690611 baseEnd_2690611 := by
    simpa [prefixWord, tailWord_2690611, baseEnd_2690611] using wordTrace_append hprefix tailTrace_2690611
  have hstable : (prefixWord ++ tailWord_2690611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690611).length < 2 ^ (prefixWord ++ tailWord_2690611).sum := by decide
  have hdescent : baseEnd_2690611 < baseStart_2690611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690641 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2690641 : Nat := 118140960795 + 2690641 * 2 ^ 59
def prefixEnd_2690641 : Nat := 4983230072969 + 3 ^ 40 * 2690641 * 2
def baseEnd_2690641 : Nat := 1381592101694112588413473

theorem tailTrace_2690641 : CollatzResearch.WordTrace tailWord_2690641 prefixEnd_2690641 1381592101694112588413473 := by
  unfold tailWord_2690641
  simp only [CollatzResearch.WordTrace]
  refine ⟨98135739445274656743263777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65423826296849771162175851 98135739445274656743263777)
  ·
    refine ⟨73601804583955992557447833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98135739445274656743263777 73601804583955992557447833)
    ·
      refine ⟨55201353437966994418085875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73601804583955992557447833 55201353437966994418085875)
      ·
        refine ⟨82802030156950491627128813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55201353437966994418085875 82802030156950491627128813)
        ·
          refine ⟨31050761308856434360173305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82802030156950491627128813 31050761308856434360173305)
          ·
            refine ⟨23288070981642325770129979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31050761308856434360173305 23288070981642325770129979)
            ·
              refine ⟨34932106472463488655194969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23288070981642325770129979 34932106472463488655194969)
              ·
                refine ⟨26199079854347616491396227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34932106472463488655194969 26199079854347616491396227)
                ·
                  refine ⟨39298619781521424737094341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26199079854347616491396227 39298619781521424737094341)
                  ·
                    refine ⟨7368491209035267138205189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39298619781521424737094341 7368491209035267138205189)
                    ·
                      refine ⟨1381592101694112588413473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7368491209035267138205189 1381592101694112588413473)
                      ·
                        rfl

theorem cell23_2690641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2690641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690641 prefixEnd_2690641 := by exact prefixLift 2690641
  have htrace : WordTrace (prefixWord ++ tailWord_2690641) baseStart_2690641 baseEnd_2690641 := by
    simpa [prefixWord, tailWord_2690641, baseEnd_2690641] using wordTrace_append hprefix tailTrace_2690641
  have hstable : (prefixWord ++ tailWord_2690641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690641).length < 2 ^ (prefixWord ++ tailWord_2690641).sum := by decide
  have hdescent : baseEnd_2690641 < baseStart_2690641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690645 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2690645 : Nat := 118140960795 + 2690645 * 2 ^ 59
def prefixEnd_2690645 : Nat := 4983230072969 + 3 ^ 40 * 2690645 * 2
def baseEnd_2690645 : Nat := 1381594155616730572763455

theorem tailTrace_2690645 : CollatzResearch.WordTrace tailWord_2690645 prefixEnd_2690645 1381594155616730572763455 := by
  unfold tailWord_2690645
  simp only [CollatzResearch.WordTrace]
  refine ⟨98135885337260165426409389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65423923558173443617606259 98135885337260165426409389)
  ·
    refine ⟨36800957001472562034903521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98135885337260165426409389 36800957001472562034903521)
    ·
      refine ⟨27600717751104421526177641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36800957001472562034903521 27600717751104421526177641)
      ·
        refine ⟨20700538313328316144633231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27600717751104421526177641 20700538313328316144633231)
        ·
          refine ⟨31050807469992474216949847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20700538313328316144633231 31050807469992474216949847)
          ·
            refine ⟨46576211204988711325424771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31050807469992474216949847 46576211204988711325424771)
            ·
              refine ⟨69864316807483066988137157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46576211204988711325424771 69864316807483066988137157)
              ·
                refine ⟨13099559401403075060275717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69864316807483066988137157 13099559401403075060275717)
                ·
                  refine ⟨2456167387763076573801697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13099559401403075060275717 2456167387763076573801697)
                  ·
                    refine ⟨1842125540822307430351273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456167387763076573801697 1842125540822307430351273)
                    ·
                      refine ⟨1381594155616730572763455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842125540822307430351273 1381594155616730572763455)
                      ·
                        rfl

theorem cell23_2690645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2690645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690645 prefixEnd_2690645 := by exact prefixLift 2690645
  have htrace : WordTrace (prefixWord ++ tailWord_2690645) baseStart_2690645 baseEnd_2690645 := by
    simpa [prefixWord, tailWord_2690645, baseEnd_2690645] using wordTrace_append hprefix tailTrace_2690645
  have hstable : (prefixWord ++ tailWord_2690645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690645).length < 2 ^ (prefixWord ++ tailWord_2690645).sum := by decide
  have hdescent : baseEnd_2690645 < baseStart_2690645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690681 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 3, 7]
def baseStart_2690681 : Nat := 118140960795 + 2690681 * 2 ^ 59
def prefixEnd_2690681 : Nat := 4983230072969 + 3 ^ 40 * 2690681 * 2
def baseEnd_2690681 : Nat := 460537546973430810637763

theorem tailTrace_2690681 : CollatzResearch.WordTrace tailWord_2690681 prefixEnd_2690681 460537546973430810637763 := by
  unfold tailWord_2690681
  simp only [CollatzResearch.WordTrace]
  refine ⟨98137198365129743574719897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65424798910086495716479931 98137198365129743574719897)
  ·
    refine ⟨73602898773847307681039923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98137198365129743574719897 73602898773847307681039923)
    ·
      refine ⟨110404348160770961521559885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73602898773847307681039923 110404348160770961521559885)
      ·
        refine ⟨41401630560289110570584957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110404348160770961521559885 41401630560289110570584957)
        ·
          refine ⟨15525611460108416463969359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41401630560289110570584957 15525611460108416463969359)
          ·
            refine ⟨23288417190162624695954039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15525611460108416463969359 23288417190162624695954039)
            ·
              refine ⟨34932625785243937043931059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23288417190162624695954039 34932625785243937043931059)
              ·
                refine ⟨52398938677865905565896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34932625785243937043931059 52398938677865905565896589)
                ·
                  refine ⟨19649602004199714587211221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52398938677865905565896589 19649602004199714587211221)
                  ·
                    refine ⟨460537546973430810637763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19649602004199714587211221 460537546973430810637763)
                    ·
                      rfl

theorem cell23_2690681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_2690681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690681 prefixEnd_2690681 := by exact prefixLift 2690681
  have htrace : WordTrace (prefixWord ++ tailWord_2690681) baseStart_2690681 baseEnd_2690681 := by
    simpa [prefixWord, tailWord_2690681, baseEnd_2690681] using wordTrace_append hprefix tailTrace_2690681
  have hstable : (prefixWord ++ tailWord_2690681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690681).length < 2 ^ (prefixWord ++ tailWord_2690681).sum := by decide
  have hdescent : baseEnd_2690681 < baseStart_2690681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690691 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2690691 : Nat := 118140960795 + 2690691 * 2 ^ 59
def prefixEnd_2690691 : Nat := 4983230072969 + 3 ^ 40 * 2690691 * 2
def baseEnd_2690691 : Nat := 1381617775726837392788243

theorem tailTrace_2690691 : CollatzResearch.WordTrace tailWord_2690691 prefixEnd_2690691 1381617775726837392788243 := by
  unfold tailWord_2690691
  simp only [CollatzResearch.WordTrace]
  refine ⟨98137563095093515282583927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65425042063395676855055951 98137563095093515282583927)
  ·
    refine ⟨147206344642640272923875891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98137563095093515282583927 147206344642640272923875891)
    ·
      refine ⟨220809516963960409385813837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147206344642640272923875891 220809516963960409385813837)
      ·
        refine ⟨82803568861485153519680189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220809516963960409385813837 82803568861485153519680189)
        ·
          refine ⟨31051338323056932569880071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82803568861485153519680189 31051338323056932569880071)
          ·
            refine ⟨46577007484585398854820107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31051338323056932569880071 46577007484585398854820107)
            ·
              refine ⟨69865511226878098282230161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46577007484585398854820107 69865511226878098282230161)
              ·
                refine ⟨52399133420158573711672621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69865511226878098282230161 52399133420158573711672621)
                ·
                  refine ⟨19649675032559465141877233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52399133420158573711672621 19649675032559465141877233)
                  ·
                    refine ⟨14737256274419598856407925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19649675032559465141877233 14737256274419598856407925)
                    ·
                      refine ⟨1381617775726837392788243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14737256274419598856407925 1381617775726837392788243)
                      ·
                        rfl

theorem cell23_2690691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2690691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690691 prefixEnd_2690691 := by exact prefixLift 2690691
  have htrace : WordTrace (prefixWord ++ tailWord_2690691) baseStart_2690691 baseEnd_2690691 := by
    simpa [prefixWord, tailWord_2690691, baseEnd_2690691] using wordTrace_append hprefix tailTrace_2690691
  have hstable : (prefixWord ++ tailWord_2690691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690691).length < 2 ^ (prefixWord ++ tailWord_2690691).sum := by decide
  have hdescent : baseEnd_2690691 < baseStart_2690691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690698 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_2690698 : Nat := 118140960795 + 2690698 * 2 ^ 59
def prefixEnd_2690698 : Nat := 4983230072969 + 3 ^ 40 * 2690698 * 2
def baseEnd_2690698 : Nat := 460540456697139621800237

theorem tailTrace_2690698 : CollatzResearch.WordTrace tailWord_2690698 prefixEnd_2690698 460540456697139621800237 := by
  unfold tailWord_2690698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534454601517038869522187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65425212270712103652059165 24534454601517038869522187)
  ·
    refine ⟨36801681902275558304283281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24534454601517038869522187 36801681902275558304283281)
    ·
      refine ⟨27601261426706668728212461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36801681902275558304283281 27601261426706668728212461)
      ·
        refine ⟨10350473035015000773079673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27601261426706668728212461 10350473035015000773079673)
        ·
          refine ⟨7762854776261250579809755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10350473035015000773079673 7762854776261250579809755)
          ·
            refine ⟨11644282164391875869714633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762854776261250579809755 11644282164391875869714633)
            ·
              refine ⟨8733211623293906902285975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11644282164391875869714633 8733211623293906902285975)
              ·
                refine ⟨13099817434940860353428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733211623293906902285975 13099817434940860353428963)
                ·
                  refine ⟨19649726152411290530143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13099817434940860353428963 19649726152411290530143445)
                  ·
                    refine ⟨460540456697139621800237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19649726152411290530143445 460540456697139621800237)
                    ·
                      rfl

theorem cell23_2690698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_2690698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690698 prefixEnd_2690698 := by exact prefixLift 2690698
  have htrace : WordTrace (prefixWord ++ tailWord_2690698) baseStart_2690698 baseEnd_2690698 := by
    simpa [prefixWord, tailWord_2690698, baseEnd_2690698] using wordTrace_append hprefix tailTrace_2690698
  have hstable : (prefixWord ++ tailWord_2690698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690698).length < 2 ^ (prefixWord ++ tailWord_2690698).sum := by decide
  have hdescent : baseEnd_2690698 < baseStart_2690698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690702 : List Nat := [4, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_2690702 : Nat := 118140960795 + 2690702 * 2 ^ 59
def prefixEnd_2690702 : Nat := 4983230072969 + 3 ^ 40 * 2690702 * 2
def baseEnd_2690702 : Nat := 153513713779337427750077

theorem tailTrace_2690702 : CollatzResearch.WordTrace tailWord_2690702 prefixEnd_2690702 153513713779337427750077 := by
  unfold tailWord_2690702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267245537256708020154295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65425309532035776107489573 12267245537256708020154295)
  ·
    refine ⟨18400868305885062030231443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12267245537256708020154295 18400868305885062030231443)
    ·
      refine ⟨27601302458827593045347165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18400868305885062030231443 27601302458827593045347165)
      ·
        refine ⟨10350488422060347392005187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27601302458827593045347165 10350488422060347392005187)
        ·
          refine ⟨15525732633090521088007781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350488422060347392005187 15525732633090521088007781)
          ·
            refine ⟨2911074868704472704001459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15525732633090521088007781 2911074868704472704001459)
            ·
              refine ⟨4366612303056709056002189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911074868704472704001459 4366612303056709056002189)
              ·
                refine ⟨1637479613646265896000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4366612303056709056002189 1637479613646265896000821)
                ·
                  refine ⟨153513713779337427750077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637479613646265896000821 153513713779337427750077)
                  ·
                    rfl

theorem cell23_2690702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_2690702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690702 prefixEnd_2690702 := by exact prefixLift 2690702
  have htrace : WordTrace (prefixWord ++ tailWord_2690702) baseStart_2690702 baseEnd_2690702 := by
    simpa [prefixWord, tailWord_2690702, baseEnd_2690702] using wordTrace_append hprefix tailTrace_2690702
  have hstable : (prefixWord ++ tailWord_2690702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690702).length < 2 ^ (prefixWord ++ tailWord_2690702).sum := by decide
  have hdescent : baseEnd_2690702 < baseStart_2690702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690719 : List Nat := [1, 1, 2, 7, 1, 1, 3, 2, 5]
def baseStart_2690719 : Nat := 118140960795 + 2690719 * 2 ^ 59
def prefixEnd_2690719 : Nat := 4983230072969 + 3 ^ 40 * 2690719 * 2
def baseEnd_2690719 : Nat := 153514683687240364804235

theorem tailTrace_2690719 : CollatzResearch.WordTrace tailWord_2690719 prefixEnd_2690719 153514683687240364804235 := by
  unfold tailWord_2690719
  simp only [CollatzResearch.WordTrace]
  refine ⟨98138584338992076064603211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65425722892661384043068807 98138584338992076064603211)
  ·
    refine ⟨147207876508488114096904817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98138584338992076064603211 147207876508488114096904817)
    ·
      refine ⟨110405907381366085572678613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147207876508488114096904817 110405907381366085572678613)
      ·
        refine ⟨2587638454250767630609655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 110405907381366085572678613 2587638454250767630609655)
        ·
          refine ⟨3881457681376151445914483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587638454250767630609655 3881457681376151445914483)
          ·
            refine ⟨5822186522064227168871725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881457681376151445914483 5822186522064227168871725)
            ·
              refine ⟨2183319945774085188326897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5822186522064227168871725 2183319945774085188326897)
              ·
                refine ⟨1637489959330563891245173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183319945774085188326897 1637489959330563891245173)
                ·
                  refine ⟨153514683687240364804235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637489959330563891245173 153514683687240364804235)
                  ·
                    rfl

theorem cell23_2690719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 5].length) (baseStart_2690719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690719 prefixEnd_2690719 := by exact prefixLift 2690719
  have htrace : WordTrace (prefixWord ++ tailWord_2690719) baseStart_2690719 baseEnd_2690719 := by
    simpa [prefixWord, tailWord_2690719, baseEnd_2690719] using wordTrace_append hprefix tailTrace_2690719
  have hstable : (prefixWord ++ tailWord_2690719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690719).length < 2 ^ (prefixWord ++ tailWord_2690719).sum := by decide
  have hdescent : baseEnd_2690719 < baseStart_2690719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690738 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_2690738 : Nat := 118140960795 + 2690738 * 2 ^ 59
def prefixEnd_2690738 : Nat := 4983230072969 + 3 ^ 40 * 2690738 * 2
def baseEnd_2690738 : Nat := 1381641909317598708900527

theorem tailTrace_2690738 : CollatzResearch.WordTrace tailWord_2690738 prefixEnd_2690738 1381641909317598708900527 := by
  unfold tailWord_2690738
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534819331480810577386217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65426184883948828206363245 24534819331480810577386217)
  ·
    refine ⟨18401114498610607933039663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24534819331480810577386217 18401114498610607933039663)
    ·
      refine ⟨27601671747915911899559495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401114498610607933039663 27601671747915911899559495)
      ·
        refine ⟨41402507621873867849339243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27601671747915911899559495 41402507621873867849339243)
        ·
          refine ⟨62103761432810801774008865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41402507621873867849339243 62103761432810801774008865)
          ·
            refine ⟨46577821074608101330506649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62103761432810801774008865 46577821074608101330506649)
            ·
              refine ⟨34933365805956075997879987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46577821074608101330506649 34933365805956075997879987)
              ·
                refine ⟨52400048708934113996819981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34933365805956075997879987 52400048708934113996819981)
                ·
                  refine ⟨19650018265850292748807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52400048708934113996819981 19650018265850292748807493)
                  ·
                    refine ⟨3684378424846929890401405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19650018265850292748807493 3684378424846929890401405)
                    ·
                      refine ⟨1381641909317598708900527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684378424846929890401405 1381641909317598708900527)
                      ·
                        rfl

theorem cell23_2690738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_2690738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690738 prefixEnd_2690738 := by exact prefixLift 2690738
  have htrace : WordTrace (prefixWord ++ tailWord_2690738) baseStart_2690738 baseEnd_2690738 := by
    simpa [prefixWord, tailWord_2690738, baseEnd_2690738] using wordTrace_append hprefix tailTrace_2690738
  have hstable : (prefixWord ++ tailWord_2690738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690738).length < 2 ^ (prefixWord ++ tailWord_2690738).sum := by decide
  have hdescent : baseEnd_2690738 < baseStart_2690738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690771 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 9]
def baseStart_2690771 : Nat := 118140960795 + 2690771 * 2 ^ 59
def prefixEnd_2690771 : Nat := 4983230072969 + 3 ^ 40 * 2690771 * 2
def baseEnd_2690771 : Nat := 460552951393065693262625

theorem tailTrace_2690771 : CollatzResearch.WordTrace tailWord_2690771 prefixEnd_2690771 460552951393065693262625 := by
  unfold tailWord_2690771
  simp only [CollatzResearch.WordTrace]
  refine ⟨98140480934803688945496167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65426987289869125963664111 98140480934803688945496167)
  ·
    refine ⟨147210721402205533418244251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98140480934803688945496167 147210721402205533418244251)
    ·
      refine ⟨220816082103308300127366377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147210721402205533418244251 220816082103308300127366377)
      ·
        refine ⟨165612061577481225095524783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220816082103308300127366377 165612061577481225095524783)
        ·
          refine ⟨248418092366221837643287175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165612061577481225095524783 248418092366221837643287175)
          ·
            refine ⟨372627138549332756464930763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248418092366221837643287175 372627138549332756464930763)
            ·
              refine ⟨558940707823999134697396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372627138549332756464930763 558940707823999134697396145)
              ·
                refine ⟨419205530867999351023047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558940707823999134697396145 419205530867999351023047109)
                ·
                  refine ⟨78601037037749878316821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419205530867999351023047109 78601037037749878316821333)
                  ·
                    refine ⟨460552951393065693262625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78601037037749878316821333 460552951393065693262625)
                    ·
                      rfl

theorem cell23_2690771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_2690771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690771 prefixEnd_2690771 := by exact prefixLift 2690771
  have htrace : WordTrace (prefixWord ++ tailWord_2690771) baseStart_2690771 baseEnd_2690771 := by
    simpa [prefixWord, tailWord_2690771, baseEnd_2690771] using wordTrace_append hprefix tailTrace_2690771
  have hstable : (prefixWord ++ tailWord_2690771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690771).length < 2 ^ (prefixWord ++ tailWord_2690771).sum := by decide
  have hdescent : baseEnd_2690771 < baseStart_2690771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690772 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2690772 : Nat := 118140960795 + 2690772 * 2 ^ 59
def prefixEnd_2690772 : Nat := 4983230072969 + 3 ^ 40 * 2690772 * 2
def baseEnd_2690772 : Nat := 1381659367659851575875371

theorem tailTrace_2690772 : CollatzResearch.WordTrace tailWord_2690772 prefixEnd_2690772 1381659367659851575875371 := by
  unfold tailWord_2690772
  simp only [CollatzResearch.WordTrace]
  refine ⟨49070258703900033058141285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65427011605200044077521713 49070258703900033058141285)
  ·
    refine ⟨9200673506981256198401491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49070258703900033058141285 9200673506981256198401491)
    ·
      refine ⟨13801010260471884297602237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200673506981256198401491 13801010260471884297602237)
      ·
        refine ⟨5175378847676956611600839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13801010260471884297602237 5175378847676956611600839)
        ·
          refine ⟨7763068271515434917401259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175378847676956611600839 7763068271515434917401259)
          ·
            refine ⟨11644602407273152376101889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763068271515434917401259 11644602407273152376101889)
            ·
              refine ⟨8733451805454864282076417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11644602407273152376101889 8733451805454864282076417)
              ·
                refine ⟨6550088854091148211557313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8733451805454864282076417 6550088854091148211557313)
                ·
                  refine ⟨4912566640568361158667985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550088854091148211557313 4912566640568361158667985)
                  ·
                    refine ⟨3684424980426270869000989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4912566640568361158667985 3684424980426270869000989)
                    ·
                      refine ⟨1381659367659851575875371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684424980426270869000989 1381659367659851575875371)
                      ·
                        rfl

theorem cell23_2690772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2690772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690772 prefixEnd_2690772 := by exact prefixLift 2690772
  have htrace : WordTrace (prefixWord ++ tailWord_2690772) baseStart_2690772 baseEnd_2690772 := by
    simpa [prefixWord, tailWord_2690772, baseEnd_2690772] using wordTrace_append hprefix tailTrace_2690772
  have hstable : (prefixWord ++ tailWord_2690772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690772).length < 2 ^ (prefixWord ++ tailWord_2690772).sum := by decide
  have hdescent : baseEnd_2690772 < baseStart_2690772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690788 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_2690788 : Nat := 118140960795 + 2690788 * 2 ^ 59
def prefixEnd_2690788 : Nat := 4983230072969 + 3 ^ 40 * 2690788 * 2
def baseEnd_2690788 : Nat := 460555861116774504425099

theorem tailTrace_2690788 : CollatzResearch.WordTrace tailWord_2690788 prefixEnd_2690788 460555861116774504425099 := by
  unfold tailWord_2690788
  simp only [CollatzResearch.WordTrace]
  refine ⟨49070550487871050424432509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65427400650494733899243345 49070550487871050424432509)
  ·
    refine ⟨18401456432951643909162191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49070550487871050424432509 18401456432951643909162191)
    ·
      refine ⟨27602184649427465863743287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401456432951643909162191 27602184649427465863743287)
      ·
        refine ⟨41403276974141198795614931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27602184649427465863743287 41403276974141198795614931)
        ·
          refine ⟨62104915461211798193422397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41403276974141198795614931 62104915461211798193422397)
          ·
            refine ⟨23289343297954424322533399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62104915461211798193422397 23289343297954424322533399)
            ·
              refine ⟨34934014946931636483800099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23289343297954424322533399 34934014946931636483800099)
              ·
                refine ⟨52401022420397454725700149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34934014946931636483800099 52401022420397454725700149)
                ·
                  refine ⟨4912595851912261380534389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52401022420397454725700149 4912595851912261380534389)
                  ·
                    refine ⟨460555861116774504425099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4912595851912261380534389 460555861116774504425099)
                    ·
                      rfl

theorem cell23_2690788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_2690788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690788 prefixEnd_2690788 := by exact prefixLift 2690788
  have htrace : WordTrace (prefixWord ++ tailWord_2690788) baseStart_2690788 baseEnd_2690788 := by
    simpa [prefixWord, tailWord_2690788, baseEnd_2690788] using wordTrace_append hprefix tailTrace_2690788
  have hstable : (prefixWord ++ tailWord_2690788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690788).length < 2 ^ (prefixWord ++ tailWord_2690788).sum := by decide
  have hdescent : baseEnd_2690788 < baseStart_2690788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690795 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 4, 3, 2]
def baseStart_2690795 : Nat := 118140960795 + 2690795 * 2 ^ 59
def prefixEnd_2690795 : Nat := 4983230072969 + 3 ^ 40 * 2690795 * 2
def baseEnd_2690795 : Nat := 1381671177714904985887765

theorem tailTrace_2690795 : CollatzResearch.WordTrace tailWord_2690795 prefixEnd_2690795 1381671177714904985887765 := by
  unfold tailWord_2690795
  simp only [CollatzResearch.WordTrace]
  refine ⟨98141356286716741044369839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65427570857811160696246559 98141356286716741044369839)
  ·
    refine ⟨147212034430075111566554759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98141356286716741044369839 147212034430075111566554759)
    ·
      refine ⟨220818051645112667349832139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147212034430075111566554759 220818051645112667349832139)
      ·
        refine ⟨331227077467669001024748209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220818051645112667349832139 331227077467669001024748209)
        ·
          refine ⟨248420308100751750768561157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331227077467669001024748209 248420308100751750768561157)
          ·
            refine ⟨46578807768890953269105217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248420308100751750768561157 46578807768890953269105217)
            ·
              refine ⟨34934105826668214951828913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46578807768890953269105217 34934105826668214951828913)
              ·
                refine ⟨26200579370001161213871685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34934105826668214951828913 26200579370001161213871685)
                ·
                  refine ⟨4912608631875217727600941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26200579370001161213871685 4912608631875217727600941)
                  ·
                    refine ⟨1842228236953206647850353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4912608631875217727600941 1842228236953206647850353)
                    ·
                      refine ⟨1381671177714904985887765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842228236953206647850353 1381671177714904985887765)
                      ·
                        rfl

theorem cell23_2690795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 3, 2].length) (baseStart_2690795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690795 prefixEnd_2690795 := by exact prefixLift 2690795
  have htrace : WordTrace (prefixWord ++ tailWord_2690795) baseStart_2690795 baseEnd_2690795 := by
    simpa [prefixWord, tailWord_2690795, baseEnd_2690795] using wordTrace_append hprefix tailTrace_2690795
  have hstable : (prefixWord ++ tailWord_2690795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690795).length < 2 ^ (prefixWord ++ tailWord_2690795).sum := by decide
  have hdescent : baseEnd_2690795 < baseStart_2690795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690798 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2690798 : Nat := 118140960795 + 2690798 * 2 ^ 59
def prefixEnd_2690798 : Nat := 4983230072969 + 3 ^ 40 * 2690798 * 2
def baseEnd_2690798 : Nat := 1381672718156868474150251

theorem tailTrace_2690798 : CollatzResearch.WordTrace tailWord_2690798 prefixEnd_2690798 1381672718156868474150251 := by
  unfold tailWord_2690798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12267683213213234069591131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65427643803803915037819365 12267683213213234069591131)
  ·
    refine ⟨18401524819819851104386697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12267683213213234069591131 18401524819819851104386697)
    ·
      refine ⟨13801143614864888328290023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18401524819819851104386697 13801143614864888328290023)
      ·
        refine ⟨20701715422297332492435035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13801143614864888328290023 20701715422297332492435035)
        ·
          refine ⟨31052573133445998738652553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20701715422297332492435035 31052573133445998738652553)
          ·
            refine ⟨23289429850084499053989415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31052573133445998738652553 23289429850084499053989415)
            ·
              refine ⟨34934144775126748580984123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23289429850084499053989415 34934144775126748580984123)
              ·
                refine ⟨52401217162690122871476185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34934144775126748580984123 52401217162690122871476185)
                ·
                  refine ⟨39300912872017592153607139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52401217162690122871476185 39300912872017592153607139)
                  ·
                    refine ⟨58951369308026388230410709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39300912872017592153607139 58951369308026388230410709)
                    ·
                      refine ⟨1381672718156868474150251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58951369308026388230410709 1381672718156868474150251)
                      ·
                        rfl

theorem cell23_2690798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2690798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690798 prefixEnd_2690798 := by exact prefixLift 2690798
  have htrace : WordTrace (prefixWord ++ tailWord_2690798) baseStart_2690798 baseEnd_2690798 := by
    simpa [prefixWord, tailWord_2690798, baseEnd_2690798] using wordTrace_append hprefix tailTrace_2690798
  have hstable : (prefixWord ++ tailWord_2690798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690798).length < 2 ^ (prefixWord ++ tailWord_2690798).sum := by decide
  have hdescent : baseEnd_2690798 < baseStart_2690798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690802 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_2690802 : Nat := 118140960795 + 2690802 * 2 ^ 59
def prefixEnd_2690802 : Nat := 4983230072969 + 3 ^ 40 * 2690802 * 2
def baseEnd_2690802 : Nat := 1381674772079486458500233

theorem tailTrace_2690802 : CollatzResearch.WordTrace tailWord_2690802 prefixEnd_2690802 1381674772079486458500233 := by
  unfold tailWord_2690802
  simp only [CollatzResearch.WordTrace]
  refine ⟨24535402899422845309968665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65427741065127587493249773 24535402899422845309968665)
  ·
    refine ⟨18401552174567133982476499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24535402899422845309968665 18401552174567133982476499)
    ·
      refine ⟨27602328261850700973714749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401552174567133982476499 27602328261850700973714749)
      ·
        refine ⟨10350873098194012865143031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27602328261850700973714749 10350873098194012865143031)
        ·
          refine ⟨15526309647291019297714547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350873098194012865143031 15526309647291019297714547)
          ·
            refine ⟨23289464470936528946571821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15526309647291019297714547 23289464470936528946571821)
            ·
              refine ⟨8733549176601198354964433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23289464470936528946571821 8733549176601198354964433)
              ·
                refine ⟨6550161882450898766223325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8733549176601198354964433 6550161882450898766223325)
                ·
                  refine ⟨2456310705919087037333747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550161882450898766223325 2456310705919087037333747)
                  ·
                    refine ⟨3684466058878630556000621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456310705919087037333747 3684466058878630556000621)
                    ·
                      refine ⟨1381674772079486458500233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684466058878630556000621 1381674772079486458500233)
                      ·
                        rfl

theorem cell23_2690802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_2690802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690802 prefixEnd_2690802 := by exact prefixLift 2690802
  have htrace : WordTrace (prefixWord ++ tailWord_2690802) baseStart_2690802 baseEnd_2690802 := by
    simpa [prefixWord, tailWord_2690802, baseEnd_2690802] using wordTrace_append hprefix tailTrace_2690802
  have hstable : (prefixWord ++ tailWord_2690802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690802).length < 2 ^ (prefixWord ++ tailWord_2690802).sum := by decide
  have hdescent : baseEnd_2690802 < baseStart_2690802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690835 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 2, 4]
def baseStart_2690835 : Nat := 118140960795 + 2690835 * 2 ^ 59
def prefixEnd_2690835 : Nat := 4983230072969 + 3 ^ 40 * 2690835 * 2
def baseEnd_2690835 : Nat := 460563905647028276462527

theorem tailTrace_2690835 : CollatzResearch.WordTrace tailWord_2690835 prefixEnd_2690835 460563905647028276462527 := by
  unfold tailWord_2690835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98142815206571827875825959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65428543471047885250550639 98142815206571827875825959)
  ·
    refine ⟨147214222809857741813738939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98142815206571827875825959 147214222809857741813738939)
    ·
      refine ⟨220821334214786612720608409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147214222809857741813738939 220821334214786612720608409)
      ·
        refine ⟨165616000661089959540456307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220821334214786612720608409 165616000661089959540456307)
        ·
          refine ⟨248424000991634939310684461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165616000661089959540456307 248424000991634939310684461)
          ·
            refine ⟨93159000371863102241506673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248424000991634939310684461 93159000371863102241506673)
            ·
              refine ⟨69869250278897326681130005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93159000371863102241506673 69869250278897326681130005)
              ·
                refine ⟨3275121106823312188177969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69869250278897326681130005 3275121106823312188177969)
                ·
                  refine ⟨2456340830117484141133477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3275121106823312188177969 2456340830117484141133477)
                  ·
                    refine ⟨460563905647028276462527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456340830117484141133477 460563905647028276462527)
                    ·
                      rfl

theorem cell23_2690835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 4].length) (baseStart_2690835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690835 prefixEnd_2690835 := by exact prefixLift 2690835
  have htrace : WordTrace (prefixWord ++ tailWord_2690835) baseStart_2690835 baseEnd_2690835 := by
    simpa [prefixWord, tailWord_2690835, baseEnd_2690835] using wordTrace_append hprefix tailTrace_2690835
  have hstable : (prefixWord ++ tailWord_2690835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690835).length < 2 ^ (prefixWord ++ tailWord_2690835).sum := by decide
  have hdescent : baseEnd_2690835 < baseStart_2690835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690848 : List Nat := [2, 1, 1, 5, 1, 1, 2, 10]
def baseStart_2690848 : Nat := 118140960795 + 2690848 * 2 ^ 59
def prefixEnd_2690848 : Nat := 4983230072969 + 3 ^ 40 * 2690848 * 2
def baseEnd_2690848 : Nat := 51174014525540491797223

theorem tailTrace_2690848 : CollatzResearch.WordTrace tailWord_2690848 prefixEnd_2690848 51174014525540491797223 := by
  unfold tailWord_2690848
  simp only [CollatzResearch.WordTrace]
  refine ⟨49071644677762365548024599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65428859570349820730699465 49071644677762365548024599)
  ·
    refine ⟨73607467016643548322036899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49071644677762365548024599 73607467016643548322036899)
    ·
      refine ⟨110411200524965322483055349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73607467016643548322036899 110411200524965322483055349)
      ·
        refine ⟨10351050049215498982786439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110411200524965322483055349 10351050049215498982786439)
        ·
          refine ⟨15526575073823248474179659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10351050049215498982786439 15526575073823248474179659)
          ·
            refine ⟨23289862610734872711269489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15526575073823248474179659 23289862610734872711269489)
            ·
              refine ⟨17467396958051154533452117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23289862610734872711269489 17467396958051154533452117)
              ·
                refine ⟨51174014525540491797223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17467396958051154533452117 51174014525540491797223)
                ·
                  rfl

theorem cell23_2690848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_2690848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690848 prefixEnd_2690848 := by exact prefixLift 2690848
  have htrace : WordTrace (prefixWord ++ tailWord_2690848) baseStart_2690848 baseEnd_2690848 := by
    simpa [prefixWord, tailWord_2690848, baseEnd_2690848] using wordTrace_append hprefix tailTrace_2690848
  have hstable : (prefixWord ++ tailWord_2690848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690848).length < 2 ^ (prefixWord ++ tailWord_2690848).sum := by decide
  have hdescent : baseEnd_2690848 < baseStart_2690848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690852 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2690852 : Nat := 118140960795 + 2690852 * 2 ^ 59
def prefixEnd_2690852 : Nat := 4983230072969 + 3 ^ 40 * 2690852 * 2
def baseEnd_2690852 : Nat := 460566815370737087625001

theorem tailTrace_2690852 : CollatzResearch.WordTrace tailWord_2690852 prefixEnd_2690852 460566815370737087625001 := by
  unfold tailWord_2690852
  simp only [CollatzResearch.WordTrace]
  refine ⟨49071717623755119889597405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65428956831673493186129873 49071717623755119889597405)
  ·
    refine ⟨18401894108908169958599027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49071717623755119889597405 18401894108908169958599027)
    ·
      refine ⟨27602841163362254937898541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18401894108908169958599027 27602841163362254937898541)
      ·
        refine ⟨10351065436260845601711953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27602841163362254937898541 10351065436260845601711953)
        ·
          refine ⟨7763299077195634201283965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10351065436260845601711953 7763299077195634201283965)
          ·
            refine ⟨2911237153948362825481487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7763299077195634201283965 2911237153948362825481487)
            ·
              refine ⟨4366855730922544238222231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911237153948362825481487 4366855730922544238222231)
              ·
                refine ⟨6550283596383816357333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366855730922544238222231 6550283596383816357333347)
                ·
                  refine ⟨9825425394575724536000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6550283596383816357333347 9825425394575724536000021)
                  ·
                    refine ⟨460566815370737087625001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9825425394575724536000021 460566815370737087625001)
                    ·
                      rfl

theorem cell23_2690852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2690852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690852 prefixEnd_2690852 := by exact prefixLift 2690852
  have htrace : WordTrace (prefixWord ++ tailWord_2690852) baseStart_2690852 baseEnd_2690852 := by
    simpa [prefixWord, tailWord_2690852, baseEnd_2690852] using wordTrace_append hprefix tailTrace_2690852
  have hstable : (prefixWord ++ tailWord_2690852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690852).length < 2 ^ (prefixWord ++ tailWord_2690852).sum := by decide
  have hdescent : baseEnd_2690852 < baseStart_2690852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690865 : List Nat := [1, 2, 2, 3, 2, 2, 4, 7]
def baseStart_2690865 : Nat := 118140960795 + 2690865 * 2 ^ 59
def prefixEnd_2690865 : Nat := 4983230072969 + 3 ^ 40 * 2690865 * 2
def baseEnd_2690865 : Nat := 51174337828174804148609

theorem tailTrace_2690865 : CollatzResearch.WordTrace tailWord_2690865 prefixEnd_2690865 51174337828174804148609 := by
  unfold tailWord_2690865
  simp only [CollatzResearch.WordTrace]
  refine ⟨98143909396463142999418049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65429272930975428666278699 98143909396463142999418049)
  ·
    refine ⟨73607932047347357249563537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98143909396463142999418049 73607932047347357249563537)
    ·
      refine ⟨55205949035510517937172653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73607932047347357249563537 55205949035510517937172653)
      ·
        refine ⟨20702230888316444226439745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55205949035510517937172653 20702230888316444226439745)
        ·
          refine ⟨15526673166237333169829809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20702230888316444226439745 15526673166237333169829809)
          ·
            refine ⟨11645004874677999877372357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15526673166237333169829809 11645004874677999877372357)
            ·
              refine ⟨2183438414002124977007317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11645004874677999877372357 2183438414002124977007317)
              ·
                refine ⟨51174337828174804148609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2183438414002124977007317 51174337828174804148609)
                ·
                  rfl

theorem cell23_2690865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 7].length) (baseStart_2690865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690865 prefixEnd_2690865 := by exact prefixLift 2690865
  have htrace : WordTrace (prefixWord ++ tailWord_2690865) baseStart_2690865 baseEnd_2690865 := by
    simpa [prefixWord, tailWord_2690865, baseEnd_2690865] using wordTrace_append hprefix tailTrace_2690865
  have hstable : (prefixWord ++ tailWord_2690865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690865).length < 2 ^ (prefixWord ++ tailWord_2690865).sum := by decide
  have hdescent : baseEnd_2690865 < baseStart_2690865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690876 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_2690876 : Nat := 118140960795 + 2690876 * 2 ^ 59
def prefixEnd_2690876 : Nat := 4983230072969 + 3 ^ 40 * 2690876 * 2
def baseEnd_2690876 : Nat := 1381712769647919168974893

theorem tailTrace_2690876 : CollatzResearch.WordTrace tailWord_2690876 prefixEnd_2690876 1381712769647919168974893 := by
  unfold tailWord_2690876
  simp only [CollatzResearch.WordTrace]
  refine ⟨49072155299711645939034241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65429540399615527918712321 49072155299711645939034241)
  ·
    refine ⟨36804116474783734454275681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49072155299711645939034241 36804116474783734454275681)
    ·
      refine ⟨27603087356087800840706761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36804116474783734454275681 27603087356087800840706761)
      ·
        refine ⟨20702315517065850630530071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27603087356087800840706761 20702315517065850630530071)
        ·
          refine ⟨31053473275598775945795107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20702315517065850630530071 31053473275598775945795107)
          ·
            refine ⟨46580209913398163918692661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31053473275598775945795107 46580209913398163918692661)
            ·
              refine ⟨4366894679381077867377437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46580209913398163918692661 4366894679381077867377437)
              ·
                refine ⟨1637585504767904200266539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4366894679381077867377437 1637585504767904200266539)
                ·
                  refine ⟨2456378257151856300399809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637585504767904200266539 2456378257151856300399809)
                  ·
                    refine ⟨1842283692863892225299857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456378257151856300399809 1842283692863892225299857)
                    ·
                      refine ⟨1381712769647919168974893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842283692863892225299857 1381712769647919168974893)
                      ·
                        rfl

theorem cell23_2690876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_2690876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690876 prefixEnd_2690876 := by exact prefixLift 2690876
  have htrace : WordTrace (prefixWord ++ tailWord_2690876) baseStart_2690876 baseEnd_2690876 := by
    simpa [prefixWord, tailWord_2690876, baseEnd_2690876] using wordTrace_append hprefix tailTrace_2690876
  have hstable : (prefixWord ++ tailWord_2690876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690876).length < 2 ^ (prefixWord ++ tailWord_2690876).sum := by decide
  have hdescent : baseEnd_2690876 < baseStart_2690876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690893 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2690893 : Nat := 118140960795 + 2690893 * 2 ^ 59
def prefixEnd_2690893 : Nat := 4983230072969 + 3 ^ 40 * 2690893 * 2
def baseEnd_2690893 : Nat := 1381721498819045602462315

theorem tailTrace_2690893 : CollatzResearch.WordTrace tailWord_2690893 prefixEnd_2690893 1381721498819045602462315 := by
  unfold tailWord_2690893
  simp only [CollatzResearch.WordTrace]
  refine ⟨98144930640361703781437333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65429953760241135854291555 98144930640361703781437333)
  ·
    refine ⟨4600543623766954864754875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98144930640361703781437333 4600543623766954864754875)
    ·
      refine ⟨6900815435650432297132313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600543623766954864754875 6900815435650432297132313)
      ·
        refine ⟨5175611576737824222849235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6900815435650432297132313 5175611576737824222849235)
        ·
          refine ⟨7763417365106736334273853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175611576737824222849235 7763417365106736334273853)
          ·
            refine ⟨2911281511915026125352695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7763417365106736334273853 2911281511915026125352695)
            ·
              refine ⟨4366922267872539188029043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911281511915026125352695 4366922267872539188029043)
              ·
                refine ⟨6550383401808808782043565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4366922267872539188029043 6550383401808808782043565)
                ·
                  refine ⟨2456393775678303293266337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550383401808808782043565 2456393775678303293266337)
                  ·
                    refine ⟨1842295331758727469949753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456393775678303293266337 1842295331758727469949753)
                    ·
                      refine ⟨1381721498819045602462315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842295331758727469949753 1381721498819045602462315)
                      ·
                        rfl

theorem cell23_2690893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2690893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690893 prefixEnd_2690893 := by exact prefixLift 2690893
  have htrace : WordTrace (prefixWord ++ tailWord_2690893) baseStart_2690893 baseEnd_2690893 := by
    simpa [prefixWord, tailWord_2690893, baseEnd_2690893] using wordTrace_append hprefix tailTrace_2690893
  have hstable : (prefixWord ++ tailWord_2690893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690893).length < 2 ^ (prefixWord ++ tailWord_2690893).sum := by decide
  have hdescent : baseEnd_2690893 < baseStart_2690893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690962 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2690962 : Nat := 118140960795 + 2690962 * 2 ^ 59
def prefixEnd_2690962 : Nat := 4983230072969 + 3 ^ 40 * 2690962 * 2
def baseEnd_2690962 : Nat := 1381756928984205832499497

theorem tailTrace_2690962 : CollatzResearch.WordTrace tailWord_2690962 prefixEnd_2690962 1381756928984205832499497 := by
  unfold tailWord_2690962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24536861819277932141424785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65431631518074485710466093 24536861819277932141424785)
  ·
    refine ⟨18402646364458449106068589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24536861819277932141424785 18402646364458449106068589)
    ·
      refine ⟨6900992386671918414775721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18402646364458449106068589 6900992386671918414775721)
      ·
        refine ⟨5175744290003938811081791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6900992386671918414775721 5175744290003938811081791)
        ·
          refine ⟨7763616435005908216622687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175744290003938811081791 7763616435005908216622687)
          ·
            refine ⟨11645424652508862324934031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7763616435005908216622687 11645424652508862324934031)
            ·
              refine ⟨17468136978763293487401047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11645424652508862324934031 17468136978763293487401047)
              ·
                refine ⟨26202205468144940231101571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17468136978763293487401047 26202205468144940231101571)
                ·
                  refine ⟨39303308202217410346652357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26202205468144940231101571 39303308202217410346652357)
                  ·
                    refine ⟨7369370287915764439997317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39303308202217410346652357 7369370287915764439997317)
                    ·
                      refine ⟨1381756928984205832499497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7369370287915764439997317 1381756928984205832499497)
                      ·
                        rfl

theorem cell23_2690962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2690962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690962 prefixEnd_2690962 := by exact prefixLift 2690962
  have htrace : WordTrace (prefixWord ++ tailWord_2690962) baseStart_2690962 baseEnd_2690962 := by
    simpa [prefixWord, tailWord_2690962, baseEnd_2690962] using wordTrace_append hprefix tailTrace_2690962
  have hstable : (prefixWord ++ tailWord_2690962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690962).length < 2 ^ (prefixWord ++ tailWord_2690962).sum := by decide
  have hdescent : baseEnd_2690962 < baseStart_2690962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690972 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 7]
def baseStart_2690972 : Nat := 118140960795 + 2690972 * 2 ^ 59
def prefixEnd_2690972 : Nat := 4983230072969 + 3 ^ 40 * 2690972 * 2
def baseEnd_2690972 : Nat := 153529118198972310374939

theorem tailTrace_2690972 : CollatzResearch.WordTrace tailWord_2690972 prefixEnd_2690972 153529118198972310374939 := by
  unfold tailWord_2690972
  simp only [CollatzResearch.WordTrace]
  refine ⟨49073906003537750136781585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65431874671383666849042113 49073906003537750136781585)
  ·
    refine ⟨36805429502653312602586189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49073906003537750136781585 36805429502653312602586189)
    ·
      refine ⟨13802036063494992225969821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36805429502653312602586189 13802036063494992225969821)
      ·
        refine ⟨5175763523810622084738683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13802036063494992225969821 5175763523810622084738683)
        ·
          refine ⟨7763645285715933127108025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175763523810622084738683 7763645285715933127108025)
          ·
            refine ⟨5822733964286949845331019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763645285715933127108025 5822733964286949845331019)
            ·
              refine ⟨8734100946430424767996529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822733964286949845331019 8734100946430424767996529)
              ·
                refine ⟨6550575709822818575997397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734100946430424767996529 6550575709822818575997397)
                ·
                  refine ⟨153529118198972310374939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6550575709822818575997397 153529118198972310374939)
                  ·
                    rfl

theorem cell23_2690972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_2690972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690972 prefixEnd_2690972 := by exact prefixLift 2690972
  have htrace : WordTrace (prefixWord ++ tailWord_2690972) baseStart_2690972 baseEnd_2690972 := by
    simpa [prefixWord, tailWord_2690972, baseEnd_2690972] using wordTrace_append hprefix tailTrace_2690972
  have hstable : (prefixWord ++ tailWord_2690972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690972).length < 2 ^ (prefixWord ++ tailWord_2690972).sum := by decide
  have hdescent : baseEnd_2690972 < baseStart_2690972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690985 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_2690985 : Nat := 118140960795 + 2690985 * 2 ^ 59
def prefixEnd_2690985 : Nat := 4983230072969 + 3 ^ 40 * 2690985 * 2
def baseEnd_2690985 : Nat := 460589579679753080837297

theorem tailTrace_2690985 : CollatzResearch.WordTrace tailWord_2690985 prefixEnd_2690985 460589579679753080837297 := by
  unfold tailWord_2690985
  simp only [CollatzResearch.WordTrace]
  refine ⟨98148286156028403493786409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65432190770685602329190939 98148286156028403493786409)
  ·
    refine ⟨73611214617021302620339807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98148286156028403493786409 73611214617021302620339807)
    ·
      refine ⟨110416821925531953930509711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73611214617021302620339807 110416821925531953930509711)
      ·
        refine ⟨165625232888297930895764567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110416821925531953930509711 165625232888297930895764567)
        ·
          refine ⟨248437849332446896343646851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165625232888297930895764567 248437849332446896343646851)
          ·
            refine ⟨372656773998670344515470277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248437849332446896343646851 372656773998670344515470277)
            ·
              refine ⟨69873145124750689596650677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 372656773998670344515470277 69873145124750689596650677)
              ·
                refine ⟨6550607355445377149686001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69873145124750689596650677 6550607355445377149686001)
                ·
                  refine ⟨4912955516584032862264501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550607355445377149686001 4912955516584032862264501)
                  ·
                    refine ⟨460589579679753080837297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4912955516584032862264501 460589579679753080837297)
                    ·
                      rfl

theorem cell23_2690985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_2690985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2690985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2690985 prefixEnd_2690985 := by exact prefixLift 2690985
  have htrace : WordTrace (prefixWord ++ tailWord_2690985) baseStart_2690985 baseEnd_2690985 := by
    simpa [prefixWord, tailWord_2690985, baseEnd_2690985] using wordTrace_append hprefix tailTrace_2690985
  have hstable : (prefixWord ++ tailWord_2690985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690985).length < 2 ^ (prefixWord ++ tailWord_2690985).sum := by decide
  have hdescent : baseEnd_2690985 < baseStart_2690985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691032 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_2691032 : Nat := 118140960795 + 2691032 * 2 ^ 59
def prefixEnd_2691032 : Nat := 4983230072969 + 3 ^ 40 * 2691032 * 2
def baseEnd_2691032 : Nat := 460597624210006852874725

theorem tailTrace_2691032 : CollatzResearch.WordTrace tailWord_2691032 prefixEnd_2691032 460597624210006852874725 := by
  unfold tailWord_2691032
  simp only [CollatzResearch.WordTrace]
  refine ⟨49075000193429065260373675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65433333591238753680498233 49075000193429065260373675)
  ·
    refine ⟨73612500290143597890560513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49075000193429065260373675 73612500290143597890560513)
    ·
      refine ⟨55209375217607698417920385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73612500290143597890560513 55209375217607698417920385)
      ·
        refine ⟨41407031413205773813440289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55209375217607698417920385 41407031413205773813440289)
        ·
          refine ⟨31055273559904330360080217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41407031413205773813440289 31055273559904330360080217)
          ·
            refine ⟨23291455169928247770060163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31055273559904330360080217 23291455169928247770060163)
            ·
              refine ⟨34937182754892371655090245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23291455169928247770060163 34937182754892371655090245)
              ·
                refine ⟨6550721766542319685329421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34937182754892371655090245 6550721766542319685329421)
                ·
                  refine ⟨2456520662453369881998533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550721766542319685329421 2456520662453369881998533)
                  ·
                    refine ⟨460597624210006852874725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2456520662453369881998533 460597624210006852874725)
                    ·
                      rfl

theorem cell23_2691032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_2691032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691032 prefixEnd_2691032 := by exact prefixLift 2691032
  have htrace : WordTrace (prefixWord ++ tailWord_2691032) baseStart_2691032 baseEnd_2691032 := by
    simpa [prefixWord, tailWord_2691032, baseEnd_2691032] using wordTrace_append hprefix tailTrace_2691032
  have hstable : (prefixWord ++ tailWord_2691032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691032).length < 2 ^ (prefixWord ++ tailWord_2691032).sum := by decide
  have hdescent : baseEnd_2691032 < baseStart_2691032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691079 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 6]
def baseStart_2691079 : Nat := 118140960795 + 2691079 * 2 ^ 59
def prefixEnd_2691079 : Nat := 4983230072969 + 3 ^ 40 * 2691079 * 2
def baseEnd_2691079 : Nat := 153535222913420208304051

theorem tailTrace_2691079 : CollatzResearch.WordTrace tailWord_2691079 prefixEnd_2691079 153535222913420208304051 := by
  unfold tailWord_2691079
  simp only [CollatzResearch.WordTrace]
  refine ⟨98151714617687857547708291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65434476411791905031805527 98151714617687857547708291)
  ·
    refine ⟨147227571926531786321562437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98151714617687857547708291 147227571926531786321562437)
    ·
      refine ⟨27605169736224709935292957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147227571926531786321562437 27605169736224709935292957)
      ·
        refine ⟨10351938651084266225734859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27605169736224709935292957 10351938651084266225734859)
        ·
          refine ⟨15527907976626399338602289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10351938651084266225734859 15527907976626399338602289)
          ·
            refine ⟨11645930982469799503951717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15527907976626399338602289 11645930982469799503951717)
            ·
              refine ⟨2183612059213087406990947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11645930982469799503951717 2183612059213087406990947)
              ·
                refine ⟨3275418088819631110486421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183612059213087406990947 3275418088819631110486421)
                ·
                  refine ⟨153535222913420208304051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3275418088819631110486421 153535222913420208304051)
                  ·
                    rfl

theorem cell23_2691079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 6].length) (baseStart_2691079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691079 prefixEnd_2691079 := by exact prefixLift 2691079
  have htrace : WordTrace (prefixWord ++ tailWord_2691079) baseStart_2691079 baseEnd_2691079 := by
    simpa [prefixWord, tailWord_2691079, baseEnd_2691079] using wordTrace_append hprefix tailTrace_2691079
  have hstable : (prefixWord ++ tailWord_2691079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691079).length < 2 ^ (prefixWord ++ tailWord_2691079).sum := by decide
  have hdescent : baseEnd_2691079 < baseStart_2691079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691123 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 1, 1, 3]
def baseStart_2691123 : Nat := 118140960795 + 2691123 * 2 ^ 59
def prefixEnd_2691123 : Nat := 4983230072969 + 3 ^ 40 * 2691123 * 2
def baseEnd_2691123 : Nat := 1381839599369579702586257

theorem tailTrace_2691123 : CollatzResearch.WordTrace tailWord_2691123 prefixEnd_2691123 1381839599369579702586257 := by
  unfold tailWord_2691123
  simp only [CollatzResearch.WordTrace]
  refine ⟨98153319429528453062310023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65435546286352302041540015 98153319429528453062310023)
  ·
    refine ⟨147229979144292679593465035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98153319429528453062310023 147229979144292679593465035)
    ·
      refine ⟨220844968716439019390197553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147229979144292679593465035 220844968716439019390197553)
      ·
        refine ⟨165633726537329264542648165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220844968716439019390197553 165633726537329264542648165)
        ·
          refine ⟨31056323725749237101746531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165633726537329264542648165 31056323725749237101746531)
          ·
            refine ⟨46584485588623855652619797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31056323725749237101746531 46584485588623855652619797)
            ·
              refine ⟨2183647761966743233716553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46584485588623855652619797 2183647761966743233716553)
              ·
                refine ⟨1637735821475057425287415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183647761966743233716553 1637735821475057425287415)
                ·
                  refine ⟨2456603732212586137931123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637735821475057425287415 2456603732212586137931123)
                  ·
                    refine ⟨3684905598318879206896685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456603732212586137931123 3684905598318879206896685)
                    ·
                      refine ⟨1381839599369579702586257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3684905598318879206896685 1381839599369579702586257)
                      ·
                        rfl

theorem cell23_2691123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 1, 1, 3].length) (baseStart_2691123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691123 prefixEnd_2691123 := by exact prefixLift 2691123
  have htrace : WordTrace (prefixWord ++ tailWord_2691123) baseStart_2691123 baseEnd_2691123 := by
    simpa [prefixWord, tailWord_2691123, baseEnd_2691123] using wordTrace_append hprefix tailTrace_2691123
  have hstable : (prefixWord ++ tailWord_2691123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691123).length < 2 ^ (prefixWord ++ tailWord_2691123).sum := by decide
  have hdescent : baseEnd_2691123 < baseStart_2691123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691132 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2691132 : Nat := 118140960795 + 2691132 * 2 ^ 59
def prefixEnd_2691132 : Nat := 4983230072969 + 3 ^ 40 * 2691132 * 2
def baseEnd_2691132 : Nat := 1381844220695470167373715

theorem tailTrace_2691132 : CollatzResearch.WordTrace tailWord_2691132 prefixEnd_2691132 1381844220695470167373715 := by
  unfold tailWord_2691132
  simp only [CollatzResearch.WordTrace]
  refine ⟨49076823843247923799693825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65435765124330565066258433 49076823843247923799693825)
  ·
    refine ⟨36807617882435942849770369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49076823843247923799693825 36807617882435942849770369)
    ·
      refine ⟨27605713411826957137327777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36807617882435942849770369 27605713411826957137327777)
      ·
        refine ⟨20704285058870217852995833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27605713411826957137327777 20704285058870217852995833)
        ·
          refine ⟨15528213794152663389746875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20704285058870217852995833 15528213794152663389746875)
          ·
            refine ⟨23292320691228995084620313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15528213794152663389746875 23292320691228995084620313)
            ·
              refine ⟨17469240518421746313465235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23292320691228995084620313 17469240518421746313465235)
              ·
                refine ⟨26203860777632619470197853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17469240518421746313465235 26203860777632619470197853)
                ·
                  refine ⟨9826447791612232301324195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26203860777632619470197853 9826447791612232301324195)
                  ·
                    refine ⟨14739671687418348451986293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9826447791612232301324195 14739671687418348451986293)
                    ·
                      refine ⟨1381844220695470167373715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14739671687418348451986293 1381844220695470167373715)
                      ·
                        rfl

theorem cell23_2691132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2691132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691132 prefixEnd_2691132 := by exact prefixLift 2691132
  have htrace : WordTrace (prefixWord ++ tailWord_2691132) baseStart_2691132 baseEnd_2691132 := by
    simpa [prefixWord, tailWord_2691132, baseEnd_2691132] using wordTrace_append hprefix tailTrace_2691132
  have hstable : (prefixWord ++ tailWord_2691132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691132).length < 2 ^ (prefixWord ++ tailWord_2691132).sum := by decide
  have hdescent : baseEnd_2691132 < baseStart_2691132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691196 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2691196 : Nat := 118140960795 + 2691196 * 2 ^ 59
def prefixEnd_2691196 : Nat := 4983230072969 + 3 ^ 40 * 2691196 * 2
def baseEnd_2691196 : Nat := 1381877083457357916973421

theorem tailTrace_2691196 : CollatzResearch.WordTrace tailWord_2691196 prefixEnd_2691196 1381877083457357916973421 := by
  unfold tailWord_2691196
  simp only [CollatzResearch.WordTrace]
  refine ⟨49077990979131993264858721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65437321305509324353144961 49077990979131993264858721)
  ·
    refine ⟨36808493234348994948644041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49077990979131993264858721 36808493234348994948644041)
    ·
      refine ⟨27606369925761746211483031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36808493234348994948644041 27606369925761746211483031)
      ·
        refine ⟨41409554888642619317224547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27606369925761746211483031 41409554888642619317224547)
        ·
          refine ⟨62114332332963928975836821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41409554888642619317224547 62114332332963928975836821)
          ·
            refine ⟨2911609328107684170742351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62114332332963928975836821 2911609328107684170742351)
            ·
              refine ⟨4367413992161526256113527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911609328107684170742351 4367413992161526256113527)
              ·
                refine ⟨6551120988242289384170291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367413992161526256113527 6551120988242289384170291)
                ·
                  refine ⟨9826681482363434076255437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551120988242289384170291 9826681482363434076255437)
                  ·
                    refine ⟨3685005555886287778595789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9826681482363434076255437 3685005555886287778595789)
                    ·
                      refine ⟨1381877083457357916973421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3685005555886287778595789 1381877083457357916973421)
                      ·
                        rfl

theorem cell23_2691196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2691196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691196 prefixEnd_2691196 := by exact prefixLift 2691196
  have htrace : WordTrace (prefixWord ++ tailWord_2691196) baseStart_2691196 baseEnd_2691196 := by
    simpa [prefixWord, tailWord_2691196, baseEnd_2691196] using wordTrace_append hprefix tailTrace_2691196
  have hstable : (prefixWord ++ tailWord_2691196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691196).length < 2 ^ (prefixWord ++ tailWord_2691196).sum := by decide
  have hdescent : baseEnd_2691196 < baseStart_2691196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691214 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2691214 : Nat := 118140960795 + 2691214 * 2 ^ 59
def prefixEnd_2691214 : Nat := 4983230072969 + 3 ^ 40 * 2691214 * 2
def baseEnd_2691214 : Nat := 1381886326109138846548339

theorem tailTrace_2691214 : CollatzResearch.WordTrace tailWord_2691214 prefixEnd_2691214 1381886326109138846548339 := by
  unfold tailWord_2691214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269579809024846950484087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65437758981465850402581797 12269579809024846950484087)
  ·
    refine ⟨18404369713537270425726131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12269579809024846950484087 18404369713537270425726131)
    ·
      refine ⟨27606554570305905638589197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18404369713537270425726131 27606554570305905638589197)
      ·
        refine ⟨10352457963864714614470949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27606554570305905638589197 10352457963864714614470949)
        ·
          refine ⟨1941085868224633990213303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10352457963864714614470949 1941085868224633990213303)
          ·
            refine ⟨2911628802336950985319955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941085868224633990213303 2911628802336950985319955)
            ·
              refine ⟨4367443203505426477979933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911628802336950985319955 4367443203505426477979933)
              ·
                refine ⟨1637791201314534929242475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4367443203505426477979933 1637791201314534929242475)
                ·
                  refine ⟨2456686801971802393863713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637791201314534929242475 2456686801971802393863713)
                  ·
                    refine ⟨1842515101478851795397785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456686801971802393863713 1842515101478851795397785)
                    ·
                      refine ⟨1381886326109138846548339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842515101478851795397785 1381886326109138846548339)
                      ·
                        rfl

theorem cell23_2691214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2691214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691214 prefixEnd_2691214 := by exact prefixLift 2691214
  have htrace : WordTrace (prefixWord ++ tailWord_2691214) baseStart_2691214 baseEnd_2691214 := by
    simpa [prefixWord, tailWord_2691214, baseEnd_2691214] using wordTrace_append hprefix tailTrace_2691214
  have hstable : (prefixWord ++ tailWord_2691214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691214).length < 2 ^ (prefixWord ++ tailWord_2691214).sum := by decide
  have hdescent : baseEnd_2691214 < baseStart_2691214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 4, 2]
def baseStart_2691219 : Nat := 118140960795 + 2691219 * 2 ^ 59
def prefixEnd_2691219 : Nat := 4983230072969 + 3 ^ 40 * 2691219 * 2
def baseEnd_2691219 : Nat := 1381888893512411326985815

theorem tailTrace_2691219 : CollatzResearch.WordTrace tailWord_2691219 prefixEnd_2691219 1381888893512411326985815 := by
  unfold tailWord_2691219
  simp only [CollatzResearch.WordTrace]
  refine ⟨98156820837180661457804711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65437880558120440971869807 98156820837180661457804711)
  ·
    refine ⟨147235231255770992186707067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98156820837180661457804711 147235231255770992186707067)
    ·
      refine ⟨220852846883656488280060601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147235231255770992186707067 220852846883656488280060601)
      ·
        refine ⟨165639635162742366210045451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220852846883656488280060601 165639635162742366210045451)
        ·
          refine ⟨248459452744113549315068177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165639635162742366210045451 248459452744113549315068177)
          ·
            refine ⟨186344589558085161986301133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248459452744113549315068177 186344589558085161986301133)
            ·
              refine ⟨69879221084281935744862925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186344589558085161986301133 69879221084281935744862925)
              ·
                refine ⟨26204707906605725904323597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69879221084281935744862925 26204707906605725904323597)
                ·
                  refine ⟨9826765464977147214121349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26204707906605725904323597 9826765464977147214121349)
                  ·
                    refine ⟨1842518524683215102647753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9826765464977147214121349 1842518524683215102647753)
                    ·
                      refine ⟨1381888893512411326985815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842518524683215102647753 1381888893512411326985815)
                      ·
                        rfl

theorem cell23_2691219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4, 2].length) (baseStart_2691219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691219 prefixEnd_2691219 := by exact prefixLift 2691219
  have htrace : WordTrace (prefixWord ++ tailWord_2691219) baseStart_2691219 baseEnd_2691219 := by
    simpa [prefixWord, tailWord_2691219, baseEnd_2691219] using wordTrace_append hprefix tailTrace_2691219
  have hstable : (prefixWord ++ tailWord_2691219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691219).length < 2 ^ (prefixWord ++ tailWord_2691219).sum := by decide
  have hdescent : baseEnd_2691219 < baseStart_2691219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691289 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_2691289 : Nat := 118140960795 + 2691289 * 2 ^ 59
def prefixEnd_2691289 : Nat := 4983230072969 + 3 ^ 40 * 2691289 * 2
def baseEnd_2691289 : Nat := 460641612386075351036831

theorem tailTrace_2691289 : CollatzResearch.WordTrace tailWord_2691289 prefixEnd_2691289 460641612386075351036831 := by
  unfold tailWord_2691289
  simp only [CollatzResearch.WordTrace]
  refine ⟨98159373946927063412852921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65439582631284708941901947 98159373946927063412852921)
  ·
    refine ⟨73619530460195297559639691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98159373946927063412852921 73619530460195297559639691)
    ·
      refine ⟨110429295690292946339459537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73619530460195297559639691 110429295690292946339459537)
      ·
        refine ⟨82821971767719709754594653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110429295690292946339459537 82821971767719709754594653)
        ·
          refine ⟨31058239412894891157972995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82821971767719709754594653 31058239412894891157972995)
          ·
            refine ⟨46587359119342336736959493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31058239412894891157972995 46587359119342336736959493)
            ·
              refine ⟨8735129834876688138179905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46587359119342336736959493 8735129834876688138179905)
              ·
                refine ⟨6551347376157516103634929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8735129834876688138179905 6551347376157516103634929)
                ·
                  refine ⟨4913510532118137077726197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6551347376157516103634929 4913510532118137077726197)
                  ·
                    refine ⟨460641612386075351036831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4913510532118137077726197 460641612386075351036831)
                    ·
                      rfl

theorem cell23_2691289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_2691289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691289 prefixEnd_2691289 := by exact prefixLift 2691289
  have htrace : WordTrace (prefixWord ++ tailWord_2691289) baseStart_2691289 baseEnd_2691289 := by
    simpa [prefixWord, tailWord_2691289, baseEnd_2691289] using wordTrace_append hprefix tailTrace_2691289
  have hstable : (prefixWord ++ tailWord_2691289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691289).length < 2 ^ (prefixWord ++ tailWord_2691289).sum := by decide
  have hdescent : baseEnd_2691289 < baseStart_2691289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691293 : List Nat := [1, 4, 3, 2, 1, 2, 1, 4, 5]
def baseStart_2691293 : Nat := 118140960795 + 2691293 * 2 ^ 59
def prefixEnd_2691293 : Nat := 4983230072969 + 3 ^ 40 * 2691293 * 2
def baseEnd_2691293 : Nat := 153547432342316004162275

theorem tailTrace_2691293 : CollatzResearch.WordTrace tailWord_2691293 prefixEnd_2691293 153547432342316004162275 := by
  unfold tailWord_2691293
  simp only [CollatzResearch.WordTrace]
  refine ⟨98159519838912572095998533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65439679892608381397332355 98159519838912572095998533)
  ·
    refine ⟨18404909969796107267999725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98159519838912572095998533 18404909969796107267999725)
    ·
      refine ⟨6901841238673540225499897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18404909969796107267999725 6901841238673540225499897)
      ·
        refine ⟨5176380929005155169124923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6901841238673540225499897 5176380929005155169124923)
        ·
          refine ⟨7764571393507732753687385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5176380929005155169124923 7764571393507732753687385)
          ·
            refine ⟨5823428545130799565265539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764571393507732753687385 5823428545130799565265539)
            ·
              refine ⟨8735142817696199347898309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823428545130799565265539 8735142817696199347898309)
              ·
                refine ⟨1637839278318037377730933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8735142817696199347898309 1637839278318037377730933)
                ·
                  refine ⟨153547432342316004162275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1637839278318037377730933 153547432342316004162275)
                  ·
                    rfl

theorem cell23_2691293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_2691293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691293 prefixEnd_2691293 := by exact prefixLift 2691293
  have htrace : WordTrace (prefixWord ++ tailWord_2691293) baseStart_2691293 baseEnd_2691293 := by
    simpa [prefixWord, tailWord_2691293, baseEnd_2691293] using wordTrace_append hprefix tailTrace_2691293
  have hstable : (prefixWord ++ tailWord_2691293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691293).length < 2 ^ (prefixWord ++ tailWord_2691293).sum := by decide
  have hdescent : baseEnd_2691293 < baseStart_2691293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691326 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2691326 : Nat := 118140960795 + 2691326 * 2 ^ 59
def prefixEnd_2691326 : Nat := 4983230072969 + 3 ^ 40 * 2691326 * 2
def baseEnd_2691326 : Nat := 1381943835942442408347823

theorem tailTrace_2691326 : CollatzResearch.WordTrace tailWord_2691326 prefixEnd_2691326 1381943835942442408347823 := by
  unfold tailWord_2691326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270090430974127341493729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65440482298528679154633221 12270090430974127341493729)
  ·
    refine ⟨9202567823230595506120297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12270090430974127341493729 9202567823230595506120297)
    ·
      refine ⟨6901925867422946629590223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9202567823230595506120297 6901925867422946629590223)
      ·
        refine ⟨10352888801134419944385335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901925867422946629590223 10352888801134419944385335)
        ·
          refine ⟨15529333201701629916578003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352888801134419944385335 15529333201701629916578003)
          ·
            refine ⟨23293999802552444874867005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15529333201701629916578003 23293999802552444874867005)
            ·
              refine ⟨8735249925957166828075127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23293999802552444874867005 8735249925957166828075127)
              ·
                refine ⟨13102874888935750242112691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8735249925957166828075127 13102874888935750242112691)
                ·
                  refine ⟨19654312333403625363169037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13102874888935750242112691 19654312333403625363169037)
                  ·
                    refine ⟨7370367125026359511188389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19654312333403625363169037 7370367125026359511188389)
                    ·
                      refine ⟨1381943835942442408347823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7370367125026359511188389 1381943835942442408347823)
                      ·
                        rfl

theorem cell23_2691326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2691326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691326 prefixEnd_2691326 := by exact prefixLift 2691326
  have htrace : WordTrace (prefixWord ++ tailWord_2691326) baseStart_2691326 baseEnd_2691326 := by
    simpa [prefixWord, tailWord_2691326, baseEnd_2691326] using wordTrace_append hprefix tailTrace_2691326
  have hstable : (prefixWord ++ tailWord_2691326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691326).length < 2 ^ (prefixWord ++ tailWord_2691326).sum := by decide
  have hdescent : baseEnd_2691326 < baseStart_2691326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691376 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_2691376 : Nat := 118140960795 + 2691376 * 2 ^ 59
def prefixEnd_2691376 : Nat := 4983230072969 + 3 ^ 40 * 2691376 * 2
def baseEnd_2691376 : Nat := 1381969509975167212722593

theorem tailTrace_2691376 : CollatzResearch.WordTrace tailWord_2691376 prefixEnd_2691376 1381969509975167212722593 := by
  unfold tailWord_2691376
  simp only [CollatzResearch.WordTrace]
  refine ⟨49081273548805938635634991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65441698065074584847513321 49081273548805938635634991)
  ·
    refine ⟨73621910323208907953452487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49081273548805938635634991 73621910323208907953452487)
    ·
      refine ⟨110432865484813361930178731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73621910323208907953452487 110432865484813361930178731)
      ·
        refine ⟨165649298227220042895268097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110432865484813361930178731 165649298227220042895268097)
        ·
          refine ⟨124236973670415032171451073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165649298227220042895268097 124236973670415032171451073)
          ·
            refine ⟨93177730252811274128588305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124236973670415032171451073 93177730252811274128588305)
            ·
              refine ⟨69883297689608455596441229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93177730252811274128588305 69883297689608455596441229)
              ·
                refine ⟨26206236633603170848665461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69883297689608455596441229 26206236633603170848665461)
                ·
                  refine ⟨2456834684400297267062387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26206236633603170848665461 2456834684400297267062387)
                  ·
                    refine ⟨3685252026600445900593581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456834684400297267062387 3685252026600445900593581)
                    ·
                      refine ⟨1381969509975167212722593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3685252026600445900593581 1381969509975167212722593)
                      ·
                        rfl

theorem cell23_2691376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_2691376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691376 prefixEnd_2691376 := by exact prefixLift 2691376
  have htrace : WordTrace (prefixWord ++ tailWord_2691376) baseStart_2691376 baseEnd_2691376 := by
    simpa [prefixWord, tailWord_2691376, baseEnd_2691376] using wordTrace_append hprefix tailTrace_2691376
  have hstable : (prefixWord ++ tailWord_2691376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691376).length < 2 ^ (prefixWord ++ tailWord_2691376).sum := by decide
  have hdescent : baseEnd_2691376 < baseStart_2691376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691410 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_2691410 : Nat := 118140960795 + 2691410 * 2 ^ 59
def prefixEnd_2691410 : Nat := 4983230072969 + 3 ^ 40 * 2691410 * 2
def baseEnd_2691410 : Nat := 1381986968317420079697437

theorem tailTrace_2691410 : CollatzResearch.WordTrace tailWord_2691410 prefixEnd_2691410 1381986968317420079697437 := by
  unfold tailWord_2691410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24540946794872175269501921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65442524786325800718671789 24540946794872175269501921)
  ·
    refine ⟨18405710096154131452126441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24540946794872175269501921 18405710096154131452126441)
    ·
      refine ⟨13804282572115598589094831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18405710096154131452126441 13804282572115598589094831)
      ·
        refine ⟨20706423858173397883642247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13804282572115598589094831 20706423858173397883642247)
        ·
          refine ⟨31059635787260096825463371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20706423858173397883642247 31059635787260096825463371)
          ·
            refine ⟨46589453680890145238195057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31059635787260096825463371 46589453680890145238195057)
            ·
              refine ⟨34942090260667608928646293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46589453680890145238195057 34942090260667608928646293)
              ·
                refine ⟨1637910480968794168530295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34942090260667608928646293 1637910480968794168530295)
                ·
                  refine ⟨2456865721453191252795443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637910480968794168530295 2456865721453191252795443)
                  ·
                    refine ⟨3685298582179786879193165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456865721453191252795443 3685298582179786879193165)
                    ·
                      refine ⟨1381986968317420079697437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3685298582179786879193165 1381986968317420079697437)
                      ·
                        rfl

theorem cell23_2691410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_2691410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691410 prefixEnd_2691410 := by exact prefixLift 2691410
  have htrace : WordTrace (prefixWord ++ tailWord_2691410) baseStart_2691410 baseEnd_2691410 := by
    simpa [prefixWord, tailWord_2691410, baseEnd_2691410] using wordTrace_append hprefix tailTrace_2691410
  have hstable : (prefixWord ++ tailWord_2691410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691410).length < 2 ^ (prefixWord ++ tailWord_2691410).sum := by decide
  have hdescent : baseEnd_2691410 < baseStart_2691410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691416 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_2691416 : Nat := 118140960795 + 2691416 * 2 ^ 59
def prefixEnd_2691416 : Nat := 4983230072969 + 3 ^ 40 * 2691416 * 2
def baseEnd_2691416 : Nat := 1381990049201347056222409

theorem tailTrace_2691416 : CollatzResearch.WordTrace tailWord_2691416 prefixEnd_2691416 1381990049201347056222409 := by
  unfold tailWord_2691416
  simp only [CollatzResearch.WordTrace]
  refine ⟨49082003008733482051363051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65442670678311309401817401 49082003008733482051363051)
  ·
    refine ⟨73623004513100223077044577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49082003008733482051363051 73623004513100223077044577)
    ·
      refine ⟨55217253384825167307783433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73623004513100223077044577 55217253384825167307783433)
      ·
        refine ⟨41412940038618875480837575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55217253384825167307783433 41412940038618875480837575)
        ·
          refine ⟨62119410057928313221256363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41412940038618875480837575 62119410057928313221256363)
          ·
            refine ⟨93179115086892469831884545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62119410057928313221256363 93179115086892469831884545)
            ·
              refine ⟨69884336315169352373913409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93179115086892469831884545 69884336315169352373913409)
              ·
                refine ⟨52413252236377014280435057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69884336315169352373913409 52413252236377014280435057)
                ·
                  refine ⟨39309939177282760710326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52413252236377014280435057 39309939177282760710326293)
                  ·
                    refine ⟨1842653398935129408296545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39309939177282760710326293 1842653398935129408296545)
                    ·
                      refine ⟨1381990049201347056222409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842653398935129408296545 1381990049201347056222409)
                      ·
                        rfl

theorem cell23_2691416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_2691416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691416 prefixEnd_2691416 := by exact prefixLift 2691416
  have htrace : WordTrace (prefixWord ++ tailWord_2691416) baseStart_2691416 baseEnd_2691416 := by
    simpa [prefixWord, tailWord_2691416, baseEnd_2691416] using wordTrace_append hprefix tailTrace_2691416
  have hstable : (prefixWord ++ tailWord_2691416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691416).length < 2 ^ (prefixWord ++ tailWord_2691416).sum := by decide
  have hdescent : baseEnd_2691416 < baseStart_2691416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691433 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 5, 2, 2]
def baseStart_2691433 : Nat := 118140960795 + 2691433 * 2 ^ 59
def prefixEnd_2691433 : Nat := 4983230072969 + 3 ^ 40 * 2691433 * 2
def baseEnd_2691433 : Nat := 1381998778372473489709831

theorem tailTrace_2691433 : CollatzResearch.WordTrace tailWord_2691433 prefixEnd_2691433 1381998778372473489709831 := by
  unfold tailWord_2691433
  simp only [CollatzResearch.WordTrace]
  refine ⟨98164626058405376006094953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65443084038936917337396635 98164626058405376006094953)
  ·
    refine ⟨73623469543804032004571215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98164626058405376006094953 73623469543804032004571215)
    ·
      refine ⟨110435204315706048006856823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73623469543804032004571215 110435204315706048006856823)
      ·
        refine ⟨165652806473559072010285235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110435204315706048006856823 165652806473559072010285235)
        ·
          refine ⟨248479209710338608015427853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165652806473559072010285235 248479209710338608015427853)
          ·
            refine ⟨93179703641376978005785445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248479209710338608015427853 93179703641376978005785445)
            ·
              refine ⟨17471194432758183376084771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93179703641376978005785445 17471194432758183376084771)
              ·
                refine ⟨26206791649137275064127157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17471194432758183376084771 26206791649137275064127157)
                ·
                  refine ⟨2456886717106619537261921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26206791649137275064127157 2456886717106619537261921)
                  ·
                    refine ⟨1842665037829964652946441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456886717106619537261921 1842665037829964652946441)
                    ·
                      refine ⟨1381998778372473489709831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842665037829964652946441 1381998778372473489709831)
                      ·
                        rfl

theorem cell23_2691433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 2, 2].length) (baseStart_2691433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691433 prefixEnd_2691433 := by exact prefixLift 2691433
  have htrace : WordTrace (prefixWord ++ tailWord_2691433) baseStart_2691433 baseEnd_2691433 := by
    simpa [prefixWord, tailWord_2691433, baseEnd_2691433] using wordTrace_append hprefix tailTrace_2691433
  have hstable : (prefixWord ++ tailWord_2691433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691433).length < 2 ^ (prefixWord ++ tailWord_2691433).sum := by decide
  have hdescent : baseEnd_2691433 < baseStart_2691433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691453 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_2691453 : Nat := 118140960795 + 2691453 * 2 ^ 59
def prefixEnd_2691453 : Nat := 4983230072969 + 3 ^ 40 * 2691453 * 2
def baseEnd_2691453 : Nat := 1382009047985563411459739

theorem tailTrace_2691453 : CollatzResearch.WordTrace tailWord_2691453 prefixEnd_2691453 1382009047985563411459739 := by
  unfold tailWord_2691453
  simp only [CollatzResearch.WordTrace]
  refine ⟨98165355518332919421823013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65443570345555279614548675 98165355518332919421823013)
  ·
    refine ⟨18406004159687422391591815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98165355518332919421823013 18406004159687422391591815)
    ·
      refine ⟨27609006239531133587387723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18406004159687422391591815 27609006239531133587387723)
      ·
        refine ⟨41413509359296700381081585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27609006239531133587387723 41413509359296700381081585)
        ·
          refine ⟨31060132019472525285811189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41413509359296700381081585 31060132019472525285811189)
          ·
            refine ⟨2911887376825549245544799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31060132019472525285811189 2911887376825549245544799)
            ·
              refine ⟨4367831065238323868317199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911887376825549245544799 4367831065238323868317199)
              ·
                refine ⟨6551746597857485802475799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367831065238323868317199 6551746597857485802475799)
                ·
                  refine ⟨9827619896786228703713699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551746597857485802475799 9827619896786228703713699)
                  ·
                    refine ⟨14741429845179343055570549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9827619896786228703713699 14741429845179343055570549)
                    ·
                      refine ⟨1382009047985563411459739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14741429845179343055570549 1382009047985563411459739)
                      ·
                        rfl

theorem cell23_2691453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_2691453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691453 prefixEnd_2691453 := by exact prefixLift 2691453
  have htrace : WordTrace (prefixWord ++ tailWord_2691453) baseStart_2691453 baseEnd_2691453 := by
    simpa [prefixWord, tailWord_2691453, baseEnd_2691453] using wordTrace_append hprefix tailTrace_2691453
  have hstable : (prefixWord ++ tailWord_2691453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691453).length < 2 ^ (prefixWord ++ tailWord_2691453).sum := by decide
  have hdescent : baseEnd_2691453 < baseStart_2691453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691467 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 1, 2, 2]
def baseStart_2691467 : Nat := 118140960795 + 2691467 * 2 ^ 59
def prefixEnd_2691467 : Nat := 4983230072969 + 3 ^ 40 * 2691467 * 2
def baseEnd_2691467 : Nat := 1382016236714726356684675

theorem tailTrace_2691467 : CollatzResearch.WordTrace tailWord_2691467 prefixEnd_2691467 1382016236714726356684675 := by
  unfold tailWord_2691467
  simp only [CollatzResearch.WordTrace]
  refine ⟨98165866140282199812832655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65443910760188133208555103 98165866140282199812832655)
  ·
    refine ⟨147248799210423299719248983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98165866140282199812832655 147248799210423299719248983)
    ·
      refine ⟨220873198815634949578873475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147248799210423299719248983 220873198815634949578873475)
      ·
        refine ⟨331309798223452424368310213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220873198815634949578873475 331309798223452424368310213)
        ·
          refine ⟨62120587166897329569058165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331309798223452424368310213 62120587166897329569058165)
          ·
            refine ⟨5823805046896624647099203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62120587166897329569058165 5823805046896624647099203)
            ·
              refine ⟨8735707570344936970648805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823805046896624647099203 8735707570344936970648805)
              ·
                refine ⟨1637945169439675681996651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8735707570344936970648805 1637945169439675681996651)
                ·
                  refine ⟨2456917754159513522994977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637945169439675681996651 2456917754159513522994977)
                  ·
                    refine ⟨1842688315619635142246233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456917754159513522994977 1842688315619635142246233)
                    ·
                      refine ⟨1382016236714726356684675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842688315619635142246233 1382016236714726356684675)
                      ·
                        rfl

theorem cell23_2691467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 2, 2].length) (baseStart_2691467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691467 prefixEnd_2691467 := by exact prefixLift 2691467
  have htrace : WordTrace (prefixWord ++ tailWord_2691467) baseStart_2691467 baseEnd_2691467 := by
    simpa [prefixWord, tailWord_2691467, baseEnd_2691467] using wordTrace_append hprefix tailTrace_2691467
  have hstable : (prefixWord ++ tailWord_2691467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691467).length < 2 ^ (prefixWord ++ tailWord_2691467).sum := by decide
  have hdescent : baseEnd_2691467 < baseStart_2691467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691493 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 3, 3, 2]
def baseStart_2691493 : Nat := 118140960795 + 2691493 * 2 ^ 59
def prefixEnd_2691493 : Nat := 4983230072969 + 3 ^ 40 * 2691493 * 2
def baseEnd_2691493 : Nat := 1382029587211743254959555

theorem tailTrace_2691493 : CollatzResearch.WordTrace tailWord_2691493 prefixEnd_2691493 1382029587211743254959555 := by
  unfold tailWord_2691493
  simp only [CollatzResearch.WordTrace]
  refine ⟨98166814438188006253279133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65444542958792004168852755 98166814438188006253279133)
  ·
    refine ⟨36812555414320502344979675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98166814438188006253279133 36812555414320502344979675)
    ·
      refine ⟨55218833121480753517469513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36812555414320502344979675 55218833121480753517469513)
      ·
        refine ⟨41414124841110565138102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55218833121480753517469513 41414124841110565138102135)
        ·
          refine ⟨62121187261665847707153203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41414124841110565138102135 62121187261665847707153203)
          ·
            refine ⟨93181780892498771560729805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62121187261665847707153203 93181780892498771560729805)
            ·
              refine ⟨34943167834687039335273677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93181780892498771560729805 34943167834687039335273677)
              ·
                refine ⟨13103687938007639750727629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34943167834687039335273677 13103687938007639750727629)
                ·
                  refine ⟨4913882976752864906522861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13103687938007639750727629 4913882976752864906522861)
                  ·
                    refine ⟨1842706116282324339946073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4913882976752864906522861 1842706116282324339946073)
                    ·
                      refine ⟨1382029587211743254959555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842706116282324339946073 1382029587211743254959555)
                      ·
                        rfl

theorem cell23_2691493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_2691493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691493 prefixEnd_2691493 := by exact prefixLift 2691493
  have htrace : WordTrace (prefixWord ++ tailWord_2691493) baseStart_2691493 baseEnd_2691493 := by
    simpa [prefixWord, tailWord_2691493, baseEnd_2691493] using wordTrace_append hprefix tailTrace_2691493
  have hstable : (prefixWord ++ tailWord_2691493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691493).length < 2 ^ (prefixWord ++ tailWord_2691493).sum := by decide
  have hdescent : baseEnd_2691493 < baseStart_2691493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691501 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2691501 : Nat := 118140960795 + 2691501 * 2 ^ 59
def prefixEnd_2691501 : Nat := 4983230072969 + 3 ^ 40 * 2691501 * 2
def baseEnd_2691501 : Nat := 1382033695056979223659519

theorem tailTrace_2691501 : CollatzResearch.WordTrace tailWord_2691501 prefixEnd_2691501 1382033695056979223659519 := by
  unfold tailWord_2691501
  simp only [CollatzResearch.WordTrace]
  refine ⟨98167106222159023619570357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65444737481439349079713571 98167106222159023619570357)
  ·
    refine ⟨9203166208327408464334721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98167106222159023619570357 9203166208327408464334721)
    ·
      refine ⟨6902374656245556348251041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9203166208327408464334721 6902374656245556348251041)
      ·
        refine ⟨5176780992184167261188281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6902374656245556348251041 5176780992184167261188281)
        ·
          refine ⟨3882585744138125445891211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5176780992184167261188281 3882585744138125445891211)
          ·
            refine ⟨5823878616207188168836817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882585744138125445891211 5823878616207188168836817)
            ·
              refine ⟨4367908962155391126627613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823878616207188168836817 4367908962155391126627613)
              ·
                refine ⟨1637965860808271672485355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4367908962155391126627613 1637965860808271672485355)
                ·
                  refine ⟨2456948791212407508728033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637965860808271672485355 2456948791212407508728033)
                  ·
                    refine ⟨1842711593409305631546025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2456948791212407508728033 1842711593409305631546025)
                    ·
                      refine ⟨1382033695056979223659519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842711593409305631546025 1382033695056979223659519)
                      ·
                        rfl

theorem cell23_2691501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2691501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691501 prefixEnd_2691501 := by exact prefixLift 2691501
  have htrace : WordTrace (prefixWord ++ tailWord_2691501) baseStart_2691501 baseEnd_2691501 := by
    simpa [prefixWord, tailWord_2691501, baseEnd_2691501] using wordTrace_append hprefix tailTrace_2691501
  have hstable : (prefixWord ++ tailWord_2691501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691501).length < 2 ^ (prefixWord ++ tailWord_2691501).sum := by decide
  have hdescent : baseEnd_2691501 < baseStart_2691501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691517 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2691517 : Nat := 118140960795 + 2691517 * 2 ^ 59
def prefixEnd_2691517 : Nat := 4983230072969 + 3 ^ 40 * 2691517 * 2
def baseEnd_2691517 : Nat := 1382041910747451161059445

theorem tailTrace_2691517 : CollatzResearch.WordTrace tailWord_2691517 prefixEnd_2691517 1382041910747451161059445 := by
  unfold tailWord_2691517
  simp only [CollatzResearch.WordTrace]
  refine ⟨98167689790101058352152805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65445126526734038901435203 98167689790101058352152805)
  ·
    refine ⟨18406441835643948441028651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98167689790101058352152805 18406441835643948441028651)
    ·
      refine ⟨27609662753465922661542977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18406441835643948441028651 27609662753465922661542977)
      ·
        refine ⟨20707247065099441996157233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27609662753465922661542977 20707247065099441996157233)
        ·
          refine ⟨15530435298824581497117925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20707247065099441996157233 15530435298824581497117925)
          ·
            refine ⟨2911956618529609030709611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15530435298824581497117925 2911956618529609030709611)
            ·
              refine ⟨4367934927794413546064417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911956618529609030709611 4367934927794413546064417)
              ·
                refine ⟨3275951195845810159548313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367934927794413546064417 3275951195845810159548313)
                ·
                  refine ⟨2456963396884357619661235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3275951195845810159548313 2456963396884357619661235)
                  ·
                    refine ⟨3685445095326536429491853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2456963396884357619661235 3685445095326536429491853)
                    ·
                      refine ⟨1382041910747451161059445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3685445095326536429491853 1382041910747451161059445)
                      ·
                        rfl

theorem cell23_2691517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2691517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691517 prefixEnd_2691517 := by exact prefixLift 2691517
  have htrace : WordTrace (prefixWord ++ tailWord_2691517) baseStart_2691517 baseEnd_2691517 := by
    simpa [prefixWord, tailWord_2691517, baseEnd_2691517] using wordTrace_append hprefix tailTrace_2691517
  have hstable : (prefixWord ++ tailWord_2691517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691517).length < 2 ^ (prefixWord ++ tailWord_2691517).sum := by decide
  have hdescent : baseEnd_2691517 < baseStart_2691517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691546 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_2691546 : Nat := 118140960795 + 2691546 * 2 ^ 59
def prefixEnd_2691546 : Nat := 4983230072969 + 3 ^ 40 * 2691546 * 2
def baseEnd_2691546 : Nat := 153561866854047949732979

theorem tailTrace_2691546 : CollatzResearch.WordTrace tailWord_2691546 prefixEnd_2691546 153561866854047949732979 := by
  unfold tailWord_2691546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24542186876748999076239623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65445831671330664203305661 24542186876748999076239623)
  ·
    refine ⟨36813280315123498614359435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24542186876748999076239623 36813280315123498614359435)
    ·
      refine ⟨55219920472685247921539153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36813280315123498614359435 55219920472685247921539153)
      ·
        refine ⟨41414940354513935941154365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55219920472685247921539153 41414940354513935941154365)
        ·
          refine ⟨15530602632942725977932887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41414940354513935941154365 15530602632942725977932887)
          ·
            refine ⟨23295903949414088966899331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15530602632942725977932887 23295903949414088966899331)
            ·
              refine ⟨34943855924121133450348997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23295903949414088966899331 34943855924121133450348997)
              ·
                refine ⟨6551972985772712521940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34943855924121133450348997 6551972985772712521940437)
                ·
                  refine ⟨153561866854047949732979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6551972985772712521940437 153561866854047949732979)
                  ·
                    rfl

theorem cell23_2691546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_2691546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691546 prefixEnd_2691546 := by exact prefixLift 2691546
  have htrace : WordTrace (prefixWord ++ tailWord_2691546) baseStart_2691546 baseEnd_2691546 := by
    simpa [prefixWord, tailWord_2691546, baseEnd_2691546] using wordTrace_append hprefix tailTrace_2691546
  have hstable : (prefixWord ++ tailWord_2691546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691546).length < 2 ^ (prefixWord ++ tailWord_2691546).sum := by decide
  have hdescent : baseEnd_2691546 < baseStart_2691546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691583 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 5, 2]
def baseStart_2691583 : Nat := 118140960795 + 2691583 * 2 ^ 59
def prefixEnd_2691583 : Nat := 4983230072969 + 3 ^ 40 * 2691583 * 2
def baseEnd_2691583 : Nat := 1382075800470647902834141

theorem tailTrace_2691583 : CollatzResearch.WordTrace tailWord_2691583 prefixEnd_2691583 1382075800470647902834141 := by
  unfold tailWord_2691583
  simp only [CollatzResearch.WordTrace]
  refine ⟨98170097007861951624055403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65446731338574634416036935 98170097007861951624055403)
  ·
    refine ⟨147255145511792927436083105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98170097007861951624055403 147255145511792927436083105)
    ·
      refine ⟨110441359133844695577062329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147255145511792927436083105 110441359133844695577062329)
      ·
        refine ⟨82831019350383521682796747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110441359133844695577062329 82831019350383521682796747)
        ·
          refine ⟨124246529025575282524195121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82831019350383521682796747 124246529025575282524195121)
          ·
            refine ⟨93184896769181461893146341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124246529025575282524195121 93184896769181461893146341)
            ·
              refine ⟨17472168144221524104964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93184896769181461893146341 17472168144221524104964939)
              ·
                refine ⟨26208252216332286157447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17472168144221524104964939 26208252216332286157447409)
                ·
                  refine ⟨19656189162249214618085557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26208252216332286157447409 19656189162249214618085557)
                  ·
                    refine ⟨1842767733960863870445521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19656189162249214618085557 1842767733960863870445521)
                    ·
                      refine ⟨1382075800470647902834141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842767733960863870445521 1382075800470647902834141)
                      ·
                        rfl

theorem cell23_2691583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_2691583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691583 prefixEnd_2691583 := by exact prefixLift 2691583
  have htrace : WordTrace (prefixWord ++ tailWord_2691583) baseStart_2691583 baseEnd_2691583 := by
    simpa [prefixWord, tailWord_2691583, baseEnd_2691583] using wordTrace_append hprefix tailTrace_2691583
  have hstable : (prefixWord ++ tailWord_2691583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691583).length < 2 ^ (prefixWord ++ tailWord_2691583).sum := by decide
  have hdescent : baseEnd_2691583 < baseStart_2691583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691591 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2691591 : Nat := 118140960795 + 2691591 * 2 ^ 59
def prefixEnd_2691591 : Nat := 4983230072969 + 3 ^ 40 * 2691591 * 2
def baseEnd_2691591 : Nat := 1382079908315883871534105

theorem tailTrace_2691591 : CollatzResearch.WordTrace tailWord_2691591 prefixEnd_2691591 1382079908315883871534105 := by
  unfold tailWord_2691591
  simp only [CollatzResearch.WordTrace]
  refine ⟨98170388791832968990346627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65446925861221979326897751 98170388791832968990346627)
  ·
    refine ⟨147255583187749453485519941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98170388791832968990346627 147255583187749453485519941)
    ·
      refine ⟨27610421847703022528534989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147255583187749453485519941 27610421847703022528534989)
      ·
        refine ⟨10353908192888633448200621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27610421847703022528534989 10353908192888633448200621)
        ·
          refine ⟨3882715572333237543075233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10353908192888633448200621 3882715572333237543075233)
          ·
            refine ⟨2912036679249928157306425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882715572333237543075233 2912036679249928157306425)
            ·
              refine ⟨2184027509437446117979819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912036679249928157306425 2184027509437446117979819)
              ·
                refine ⟨3276041264156169176969729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184027509437446117979819 3276041264156169176969729)
                ·
                  refine ⟨2457030948117126882727297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3276041264156169176969729 2457030948117126882727297)
                  ·
                    refine ⟨1842773211087845162045473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457030948117126882727297 1842773211087845162045473)
                    ·
                      refine ⟨1382079908315883871534105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842773211087845162045473 1382079908315883871534105)
                      ·
                        rfl

theorem cell23_2691591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2691591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691591 prefixEnd_2691591 := by exact prefixLift 2691591
  have htrace : WordTrace (prefixWord ++ tailWord_2691591) baseStart_2691591 baseEnd_2691591 := by
    simpa [prefixWord, tailWord_2691591, baseEnd_2691591] using wordTrace_append hprefix tailTrace_2691591
  have hstable : (prefixWord ++ tailWord_2691591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691591).length < 2 ^ (prefixWord ++ tailWord_2691591).sum := by decide
  have hdescent : baseEnd_2691591 < baseStart_2691591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691653 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 6]
def baseStart_2691653 : Nat := 118140960795 + 2691653 * 2 ^ 59
def prefixEnd_2691653 : Nat := 4983230072969 + 3 ^ 40 * 2691653 * 2
def baseEnd_2691653 : Nat := 153567971568495847662091

theorem tailTrace_2691653 : CollatzResearch.WordTrace tailWord_2691653 prefixEnd_2691653 153567971568495847662091 := by
  unfold tailWord_2691653
  simp only [CollatzResearch.WordTrace]
  refine ⟨98172650117608353579103613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65448433411738902386069075 98172650117608353579103613)
  ·
    refine ⟨36814743794103132592163855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98172650117608353579103613 36814743794103132592163855)
    ·
      refine ⟨55222115691154698888245783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36814743794103132592163855 55222115691154698888245783)
      ·
        refine ⟨82833173536732048332368675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55222115691154698888245783 82833173536732048332368675)
        ·
          refine ⟨124249760305098072498553013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82833173536732048332368675 124249760305098072498553013)
          ·
            refine ⟨11648415028602944296739345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124249760305098072498553013 11648415028602944296739345)
            ·
              refine ⟨8736311271452208222554509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11648415028602944296739345 8736311271452208222554509)
              ·
                refine ⟨3276116726794578083457941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8736311271452208222554509 3276116726794578083457941)
                ·
                  refine ⟨153567971568495847662091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3276116726794578083457941 153567971568495847662091)
                  ·
                    rfl

theorem cell23_2691653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_2691653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691653 prefixEnd_2691653 := by exact prefixLift 2691653
  have htrace : WordTrace (prefixWord ++ tailWord_2691653) baseStart_2691653 baseEnd_2691653 := by
    simpa [prefixWord, tailWord_2691653, baseEnd_2691653] using wordTrace_append hprefix tailTrace_2691653
  have hstable : (prefixWord ++ tailWord_2691653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691653).length < 2 ^ (prefixWord ++ tailWord_2691653).sum := by decide
  have hdescent : baseEnd_2691653 < baseStart_2691653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691703 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_2691703 : Nat := 118140960795 + 2691703 * 2 ^ 59
def prefixEnd_2691703 : Nat := 4983230072969 + 3 ^ 40 * 2691703 * 2
def baseEnd_2691703 : Nat := 1382137418149187433333589

theorem tailTrace_2691703 : CollatzResearch.WordTrace tailWord_2691703 prefixEnd_2691703 1382137418149187433333589 := by
  unfold tailWord_2691703
  simp only [CollatzResearch.WordTrace]
  refine ⟨98174473767427212118423763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65449649178284808078949175 98174473767427212118423763)
  ·
    refine ⟨147261710651140818177635645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98174473767427212118423763 147261710651140818177635645)
    ·
      refine ⟨55223141494177806816613367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147261710651140818177635645 55223141494177806816613367)
      ·
        refine ⟨82834712241266710224920051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55223141494177806816613367 82834712241266710224920051)
        ·
          refine ⟨124252068361900065337380077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82834712241266710224920051 124252068361900065337380077)
          ·
            refine ⟨46594525635712524501517529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124252068361900065337380077 46594525635712524501517529)
            ·
              refine ⟨34945894226784393376138147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46594525635712524501517529 34945894226784393376138147)
              ·
                refine ⟨52418841340176590064207221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34945894226784393376138147 52418841340176590064207221)
                ·
                  refine ⟨4914266375641555318519427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52418841340176590064207221 4914266375641555318519427)
                  ·
                    refine ⟨7371399563462332977779141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914266375641555318519427 7371399563462332977779141)
                    ·
                      refine ⟨1382137418149187433333589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7371399563462332977779141 1382137418149187433333589)
                      ·
                        rfl

theorem cell23_2691703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_2691703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691703 prefixEnd_2691703 := by exact prefixLift 2691703
  have htrace : WordTrace (prefixWord ++ tailWord_2691703) baseStart_2691703 baseEnd_2691703 := by
    simpa [prefixWord, tailWord_2691703, baseEnd_2691703] using wordTrace_append hprefix tailTrace_2691703
  have hstable : (prefixWord ++ tailWord_2691703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691703).length < 2 ^ (prefixWord ++ tailWord_2691703).sum := by decide
  have hdescent : baseEnd_2691703 < baseStart_2691703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691740 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2691740 : Nat := 118140960795 + 2691740 * 2 ^ 59
def prefixEnd_2691740 : Nat := 4983230072969 + 3 ^ 40 * 2691740 * 2
def baseEnd_2691740 : Nat := 1382156416933403788570919

theorem tailTrace_2691740 : CollatzResearch.WordTrace tailWord_2691740 prefixEnd_2691740 1382156416933403788570919 := by
  unfold tailWord_2691740
  simp only [CollatzResearch.WordTrace]
  refine ⟨49087911634146583718760337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65450548845528778291680449 49087911634146583718760337)
  ·
    refine ⟨36815933725609937789070253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49087911634146583718760337 36815933725609937789070253)
    ·
      refine ⟨13805975147103726670901345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36815933725609937789070253 13805975147103726670901345)
      ·
        refine ⟨10354481360327795003176009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13805975147103726670901345 10354481360327795003176009)
        ·
          refine ⟨7765861020245846252382007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10354481360327795003176009 7765861020245846252382007)
          ·
            refine ⟨11648791530368769378573011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7765861020245846252382007 11648791530368769378573011)
            ·
              refine ⟨17473187295553154067859517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11648791530368769378573011 17473187295553154067859517)
              ·
                refine ⟨6552445235832432775447319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17473187295553154067859517 6552445235832432775447319)
                ·
                  refine ⟨9828667853748649163170979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552445235832432775447319 9828667853748649163170979)
                  ·
                    refine ⟨14743001780622973744756469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9828667853748649163170979 14743001780622973744756469)
                    ·
                      refine ⟨1382156416933403788570919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14743001780622973744756469 1382156416933403788570919)
                      ·
                        rfl

theorem cell23_2691740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2691740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691740 prefixEnd_2691740 := by exact prefixLift 2691740
  have htrace : WordTrace (prefixWord ++ tailWord_2691740) baseStart_2691740 baseEnd_2691740 := by
    simpa [prefixWord, tailWord_2691740, baseEnd_2691740] using wordTrace_append hprefix tailTrace_2691740
  have hstable : (prefixWord ++ tailWord_2691740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691740).length < 2 ^ (prefixWord ++ tailWord_2691740).sum := by decide
  have hdescent : baseEnd_2691740 < baseStart_2691740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691770 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_2691770 : Nat := 118140960795 + 2691770 * 2 ^ 59
def prefixEnd_2691770 : Nat := 4983230072969 + 3 ^ 40 * 2691770 * 2
def baseEnd_2691770 : Nat := 1382171821353038671195781

theorem tailTrace_2691770 : CollatzResearch.WordTrace tailWord_2691770 prefixEnd_2691770 1382171821353038671195781 := by
  unfold tailWord_2691770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24544229364546120640278191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65451278305456321707408509 24544229364546120640278191)
  ·
    refine ⟨36816344046819180960417287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24544229364546120640278191 36816344046819180960417287)
    ·
      refine ⟨55224516070228771440625931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36816344046819180960417287 55224516070228771440625931)
      ·
        refine ⟨82836774105343157160938897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55224516070228771440625931 82836774105343157160938897)
        ·
          refine ⟨62127580579007367870704173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82836774105343157160938897 62127580579007367870704173)
          ·
            refine ⟨23297842717127762951514065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62127580579007367870704173 23297842717127762951514065)
            ·
              refine ⟨17473382037845822213635549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23297842717127762951514065 17473382037845822213635549)
              ·
                refine ⟨6552518264192183330113331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17473382037845822213635549 6552518264192183330113331)
                ·
                  refine ⟨9828777396288274995169997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6552518264192183330113331 9828777396288274995169997)
                  ·
                    refine ⟨3685791523608103123188749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9828777396288274995169997 3685791523608103123188749)
                    ·
                      refine ⟨1382171821353038671195781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3685791523608103123188749 1382171821353038671195781)
                      ·
                        rfl

theorem cell23_2691770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_2691770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691770 prefixEnd_2691770 := by exact prefixLift 2691770
  have htrace : WordTrace (prefixWord ++ tailWord_2691770) baseStart_2691770 baseEnd_2691770 := by
    simpa [prefixWord, tailWord_2691770, baseEnd_2691770] using wordTrace_append hprefix tailTrace_2691770
  have hstable : (prefixWord ++ tailWord_2691770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691770).length < 2 ^ (prefixWord ++ tailWord_2691770).sum := by decide
  have hdescent : baseEnd_2691770 < baseStart_2691770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691783 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2691783 : Nat := 118140960795 + 2691783 * 2 ^ 59
def prefixEnd_2691783 : Nat := 4983230072969 + 3 ^ 40 * 2691783 * 2
def baseEnd_2691783 : Nat := 1382178496601547120333221

theorem tailTrace_2691783 : CollatzResearch.WordTrace tailWord_2691783 prefixEnd_2691783 1382178496601547120333221 := by
  unfold tailWord_2691783
  simp only [CollatzResearch.WordTrace]
  refine ⟨98177391607137385781336003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65451594404758257187557335 98177391607137385781336003)
  ·
    refine ⟨147266087410706078672004005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98177391607137385781336003 147266087410706078672004005)
    ·
      refine ⟨27612391389507389751000751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147266087410706078672004005 27612391389507389751000751)
      ·
        refine ⟨41418587084261084626501127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27612391389507389751000751 41418587084261084626501127)
        ·
          refine ⟨62127880626391626939751691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41418587084261084626501127 62127880626391626939751691)
          ·
            refine ⟨93191820939587440409627537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62127880626391626939751691 93191820939587440409627537)
            ·
              refine ⟨69893865704690580307220653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93191820939587440409627537 69893865704690580307220653)
              ·
                refine ⟨26210199639258967615207745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69893865704690580307220653 26210199639258967615207745)
                ·
                  refine ⟨19657649729444225711405809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26210199639258967615207745 19657649729444225711405809)
                  ·
                    refine ⟨14743237297083169283554357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19657649729444225711405809 14743237297083169283554357)
                    ·
                      refine ⟨1382178496601547120333221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14743237297083169283554357 1382178496601547120333221)
                      ·
                        rfl

theorem cell23_2691783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2691783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691783 prefixEnd_2691783 := by exact prefixLift 2691783
  have htrace : WordTrace (prefixWord ++ tailWord_2691783) baseStart_2691783 baseEnd_2691783 := by
    simpa [prefixWord, tailWord_2691783, baseEnd_2691783] using wordTrace_append hprefix tailTrace_2691783
  have hstable : (prefixWord ++ tailWord_2691783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691783).length < 2 ^ (prefixWord ++ tailWord_2691783).sum := by decide
  have hdescent : baseEnd_2691783 < baseStart_2691783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691827 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 6, 2, 2]
def baseStart_2691827 : Nat := 118140960795 + 2691827 * 2 ^ 59
def prefixEnd_2691827 : Nat := 4983230072969 + 3 ^ 40 * 2691827 * 2
def baseEnd_2691827 : Nat := 1382201089750344948183019

theorem tailTrace_2691827 : CollatzResearch.WordTrace tailWord_2691827 prefixEnd_2691827 1382201089750344948183019 := by
  unfold tailWord_2691827
  simp only [CollatzResearch.WordTrace]
  refine ⟨98178996418977981295937735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65452664279318654197291823 98178996418977981295937735)
  ·
    refine ⟨147268494628466971943906603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98178996418977981295937735 147268494628466971943906603)
    ·
      refine ⟨220902741942700457915859905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147268494628466971943906603 220902741942700457915859905)
      ·
        refine ⟨165677056457025343436894929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220902741942700457915859905 165677056457025343436894929)
        ·
          refine ⟨124257792342769007577671197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165677056457025343436894929 124257792342769007577671197)
          ·
            refine ⟨46596672128538377841626699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124257792342769007577671197 46596672128538377841626699)
            ·
              refine ⟨69895008192807566762440049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46596672128538377841626699 69895008192807566762440049)
              ·
                refine ⟨52421256144605675071830037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69895008192807566762440049 52421256144605675071830037)
                ·
                  refine ⟨2457246381778391018992033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52421256144605675071830037 2457246381778391018992033)
                  ·
                    refine ⟨1842934786333793264244025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457246381778391018992033 1842934786333793264244025)
                    ·
                      refine ⟨1382201089750344948183019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842934786333793264244025 1382201089750344948183019)
                      ·
                        rfl

theorem cell23_2691827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 2, 2].length) (baseStart_2691827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691827 prefixEnd_2691827 := by exact prefixLift 2691827
  have htrace : WordTrace (prefixWord ++ tailWord_2691827) baseStart_2691827 baseEnd_2691827 := by
    simpa [prefixWord, tailWord_2691827, baseEnd_2691827] using wordTrace_append hprefix tailTrace_2691827
  have hstable : (prefixWord ++ tailWord_2691827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691827).length < 2 ^ (prefixWord ++ tailWord_2691827).sum := by decide
  have hdescent : baseEnd_2691827 < baseStart_2691827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2691843 : Nat := 118140960795 + 2691843 * 2 ^ 59
def prefixEnd_2691843 : Nat := 4983230072969 + 3 ^ 40 * 2691843 * 2
def baseEnd_2691843 : Nat := 1382209305440816885582945

theorem tailTrace_2691843 : CollatzResearch.WordTrace tailWord_2691843 prefixEnd_2691843 1382209305440816885582945 := by
  unfold tailWord_2691843
  simp only [CollatzResearch.WordTrace]
  refine ⟨98179579986920016028520183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65453053324613344019013455 98179579986920016028520183)
  ·
    refine ⟨147269369980380024042780275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98179579986920016028520183 147269369980380024042780275)
    ·
      refine ⟨220904054970570036064170413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147269369980380024042780275 220904054970570036064170413)
      ·
        refine ⟨82839020613963763524063905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220904054970570036064170413 82839020613963763524063905)
        ·
          refine ⟨62129265460472822643047929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82839020613963763524063905 62129265460472822643047929)
          ·
            refine ⟨46596949095354616982285947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62129265460472822643047929 46596949095354616982285947)
            ·
              refine ⟨69895423643031925473428921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46596949095354616982285947 69895423643031925473428921)
              ·
                refine ⟨52421567732273944105071691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69895423643031925473428921 52421567732273944105071691)
                ·
                  refine ⟨78632351598410916157607537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52421567732273944105071691 78632351598410916157607537)
                  ·
                    refine ⟨58974263698808187118205653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78632351598410916157607537 58974263698808187118205653)
                    ·
                      refine ⟨1382209305440816885582945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58974263698808187118205653 1382209305440816885582945)
                      ·
                        rfl

theorem cell23_2691843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2691843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691843 prefixEnd_2691843 := by exact prefixLift 2691843
  have htrace : WordTrace (prefixWord ++ tailWord_2691843) baseStart_2691843 baseEnd_2691843 := by
    simpa [prefixWord, tailWord_2691843, baseEnd_2691843] using wordTrace_append hprefix tailTrace_2691843
  have hstable : (prefixWord ++ tailWord_2691843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691843).length < 2 ^ (prefixWord ++ tailWord_2691843).sum := by decide
  have hdescent : baseEnd_2691843 < baseStart_2691843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691844 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2691844 : Nat := 118140960795 + 2691844 * 2 ^ 59
def prefixEnd_2691844 : Nat := 4983230072969 + 3 ^ 40 * 2691844 * 2
def baseEnd_2691844 : Nat := 1382209818921471381670441

theorem tailTrace_2691844 : CollatzResearch.WordTrace tailWord_2691844 prefixEnd_2691844 1382209818921471381670441 := by
  unfold tailWord_2691844
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089808229958196599653293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65453077639944262132871057 49089808229958196599653293)
  ·
    refine ⟨18408678086234323724869985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49089808229958196599653293 18408678086234323724869985)
    ·
      refine ⟨13806508564675742793652489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18408678086234323724869985 13806508564675742793652489)
      ·
        refine ⟨10354881423506807095239367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13806508564675742793652489 10354881423506807095239367)
        ·
          refine ⟨15532322135260210642859051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354881423506807095239367 15532322135260210642859051)
          ·
            refine ⟨23298483202890315964288577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15532322135260210642859051 23298483202890315964288577)
            ·
              refine ⟨17473862402167736973216433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23298483202890315964288577 17473862402167736973216433)
              ·
                refine ⟨13105396801625802729912325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17473862402167736973216433 13105396801625802729912325)
                ·
                  refine ⟨2457261900304838011858561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13105396801625802729912325 2457261900304838011858561)
                  ·
                    refine ⟨1842946425228628508893921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2457261900304838011858561 1842946425228628508893921)
                    ·
                      refine ⟨1382209818921471381670441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1842946425228628508893921 1382209818921471381670441)
                      ·
                        rfl

theorem cell23_2691844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2691844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691844 prefixEnd_2691844 := by exact prefixLift 2691844
  have htrace : WordTrace (prefixWord ++ tailWord_2691844) baseStart_2691844 baseEnd_2691844 := by
    simpa [prefixWord, tailWord_2691844, baseEnd_2691844] using wordTrace_append hprefix tailTrace_2691844
  have hstable : (prefixWord ++ tailWord_2691844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691844).length < 2 ^ (prefixWord ++ tailWord_2691844).sum := by decide
  have hdescent : baseEnd_2691844 < baseStart_2691844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691880 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2691880 : Nat := 118140960795 + 2691880 * 2 ^ 59
def prefixEnd_2691880 : Nat := 4983230072969 + 3 ^ 40 * 2691880 * 2
def baseEnd_2691880 : Nat := 460742768075011080273425

theorem tailTrace_2691880 : CollatzResearch.WordTrace tailWord_2691880 prefixEnd_2691880 460742768075011080273425 := by
  unfold tailWord_2691880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49090464743892985673808547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65453952991857314231744729 49090464743892985673808547)
  ·
    refine ⟨73635697115839478510712821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49090464743892985673808547 73635697115839478510712821)
    ·
      refine ⟨6903346604609951110379327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73635697115839478510712821 6903346604609951110379327)
      ·
        refine ⟨10355019906914926665568991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903346604609951110379327 10355019906914926665568991)
        ·
          refine ⟨15532529860372389998353487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10355019906914926665568991 15532529860372389998353487)
          ·
            refine ⟨23298794790558584997530231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15532529860372389998353487 23298794790558584997530231)
            ·
              refine ⟨34948192185837877496295347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23298794790558584997530231 34948192185837877496295347)
              ·
                refine ⟨52422288278756816244443021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34948192185837877496295347 52422288278756816244443021)
                ·
                  refine ⟨19658358104533806091666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52422288278756816244443021 19658358104533806091666133)
                  ·
                    refine ⟨460742768075011080273425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19658358104533806091666133 460742768075011080273425)
                    ·
                      rfl

theorem cell23_2691880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2691880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691880 prefixEnd_2691880 := by exact prefixLift 2691880
  have htrace : WordTrace (prefixWord ++ tailWord_2691880) baseStart_2691880 baseEnd_2691880 := by
    simpa [prefixWord, tailWord_2691880, baseEnd_2691880] using wordTrace_append hprefix tailTrace_2691880
  have hstable : (prefixWord ++ tailWord_2691880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691880).length < 2 ^ (prefixWord ++ tailWord_2691880).sum := by decide
  have hdescent : baseEnd_2691880 < baseStart_2691880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691901 : List Nat := [1, 4, 1, 4, 2, 2, 1, 3, 5]
def baseStart_2691901 : Nat := 118140960795 + 2691901 * 2 ^ 59
def prefixEnd_2691901 : Nat := 4983230072969 + 3 ^ 40 * 2691901 * 2
def baseEnd_2691901 : Nat := 153582120813197517628631

theorem tailTrace_2691901 : CollatzResearch.WordTrace tailWord_2691901 prefixEnd_2691901 153582120813197517628631 := by
  unfold tailWord_2691901
  simp only [CollatzResearch.WordTrace]
  refine ⟨98181695420709891934131557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65454463613806594622754371 98181695420709891934131557)
  ·
    refine ⟨18409067891383104737649667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98181695420709891934131557 18409067891383104737649667)
    ·
      refine ⟨27613601837074657106474501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18409067891383104737649667 27613601837074657106474501)
      ·
        refine ⟨5177550344451498207463969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27613601837074657106474501 5177550344451498207463969)
        ·
          refine ⟨3883162758338623655597977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5177550344451498207463969 3883162758338623655597977)
          ·
            refine ⟨2912372068753967741698483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3883162758338623655597977 2912372068753967741698483)
            ·
              refine ⟨4368558103130951612547725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912372068753967741698483 4368558103130951612547725)
              ·
                refine ⟨1638209288674106854705397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4368558103130951612547725 1638209288674106854705397)
                ·
                  refine ⟨153582120813197517628631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1638209288674106854705397 153582120813197517628631)
                  ·
                    rfl

theorem cell23_2691901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_2691901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691901 prefixEnd_2691901 := by exact prefixLift 2691901
  have htrace : WordTrace (prefixWord ++ tailWord_2691901) baseStart_2691901 baseEnd_2691901 := by
    simpa [prefixWord, tailWord_2691901, baseEnd_2691901] using wordTrace_append hprefix tailTrace_2691901
  have hstable : (prefixWord ++ tailWord_2691901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691901).length < 2 ^ (prefixWord ++ tailWord_2691901).sum := by decide
  have hdescent : baseEnd_2691901 < baseStart_2691901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691978 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_2691978 : Nat := 118140960795 + 2691978 * 2 ^ 59
def prefixEnd_2691978 : Nat := 4983230072969 + 3 ^ 40 * 2691978 * 2
def baseEnd_2691978 : Nat := 460759541776391285798275

theorem tailTrace_2691978 : CollatzResearch.WordTrace tailWord_2691978 prefixEnd_2691978 460759541776391285798275 := by
  unfold tailWord_2691978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24546125960357733521171147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65456335894287289389789725 24546125960357733521171147)
  ·
    refine ⟨36819188940536600281756721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24546125960357733521171147 36819188940536600281756721)
    ·
      refine ⟨27614391705402450211317541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36819188940536600281756721 27614391705402450211317541)
      ·
        refine ⟨5177698444762959414622039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27614391705402450211317541 5177698444762959414622039)
        ·
          refine ⟨7766547667144439121933059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177698444762959414622039 7766547667144439121933059)
          ·
            refine ⟨11649821500716658682899589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766547667144439121933059 11649821500716658682899589)
            ·
              refine ⟨2184341531384373503043673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11649821500716658682899589 2184341531384373503043673)
              ·
                refine ⟨1638256148538280127282755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2184341531384373503043673 1638256148538280127282755)
                ·
                  refine ⟨2457384222807420190924133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1638256148538280127282755 2457384222807420190924133)
                  ·
                    refine ⟨460759541776391285798275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2457384222807420190924133 460759541776391285798275)
                    ·
                      rfl

theorem cell23_2691978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_2691978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2691978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2691978 prefixEnd_2691978 := by exact prefixLift 2691978
  have htrace : WordTrace (prefixWord ++ tailWord_2691978) baseStart_2691978 baseEnd_2691978 := by
    simpa [prefixWord, tailWord_2691978, baseEnd_2691978] using wordTrace_append hprefix tailTrace_2691978
  have hstable : (prefixWord ++ tailWord_2691978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691978).length < 2 ^ (prefixWord ++ tailWord_2691978).sum := by decide
  have hdescent : baseEnd_2691978 < baseStart_2691978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692001 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2692001 : Nat := 118140960795 + 2692001 * 2 ^ 59
def prefixEnd_2692001 : Nat := 4983230072969 + 3 ^ 40 * 2692001 * 2
def baseEnd_2692001 : Nat := 1382290435384227267407219

theorem tailTrace_2692001 : CollatzResearch.WordTrace tailWord_2692001 prefixEnd_2692001 1382290435384227267407219 := by
  unfold tailWord_2692001
  simp only [CollatzResearch.WordTrace]
  refine ⟨98185342720347609012771857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65456895146898406008514571 98185342720347609012771857)
  ·
    refine ⟨73639007040260706759578893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98185342720347609012771857 73639007040260706759578893)
    ·
      refine ⟨27614627640097765034842085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73639007040260706759578893 27614627640097765034842085)
      ·
        refine ⟨5177742682518330944032891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27614627640097765034842085 5177742682518330944032891)
        ·
          refine ⟨7766614023777496416049337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177742682518330944032891 7766614023777496416049337)
          ·
            refine ⟨5824960517833122312037003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7766614023777496416049337 5824960517833122312037003)
            ·
              refine ⟨8737440776749683468055505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824960517833122312037003 8737440776749683468055505)
              ·
                refine ⟨6553080582562262601041629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737440776749683468055505 6553080582562262601041629)
                ·
                  refine ⟨2457405218460848475390611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6553080582562262601041629 2457405218460848475390611)
                  ·
                    refine ⟨3686107827691272713085917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457405218460848475390611 3686107827691272713085917)
                    ·
                      refine ⟨1382290435384227267407219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686107827691272713085917 1382290435384227267407219)
                      ·
                        rfl

theorem cell23_2692001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2692001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692001 prefixEnd_2692001 := by exact prefixLift 2692001
  have htrace : WordTrace (prefixWord ++ tailWord_2692001) baseStart_2692001 baseEnd_2692001 := by
    simpa [prefixWord, tailWord_2692001, baseEnd_2692001] using wordTrace_append hprefix tailTrace_2692001
  have hstable : (prefixWord ++ tailWord_2692001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692001).length < 2 ^ (prefixWord ++ tailWord_2692001).sum := by decide
  have hdescent : baseEnd_2692001 < baseStart_2692001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692024 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_2692024 : Nat := 118140960795 + 2692024 * 2 ^ 59
def prefixEnd_2692024 : Nat := 4983230072969 + 3 ^ 40 * 2692024 * 2
def baseEnd_2692024 : Nat := 1382302245439280677419613

theorem tailTrace_2692024 : CollatzResearch.WordTrace tailWord_2692024 prefixEnd_2692024 1382302245439280677419613 := by
  unfold tailWord_2692024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49093090799632141970429563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65457454399509522627239417 49093090799632141970429563)
  ·
    refine ⟨73639636199448212955644345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49093090799632141970429563 73639636199448212955644345)
    ·
      refine ⟨55229727149586159716733259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73639636199448212955644345 55229727149586159716733259)
      ·
        refine ⟨82844590724379239575099889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55229727149586159716733259 82844590724379239575099889)
        ·
          refine ⟨62133443043284429681324917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82844590724379239575099889 62133443043284429681324917)
          ·
            refine ⟨5825010285307915282624211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62133443043284429681324917 5825010285307915282624211)
            ·
              refine ⟨8737515427961872923936317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825010285307915282624211 8737515427961872923936317)
              ·
                refine ⟨3276568285485702346476119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8737515427961872923936317 3276568285485702346476119)
                ·
                  refine ⟨4914852428228553519714179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276568285485702346476119 4914852428228553519714179)
                  ·
                    refine ⟨7372278642342830279571269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4914852428228553519714179 7372278642342830279571269)
                    ·
                      refine ⟨1382302245439280677419613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7372278642342830279571269 1382302245439280677419613)
                      ·
                        rfl

theorem cell23_2692024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_2692024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692024 prefixEnd_2692024 := by exact prefixLift 2692024
  have htrace : WordTrace (prefixWord ++ tailWord_2692024) baseStart_2692024 baseEnd_2692024 := by
    simpa [prefixWord, tailWord_2692024, baseEnd_2692024] using wordTrace_append hprefix tailTrace_2692024
  have hstable : (prefixWord ++ tailWord_2692024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692024).length < 2 ^ (prefixWord ++ tailWord_2692024).sum := by decide
  have hdescent : baseEnd_2692024 < baseStart_2692024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692061 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2692061 : Nat := 118140960795 + 2692061 * 2 ^ 59
def prefixEnd_2692061 : Nat := 4983230072969 + 3 ^ 40 * 2692061 * 2
def baseEnd_2692061 : Nat := 1382321244223497032656943

theorem tailTrace_2692061 : CollatzResearch.WordTrace tailWord_2692061 prefixEnd_2692061 1382321244223497032656943 := by
  unfold tailWord_2692061
  simp only [CollatzResearch.WordTrace]
  refine ⟨98187531100130239259956037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65458354066753492839970691 98187531100130239259956037)
  ·
    refine ⟨18410162081274419861241757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98187531100130239259956037 18410162081274419861241757)
    ·
      refine ⟨6903810780477907447965659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18410162081274419861241757 6903810780477907447965659)
      ·
        refine ⟨10355716170716861171948489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903810780477907447965659 10355716170716861171948489)
        ·
          refine ⟨7766787128037645878961367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10355716170716861171948489 7766787128037645878961367)
          ·
            refine ⟨11650180692056468818442051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766787128037645878961367 11650180692056468818442051)
            ·
              refine ⟨17475271038084703227663077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650180692056468818442051 17475271038084703227663077)
              ·
                refine ⟨3276613319640881855186827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17475271038084703227663077 3276613319640881855186827)
                ·
                  refine ⟨4914919979461322782780241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276613319640881855186827 4914919979461322782780241)
                  ·
                    refine ⟨3686189984595992087085181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4914919979461322782780241 3686189984595992087085181)
                    ·
                      refine ⟨1382321244223497032656943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686189984595992087085181 1382321244223497032656943)
                      ·
                        rfl

theorem cell23_2692061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2692061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692061 prefixEnd_2692061 := by exact prefixLift 2692061
  have htrace : WordTrace (prefixWord ++ tailWord_2692061) baseStart_2692061 baseEnd_2692061 := by
    simpa [prefixWord, tailWord_2692061, baseEnd_2692061] using wordTrace_append hprefix tailTrace_2692061
  have hstable : (prefixWord ++ tailWord_2692061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692061).length < 2 ^ (prefixWord ++ tailWord_2692061).sum := by decide
  have hdescent : baseEnd_2692061 < baseStart_2692061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692108 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 2, 1, 3]
def baseStart_2692108 : Nat := 118140960795 + 2692108 * 2 ^ 59
def prefixEnd_2692108 : Nat := 4983230072969 + 3 ^ 40 * 2692108 * 2
def baseEnd_2692108 : Nat := 1382345377814258348769227

theorem tailTrace_2692108 : CollatzResearch.WordTrace tailWord_2692108 prefixEnd_2692108 1382345377814258348769227 := by
  unfold tailWord_2692108
  simp only [CollatzResearch.WordTrace]
  refine ⟨49094622665479983143458489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65459496887306644191277985 49094622665479983143458489)
  ·
    refine ⟨36820966999109987357593867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49094622665479983143458489 36820966999109987357593867)
    ·
      refine ⟨55231450498664981036390801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36820966999109987357593867 55231450498664981036390801)
      ·
        refine ⟨41423587873998735777293101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55231450498664981036390801 41423587873998735777293101)
        ·
          refine ⟨15533845452749525916484913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41423587873998735777293101 15533845452749525916484913)
          ·
            refine ⟨11650384089562144437363685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15533845452749525916484913 11650384089562144437363685)
            ·
              refine ⟨2184447016792902082005691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11650384089562144437363685 2184447016792902082005691)
              ·
                refine ⟨3276670525189353123008537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184447016792902082005691 3276670525189353123008537)
                ·
                  refine ⟨2457502893892014842256403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3276670525189353123008537 2457502893892014842256403)
                  ·
                    refine ⟨3686254340838022263384605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2457502893892014842256403 3686254340838022263384605)
                    ·
                      refine ⟨1382345377814258348769227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686254340838022263384605 1382345377814258348769227)
                      ·
                        rfl

theorem cell23_2692108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_2692108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692108 prefixEnd_2692108 := by exact prefixLift 2692108
  have htrace : WordTrace (prefixWord ++ tailWord_2692108) baseStart_2692108 baseEnd_2692108 := by
    simpa [prefixWord, tailWord_2692108, baseEnd_2692108] using wordTrace_append hprefix tailTrace_2692108
  have hstable : (prefixWord ++ tailWord_2692108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692108).length < 2 ^ (prefixWord ++ tailWord_2692108).sum := by decide
  have hdescent : baseEnd_2692108 < baseStart_2692108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692131 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 4, 2]
def baseStart_2692131 : Nat := 118140960795 + 2692131 * 2 ^ 59
def prefixEnd_2692131 : Nat := 4983230072969 + 3 ^ 40 * 2692131 * 2
def baseEnd_2692131 : Nat := 1382357187869311758781621

theorem tailTrace_2692131 : CollatzResearch.WordTrace tailWord_2692131 prefixEnd_2692131 1382357187869311758781621 := by
  unfold tailWord_2692131
  simp only [CollatzResearch.WordTrace]
  refine ⟨98190084209876641215004247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65460056139917760810002831 98190084209876641215004247)
  ·
    refine ⟨147285126314814961822506371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98190084209876641215004247 147285126314814961822506371)
    ·
      refine ⟨220927689472222442733759557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147285126314814961822506371 220927689472222442733759557)
      ·
        refine ⟨41423941776041708012579917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220927689472222442733759557 41423941776041708012579917)
        ·
          refine ⟨15533978166015640504717469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41423941776041708012579917 15533978166015640504717469)
          ·
            refine ⟨5825241812255865189269051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15533978166015640504717469 5825241812255865189269051)
            ·
              refine ⟨8737862718383797783903577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825241812255865189269051 8737862718383797783903577)
              ·
                refine ⟨6553397038787848337927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8737862718383797783903577 6553397038787848337927683)
                ·
                  refine ⟨9830095558181772506891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6553397038787848337927683 9830095558181772506891525)
                  ·
                    refine ⟨1843142917159082345042161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9830095558181772506891525 1843142917159082345042161)
                    ·
                      refine ⟨1382357187869311758781621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843142917159082345042161 1382357187869311758781621)
                      ·
                        rfl

theorem cell23_2692131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_2692131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692131 prefixEnd_2692131 := by exact prefixLift 2692131
  have htrace : WordTrace (prefixWord ++ tailWord_2692131) baseStart_2692131 baseEnd_2692131 := by
    simpa [prefixWord, tailWord_2692131, baseEnd_2692131] using wordTrace_append hprefix tailTrace_2692131
  have hstable : (prefixWord ++ tailWord_2692131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692131).length < 2 ^ (prefixWord ++ tailWord_2692131).sum := by decide
  have hdescent : baseEnd_2692131 < baseStart_2692131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692161 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2692161 : Nat := 118140960795 + 2692161 * 2 ^ 59
def prefixEnd_2692161 : Nat := 4983230072969 + 3 ^ 40 * 2692161 * 2
def baseEnd_2692161 : Nat := 1382372592288946641406483

theorem tailTrace_2692161 : CollatzResearch.WordTrace tailWord_2692161 prefixEnd_2692161 1382372592288946641406483 := by
  unfold tailWord_2692161
  simp only [CollatzResearch.WordTrace]
  refine ⟨98191178399767956338596337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65460785599845304225730891 98191178399767956338596337)
  ·
    refine ⟨73643383799825967253947253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98191178399767956338596337 73643383799825967253947253)
    ·
      refine ⟨6904067231233684430057555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73643383799825967253947253 6904067231233684430057555)
      ·
        refine ⟨10356100846850526645086333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904067231233684430057555 10356100846850526645086333)
        ·
          refine ⟨3883537817568947491907375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10356100846850526645086333 3883537817568947491907375)
          ·
            refine ⟨5825306726353421237861063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883537817568947491907375 5825306726353421237861063)
            ·
              refine ⟨8737960089530131856791595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825306726353421237861063 8737960089530131856791595)
              ·
                refine ⟨13106940134295197785187393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737960089530131856791595 13106940134295197785187393)
                ·
                  refine ⟨9830205100721398338890545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13106940134295197785187393 9830205100721398338890545)
                  ·
                    refine ⟨7372653825541048754167909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9830205100721398338890545 7372653825541048754167909)
                    ·
                      refine ⟨1382372592288946641406483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7372653825541048754167909 1382372592288946641406483)
                      ·
                        rfl

theorem cell23_2692161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2692161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692161 prefixEnd_2692161 := by exact prefixLift 2692161
  have htrace : WordTrace (prefixWord ++ tailWord_2692161) baseStart_2692161 baseEnd_2692161 := by
    simpa [prefixWord, tailWord_2692161, baseEnd_2692161] using wordTrace_append hprefix tailTrace_2692161
  have hstable : (prefixWord ++ tailWord_2692161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692161).length < 2 ^ (prefixWord ++ tailWord_2692161).sum := by decide
  have hdescent : baseEnd_2692161 < baseStart_2692161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692177 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2692177 : Nat := 118140960795 + 2692177 * 2 ^ 59
def prefixEnd_2692177 : Nat := 4983230072969 + 3 ^ 40 * 2692177 * 2
def baseEnd_2692177 : Nat := 1382380807979418578806409

theorem tailTrace_2692177 : CollatzResearch.WordTrace tailWord_2692177 prefixEnd_2692177 1382380807979418578806409 := by
  unfold tailWord_2692177
  simp only [CollatzResearch.WordTrace]
  refine ⟨98191761967709991071178785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65461174645139994047452523 98191761967709991071178785)
  ·
    refine ⟨73643821475782493303384089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98191761967709991071178785 73643821475782493303384089)
    ·
      refine ⟨55232866106836869977538067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73643821475782493303384089 55232866106836869977538067)
      ·
        refine ⟨82849299160255304966307101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55232866106836869977538067 82849299160255304966307101)
        ·
          refine ⟨31068487185095739362365163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82849299160255304966307101 31068487185095739362365163)
          ·
            refine ⟨46602730777643609043547745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31068487185095739362365163 46602730777643609043547745)
            ·
              refine ⟨34952048083232706782660809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46602730777643609043547745 34952048083232706782660809)
              ·
                refine ⟨26214036062424530086995607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34952048083232706782660809 26214036062424530086995607)
                ·
                  refine ⟨39321054093636795130493411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26214036062424530086995607 39321054093636795130493411)
                  ·
                    refine ⟨58981581140455192695740117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39321054093636795130493411 58981581140455192695740117)
                    ·
                      refine ⟨1382380807979418578806409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58981581140455192695740117 1382380807979418578806409)
                      ·
                        rfl

theorem cell23_2692177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2692177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692177 prefixEnd_2692177 := by exact prefixLift 2692177
  have htrace : WordTrace (prefixWord ++ tailWord_2692177) baseStart_2692177 baseEnd_2692177 := by
    simpa [prefixWord, tailWord_2692177, baseEnd_2692177] using wordTrace_append hprefix tailTrace_2692177
  have hstable : (prefixWord ++ tailWord_2692177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692177).length < 2 ^ (prefixWord ++ tailWord_2692177).sum := by decide
  have hdescent : baseEnd_2692177 < baseStart_2692177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692204 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_2692204 : Nat := 118140960795 + 2692204 * 2 ^ 59
def prefixEnd_2692204 : Nat := 4983230072969 + 3 ^ 40 * 2692204 * 2
def baseEnd_2692204 : Nat := 1382394671957089973168785

theorem tailTrace_2692204 : CollatzResearch.WordTrace tailWord_2692204 prefixEnd_2692204 1382394671957089973168785 := by
  unfold tailWord_2692204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49096373369306087341205833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65461831159074783121607777 49096373369306087341205833)
  ·
    refine ⟨36822280026979565505904375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49096373369306087341205833 36822280026979565505904375)
    ·
      refine ⟨55233420040469348258856563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36822280026979565505904375 55233420040469348258856563)
      ·
        refine ⟨82850130060704022388284845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55233420040469348258856563 82850130060704022388284845)
        ·
          refine ⟨31068798772764008395606817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82850130060704022388284845 31068798772764008395606817)
          ·
            refine ⟨23301599079573006296705113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31068798772764008395606817 23301599079573006296705113)
            ·
              refine ⟨17476199309679754722528835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23301599079573006296705113 17476199309679754722528835)
              ·
                refine ⟨26214298964519632083793253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17476199309679754722528835 26214298964519632083793253)
                ·
                  refine ⟨4915181055847431015711235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26214298964519632083793253 4915181055847431015711235)
                  ·
                    refine ⟨7372771583771146523566853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915181055847431015711235 7372771583771146523566853)
                    ·
                      refine ⟨1382394671957089973168785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7372771583771146523566853 1382394671957089973168785)
                      ·
                        rfl

theorem cell23_2692204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_2692204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692204 prefixEnd_2692204 := by exact prefixLift 2692204
  have htrace : WordTrace (prefixWord ++ tailWord_2692204) baseStart_2692204 baseEnd_2692204 := by
    simpa [prefixWord, tailWord_2692204, baseEnd_2692204] using wordTrace_append hprefix tailTrace_2692204
  have hstable : (prefixWord ++ tailWord_2692204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692204).length < 2 ^ (prefixWord ++ tailWord_2692204).sum := by decide
  have hdescent : baseEnd_2692204 < baseStart_2692204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692221 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_2692221 : Nat := 118140960795 + 2692221 * 2 ^ 59
def prefixEnd_2692221 : Nat := 4983230072969 + 3 ^ 40 * 2692221 * 2
def baseEnd_2692221 : Nat := 1382403401128216406656207

theorem tailTrace_2692221 : CollatzResearch.WordTrace tailWord_2692221 prefixEnd_2692221 1382403401128216406656207 := by
  unfold tailWord_2692221
  simp only [CollatzResearch.WordTrace]
  refine ⟨98193366779550586585780517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65462244519700391057187011 98193366779550586585780517)
  ·
    refine ⟨18411256271165734984833847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98193366779550586585780517 18411256271165734984833847)
    ·
      refine ⟨27616884406748602477250771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18411256271165734984833847 27616884406748602477250771)
      ·
        refine ⟨41425326610122903715876157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27616884406748602477250771 41425326610122903715876157)
        ·
          refine ⟨15534497478796088893453559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41425326610122903715876157 15534497478796088893453559)
          ·
            refine ⟨23301746218194133340180339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15534497478796088893453559 23301746218194133340180339)
            ·
              refine ⟨34952619327291200010270509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23301746218194133340180339 34952619327291200010270509)
              ·
                refine ⟨13107232247734200003851441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34952619327291200010270509 13107232247734200003851441)
                ·
                  refine ⟨9830424185800650002888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13107232247734200003851441 9830424185800650002888581)
                  ·
                    refine ⟨1843204534837621875541609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9830424185800650002888581 1843204534837621875541609)
                    ·
                      refine ⟨1382403401128216406656207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843204534837621875541609 1382403401128216406656207)
                      ·
                        rfl

theorem cell23_2692221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_2692221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692221 prefixEnd_2692221 := by exact prefixLift 2692221
  have htrace : WordTrace (prefixWord ++ tailWord_2692221) baseStart_2692221 baseEnd_2692221 := by
    simpa [prefixWord, tailWord_2692221, baseEnd_2692221] using wordTrace_append hprefix tailTrace_2692221
  have hstable : (prefixWord ++ tailWord_2692221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692221).length < 2 ^ (prefixWord ++ tailWord_2692221).sum := by decide
  have hdescent : baseEnd_2692221 < baseStart_2692221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692224 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_2692224 : Nat := 118140960795 + 2692224 * 2 ^ 59
def prefixEnd_2692224 : Nat := 4983230072969 + 3 ^ 40 * 2692224 * 2
def baseEnd_2692224 : Nat := 1382404941570179894918693

theorem tailTrace_2692224 : CollatzResearch.WordTrace tailWord_2692224 prefixEnd_2692224 1382404941570179894918693 := by
  unfold tailWord_2692224
  simp only [CollatzResearch.WordTrace]
  refine ⟨49096738099269859049069863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65462317465693145398759817 49096738099269859049069863)
  ·
    refine ⟨73645107148904788573604795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49096738099269859049069863 73645107148904788573604795)
    ·
      refine ⟨110467660723357182860407193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73645107148904788573604795 110467660723357182860407193)
      ·
        refine ⟨82850745542517887145305395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110467660723357182860407193 82850745542517887145305395)
        ·
          refine ⟨124276118313776830717958093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82850745542517887145305395 124276118313776830717958093)
          ·
            refine ⟨46603544367666311519234285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124276118313776830717958093 46603544367666311519234285)
            ·
              refine ⟨17476329137874866819712857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46603544367666311519234285 17476329137874866819712857)
              ·
                refine ⟨13107246853406150114784643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17476329137874866819712857 13107246853406150114784643)
                ·
                  refine ⟨19660870280109225172176965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13107246853406150114784643 19660870280109225172176965)
                  ·
                    refine ⟨3686413177520479719783181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19660870280109225172176965 3686413177520479719783181)
                    ·
                      refine ⟨1382404941570179894918693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3686413177520479719783181 1382404941570179894918693)
                      ·
                        rfl

theorem cell23_2692224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_2692224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692224 prefixEnd_2692224 := by exact prefixLift 2692224
  have htrace : WordTrace (prefixWord ++ tailWord_2692224) baseStart_2692224 baseEnd_2692224 := by
    simpa [prefixWord, tailWord_2692224, baseEnd_2692224] using wordTrace_append hprefix tailTrace_2692224
  have hstable : (prefixWord ++ tailWord_2692224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692224).length < 2 ^ (prefixWord ++ tailWord_2692224).sum := by decide
  have hdescent : baseEnd_2692224 < baseStart_2692224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692234 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2692234 : Nat := 118140960795 + 2692234 * 2 ^ 59
def prefixEnd_2692234 : Nat := 4983230072969 + 3 ^ 40 * 2692234 * 2
def baseEnd_2692234 : Nat := 1382410076376724855793647

theorem tailTrace_2692234 : CollatzResearch.WordTrace tailWord_2692234 prefixEnd_2692234 1382410076376724855793647 := by
  unfold tailWord_2692234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548460232125872451500939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65462560619002326537335837 24548460232125872451500939)
  ·
    refine ⟨36822690348188808677251409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24548460232125872451500939 36822690348188808677251409)
    ·
      refine ⟨27617017761141606507938557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36822690348188808677251409 27617017761141606507938557)
      ·
        refine ⟨10356381660428102440476959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27617017761141606507938557 10356381660428102440476959)
        ·
          refine ⟨15534572490642153660715439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10356381660428102440476959 15534572490642153660715439)
          ·
            refine ⟨23301858735963230491073159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15534572490642153660715439 23301858735963230491073159)
            ·
              refine ⟨34952788103944845736609739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23301858735963230491073159 34952788103944845736609739)
              ·
                refine ⟨52429182155917268604914609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34952788103944845736609739 52429182155917268604914609)
                ·
                  refine ⟨39321886616937951453685957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52429182155917268604914609 39321886616937951453685957)
                  ·
                    refine ⟨7372853740675865897566117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39321886616937951453685957 7372853740675865897566117)
                    ·
                      refine ⟨1382410076376724855793647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7372853740675865897566117 1382410076376724855793647)
                      ·
                        rfl

theorem cell23_2692234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2692234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692234 prefixEnd_2692234 := by exact prefixLift 2692234
  have htrace : WordTrace (prefixWord ++ tailWord_2692234) baseStart_2692234 baseEnd_2692234 := by
    simpa [prefixWord, tailWord_2692234, baseEnd_2692234] using wordTrace_append hprefix tailTrace_2692234
  have hstable : (prefixWord ++ tailWord_2692234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692234).length < 2 ^ (prefixWord ++ tailWord_2692234).sum := by decide
  have hdescent : baseEnd_2692234 < baseStart_2692234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692298 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_2692298 : Nat := 118140960795 + 2692298 * 2 ^ 59
def prefixEnd_2692298 : Nat := 4983230072969 + 3 ^ 40 * 2692298 * 2
def baseEnd_2692298 : Nat := 1382442939138612605393353

theorem tailTrace_2692298 : CollatzResearch.WordTrace tailWord_2692298 prefixEnd_2692298 1382442939138612605393353 := by
  unfold tailWord_2692298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24549043800067907184083387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65464116800181085824222365 24549043800067907184083387)
  ·
    refine ⟨36823565700101860776125081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24549043800067907184083387 36823565700101860776125081)
    ·
      refine ⟨27617674275076395582093811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36823565700101860776125081 27617674275076395582093811)
      ·
        refine ⟨41426511412614593373140717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27617674275076395582093811 41426511412614593373140717)
        ·
          refine ⟨15534941779730472514927769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41426511412614593373140717 15534941779730472514927769)
          ·
            refine ⟨11651206334797854386195827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15534941779730472514927769 11651206334797854386195827)
            ·
              refine ⟨17476809502196781579293741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651206334797854386195827 17476809502196781579293741)
              ·
                refine ⟨6553803563323793092235153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17476809502196781579293741 6553803563323793092235153)
                ·
                  refine ⟨4915352672492844819176365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6553803563323793092235153 4915352672492844819176365)
                  ·
                    refine ⟨1843257252184816807191137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4915352672492844819176365 1843257252184816807191137)
                    ·
                      refine ⟨1382442939138612605393353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1843257252184816807191137 1382442939138612605393353)
                      ·
                        rfl

theorem cell23_2692298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_2692298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692298 prefixEnd_2692298 := by exact prefixLift 2692298
  have htrace : WordTrace (prefixWord ++ tailWord_2692298) baseStart_2692298 baseEnd_2692298 := by
    simpa [prefixWord, tailWord_2692298, baseEnd_2692298] using wordTrace_append hprefix tailTrace_2692298
  have hstable : (prefixWord ++ tailWord_2692298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692298).length < 2 ^ (prefixWord ++ tailWord_2692298).sum := by decide
  have hdescent : baseEnd_2692298 < baseStart_2692298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692311 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_2692311 : Nat := 118140960795 + 2692311 * 2 ^ 59
def prefixEnd_2692311 : Nat := 4983230072969 + 3 ^ 40 * 2692311 * 2
def baseEnd_2692311 : Nat := 1382449614387121054530793

theorem tailTrace_2692311 : CollatzResearch.WordTrace tailWord_2692311 prefixEnd_2692311 1382449614387121054530793 := by
  unfold tailWord_2692311
  simp only [CollatzResearch.WordTrace]
  refine ⟨98196649349224531956556787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65464432899483021304371191 98196649349224531956556787)
  ·
    refine ⟨147294974023836797934835181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98196649349224531956556787 147294974023836797934835181)
    ·
      refine ⟨55235615258938799225563193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147294974023836797934835181 55235615258938799225563193)
      ·
        refine ⟨41426711444204099419172395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55235615258938799225563193 41426711444204099419172395)
        ·
          refine ⟨62140067166306149128758593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41426711444204099419172395 62140067166306149128758593)
          ·
            refine ⟨46605050374729611846568945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62140067166306149128758593 46605050374729611846568945)
            ·
              refine ⟨34953787781047208884926709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46605050374729611846568945 34953787781047208884926709)
              ·
                refine ⟨3276917604473175832961879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34953787781047208884926709 3276917604473175832961879)
                ·
                  refine ⟨4915376406709763749442819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276917604473175832961879 4915376406709763749442819)
                  ·
                    refine ⟨7373064610064645624164229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4915376406709763749442819 7373064610064645624164229)
                    ·
                      refine ⟨1382449614387121054530793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7373064610064645624164229 1382449614387121054530793)
                      ·
                        rfl

theorem cell23_2692311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_2692311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2692311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2692311 prefixEnd_2692311 := by exact prefixLift 2692311
  have htrace : WordTrace (prefixWord ++ tailWord_2692311) baseStart_2692311 baseEnd_2692311 := by
    simpa [prefixWord, tailWord_2692311, baseEnd_2692311] using wordTrace_append hprefix tailTrace_2692311
  have hstable : (prefixWord ++ tailWord_2692311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692311).length < 2 ^ (prefixWord ++ tailWord_2692311).sum := by decide
  have hdescent : baseEnd_2692311 < baseStart_2692311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
