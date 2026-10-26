import V185TrunkScan23Chunk1385

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8209443 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 5]
def baseStart_8209443 : Nat := 118140960795 + 8209443 * 2 ^ 59
def prefixEnd_8209443 : Nat := 4983230072969 + 3 ^ 40 * 8209443 * 2
def baseEnd_8209443 : Nat := 468376684965381027800885

theorem tailTrace_8209443 : CollatzResearch.WordTrace tailWord_8209443 prefixEnd_8209443 468376684965381027800885 := by
  unfold tailWord_8209443
  simp only [CollatzResearch.WordTrace]
  refine ⟨299422984797597547085712983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199615323198398364723808655 299422984797597547085712983)
  ·
    refine ⟨449134477196396320628569475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299422984797597547085712983 449134477196396320628569475)
    ·
      refine ⟨673701715794594480942854213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449134477196396320628569475 673701715794594480942854213)
      ·
        refine ⟨126319071711486465176785165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673701715794594480942854213 126319071711486465176785165)
        ·
          refine ⟨47369651891807424441294437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126319071711486465176785165 47369651891807424441294437)
          ·
            refine ⟨8881809729713892082742707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47369651891807424441294437 8881809729713892082742707)
            ·
              refine ⟨13322714594570838124114061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881809729713892082742707 13322714594570838124114061)
              ·
                refine ⟨4996017972964064296542773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322714594570838124114061 4996017972964064296542773)
                ·
                  refine ⟨468376684965381027800885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996017972964064296542773 468376684965381027800885)
                  ·
                    rfl

theorem cell23_8209443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 5].length) (baseStart_8209443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209443 prefixEnd_8209443 := by exact prefixLift 8209443
  have htrace : WordTrace (prefixWord ++ tailWord_8209443) baseStart_8209443 baseEnd_8209443 := by
    simpa [prefixWord, tailWord_8209443, baseEnd_8209443] using wordTrace_append hprefix tailTrace_8209443
  have hstable : (prefixWord ++ tailWord_8209443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209443).length < 2 ^ (prefixWord ++ tailWord_8209443).sum := by decide
  have hdescent : baseEnd_8209443 < baseStart_8209443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209486 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_8209486 : Nat := 118140960795 + 8209486 * 2 ^ 59
def prefixEnd_8209486 : Nat := 4983230072969 + 3 ^ 40 * 8209486 * 2
def baseEnd_8209486 : Nat := 1405137414785524193990089

theorem tailTrace_8209486 : CollatzResearch.WordTrace tailWord_8209486 prefixEnd_8209486 1405137414785524193990089 := by
  unfold tailWord_8209486
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428069142055220678691039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199616368757627843619685541 37428069142055220678691039)
  ·
    refine ⟨56142103713082831018036559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37428069142055220678691039 56142103713082831018036559)
    ·
      refine ⟨84213155569624246527054839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56142103713082831018036559 84213155569624246527054839)
      ·
        refine ⟨126319733354436369790582259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84213155569624246527054839 126319733354436369790582259)
        ·
          refine ⟨189479600031654554685873389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126319733354436369790582259 189479600031654554685873389)
          ·
            refine ⟨71054850011870458007202521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189479600031654554685873389 71054850011870458007202521)
            ·
              refine ⟨53291137508902843505401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71054850011870458007202521 53291137508902843505401891)
              ·
                refine ⟨79936706263354265258102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53291137508902843505401891 79936706263354265258102837)
                ·
                  refine ⟨7494066212189462367947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79936706263354265258102837 7494066212189462367947141)
                  ·
                    refine ⟨1405137414785524193990089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494066212189462367947141 1405137414785524193990089)
                    ·
                      rfl

theorem cell23_8209486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_8209486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209486 prefixEnd_8209486 := by exact prefixLift 8209486
  have htrace : WordTrace (prefixWord ++ tailWord_8209486) baseStart_8209486 baseEnd_8209486 := by
    simpa [prefixWord, tailWord_8209486, baseEnd_8209486] using wordTrace_append hprefix tailTrace_8209486
  have hstable : (prefixWord ++ tailWord_8209486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209486).length < 2 ^ (prefixWord ++ tailWord_8209486).sum := by decide
  have hdescent : baseEnd_8209486 < baseStart_8209486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209489 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_8209489 : Nat := 118140960795 + 8209489 * 2 ^ 59
def prefixEnd_8209489 : Nat := 4983230072969 + 3 ^ 40 * 8209489 * 2
def baseEnd_8209489 : Nat := 4215413784798536070232753

theorem tailTrace_8209489 : CollatzResearch.WordTrace tailWord_8209489 prefixEnd_8209489 4215413784798536070232753 := by
  unfold tailWord_8209489
  simp only [CollatzResearch.WordTrace]
  refine ⟨299424662555430896941887521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199616441703620597961258347 299424662555430896941887521)
  ·
    refine ⟨224568496916573172706415641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299424662555430896941887521 224568496916573172706415641)
    ·
      refine ⟨168426372687429879529811731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224568496916573172706415641 168426372687429879529811731)
      ·
        refine ⟨252639559031144819294717597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168426372687429879529811731 252639559031144819294717597)
        ·
          refine ⟨94739834636679307235519099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252639559031144819294717597 94739834636679307235519099)
          ·
            refine ⟨142109751955018960853278649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94739834636679307235519099 142109751955018960853278649)
            ·
              refine ⟨106582313966264220639958987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142109751955018960853278649 106582313966264220639958987)
              ·
                refine ⟨159873470949396330959938481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106582313966264220639958987 159873470949396330959938481)
                ·
                  refine ⟨119905103212047248219953861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159873470949396330959938481 119905103212047248219953861)
                  ·
                    refine ⟨22482206852258859041241349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119905103212047248219953861 22482206852258859041241349)
                    ·
                      refine ⟨4215413784798536070232753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22482206852258859041241349 4215413784798536070232753)
                      ·
                        rfl

theorem cell23_8209489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_8209489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209489 prefixEnd_8209489 := by exact prefixLift 8209489
  have htrace : WordTrace (prefixWord ++ tailWord_8209489) baseStart_8209489 baseEnd_8209489 := by
    simpa [prefixWord, tailWord_8209489, baseEnd_8209489] using wordTrace_append hprefix tailTrace_8209489
  have hstable : (prefixWord ++ tailWord_8209489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209489).length < 2 ^ (prefixWord ++ tailWord_8209489).sum := by decide
  have hdescent : baseEnd_8209489 < baseStart_8209489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209503 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 1, 4]
def baseStart_8209503 : Nat := 118140960795 + 8209503 * 2 ^ 59
def prefixEnd_8209503 : Nat := 4983230072969 + 3 ^ 40 * 8209503 * 2
def baseEnd_8209503 : Nat := 1405140324509233005152563

theorem tailTrace_8209503 : CollatzResearch.WordTrace tailWord_8209503 prefixEnd_8209503 1405140324509233005152563 := by
  unfold tailWord_8209503
  simp only [CollatzResearch.WordTrace]
  refine ⟨299425173177380177332897163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199616782118253451555264775 299425173177380177332897163)
  ·
    refine ⟨449137759766070265999345745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299425173177380177332897163 449137759766070265999345745)
    ·
      refine ⟨336853319824552699499509309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449137759766070265999345745 336853319824552699499509309)
      ·
        refine ⟨126319994934207262312315991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336853319824552699499509309 126319994934207262312315991)
        ·
          refine ⟨189479992401310893468473987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126319994934207262312315991 189479992401310893468473987)
          ·
            refine ⟨284219988601966340202710981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189479992401310893468473987 284219988601966340202710981)
            ·
              refine ⟨53291247862868688788008309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284219988601966340202710981 53291247862868688788008309)
              ·
                refine ⟨4996054487143939573875779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53291247862868688788008309 4996054487143939573875779)
                ·
                  refine ⟨7494081730715909360813669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996054487143939573875779 7494081730715909360813669)
                  ·
                    refine ⟨1405140324509233005152563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494081730715909360813669 1405140324509233005152563)
                    ·
                      rfl

theorem cell23_8209503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_8209503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209503 prefixEnd_8209503 := by exact prefixLift 8209503
  have htrace : WordTrace (prefixWord ++ tailWord_8209503) baseStart_8209503 baseEnd_8209503 := by
    simpa [prefixWord, tailWord_8209503, baseEnd_8209503] using wordTrace_append hprefix tailTrace_8209503
  have hstable : (prefixWord ++ tailWord_8209503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209503).length < 2 ^ (prefixWord ++ tailWord_8209503).sum := by decide
  have hdescent : baseEnd_8209503 < baseStart_8209503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209516 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 6]
def baseStart_8209516 : Nat := 118140960795 + 8209516 * 2 ^ 59
def prefixEnd_8209516 : Nat := 4983230072969 + 3 ^ 40 * 8209516 * 2
def baseEnd_8209516 : Nat := 468380849864023051621681

theorem tailTrace_8209516 : CollatzResearch.WordTrace tailWord_8209516 prefixEnd_8209516 468380849864023051621681 := by
  unfold tailWord_8209516
  simp only [CollatzResearch.WordTrace]
  refine ⟨149712823663166540276560201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199617098217555387035413601 149712823663166540276560201)
  ·
    refine ⟨112284617747374905207420151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149712823663166540276560201 112284617747374905207420151)
    ·
      refine ⟨168426926621062357811130227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112284617747374905207420151 168426926621062357811130227)
      ·
        refine ⟨252640389931593536716695341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168426926621062357811130227 252640389931593536716695341)
        ·
          refine ⟨94740146224347576268760753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252640389931593536716695341 94740146224347576268760753)
          ·
            refine ⟨71055109668260682201570565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94740146224347576268760753 71055109668260682201570565)
            ·
              refine ⟨13322833062798877912794481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71055109668260682201570565 13322833062798877912794481)
              ·
                refine ⟨9992124797099158434595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13322833062798877912794481 9992124797099158434595861)
                ·
                  refine ⟨468380849864023051621681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9992124797099158434595861 468380849864023051621681)
                  ·
                    rfl

theorem cell23_8209516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_8209516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209516 prefixEnd_8209516 := by exact prefixLift 8209516
  have htrace : WordTrace (prefixWord ++ tailWord_8209516) baseStart_8209516 baseEnd_8209516 := by
    simpa [prefixWord, tailWord_8209516, baseEnd_8209516] using wordTrace_append hprefix tailTrace_8209516
  have hstable : (prefixWord ++ tailWord_8209516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209516).length < 2 ^ (prefixWord ++ tailWord_8209516).sum := by decide
  have hdescent : baseEnd_8209516 < baseStart_8209516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209519 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_8209519 : Nat := 118140960795 + 8209519 * 2 ^ 59
def prefixEnd_8209519 : Nat := 4983230072969 + 3 ^ 40 * 8209519 * 2
def baseEnd_8209519 : Nat := 4215429189218170952857615

theorem tailTrace_8209519 : CollatzResearch.WordTrace tailWord_8209519 prefixEnd_8209519 4215429189218170952857615 := by
  unfold tailWord_8209519
  simp only [CollatzResearch.WordTrace]
  refine ⟨299425756745322212065479611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199617171163548141376986407 299425756745322212065479611)
  ·
    refine ⟨449138635117983318098219417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299425756745322212065479611 449138635117983318098219417)
    ·
      refine ⟨336853976338487488573664563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449138635117983318098219417 336853976338487488573664563)
      ·
        refine ⟨505280964507731232860496845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336853976338487488573664563 505280964507731232860496845)
        ·
          refine ⟨189480361690399212322686317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505280964507731232860496845 189480361690399212322686317)
          ·
            refine ⟨71055135633899704621007369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189480361690399212322686317 71055135633899704621007369)
            ·
              refine ⟨53291351725424778465755527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71055135633899704621007369 53291351725424778465755527)
              ·
                refine ⟨79937027588137167698633291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53291351725424778465755527 79937027588137167698633291)
                ·
                  refine ⟨119905541382205751547949937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79937027588137167698633291 119905541382205751547949937)
                  ·
                    refine ⟨89929156036654313660962453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119905541382205751547949937 89929156036654313660962453)
                    ·
                      refine ⟨4215429189218170952857615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89929156036654313660962453 4215429189218170952857615)
                      ·
                        rfl

theorem cell23_8209519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_8209519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209519 prefixEnd_8209519 := by exact prefixLift 8209519
  have htrace : WordTrace (prefixWord ++ tailWord_8209519) baseStart_8209519 baseEnd_8209519 := by
    simpa [prefixWord, tailWord_8209519, baseEnd_8209519] using wordTrace_append hprefix tailTrace_8209519
  have hstable : (prefixWord ++ tailWord_8209519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209519).length < 2 ^ (prefixWord ++ tailWord_8209519).sum := by decide
  have hdescent : baseEnd_8209519 < baseStart_8209519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209539 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_8209539 : Nat := 118140960795 + 8209539 * 2 ^ 59
def prefixEnd_8209539 : Nat := 4983230072969 + 3 ^ 40 * 8209539 * 2
def baseEnd_8209539 : Nat := 4215439458831260874607523

theorem tailTrace_8209539 : CollatzResearch.WordTrace tailWord_8209539 prefixEnd_8209539 4215439458831260874607523 := by
  unfold tailWord_8209539
  simp only [CollatzResearch.WordTrace]
  refine ⟨299426486205249755481207671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199617657470166503654138447 299426486205249755481207671)
  ·
    refine ⟨449139729307874633221811507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299426486205249755481207671 449139729307874633221811507)
    ·
      refine ⟨673709593961811949832717261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449139729307874633221811507 673709593961811949832717261)
      ·
        refine ⟨252641097735679481187268973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673709593961811949832717261 252641097735679481187268973)
        ·
          refine ⟨94740411650879805445225865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252641097735679481187268973 94740411650879805445225865)
          ·
            refine ⟨71055308738159854083919399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94740411650879805445225865 71055308738159854083919399)
            ·
              refine ⟨106582963107239781125879099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71055308738159854083919399 106582963107239781125879099)
              ·
                refine ⟨159874444660859671688818649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106582963107239781125879099 159874444660859671688818649)
                ·
                  refine ⟨119905833495644753766613987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159874444660859671688818649 119905833495644753766613987)
                  ·
                    refine ⟨179858750243467130649920981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119905833495644753766613987 179858750243467130649920981)
                    ·
                      refine ⟨4215439458831260874607523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179858750243467130649920981 4215439458831260874607523)
                      ·
                        rfl

theorem cell23_8209539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_8209539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209539 prefixEnd_8209539 := by exact prefixLift 8209539
  have htrace : WordTrace (prefixWord ++ tailWord_8209539) baseStart_8209539 baseEnd_8209539 := by
    simpa [prefixWord, tailWord_8209539, baseEnd_8209539] using wordTrace_append hprefix tailTrace_8209539
  have hstable : (prefixWord ++ tailWord_8209539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209539).length < 2 ^ (prefixWord ++ tailWord_8209539).sum := by decide
  have hdescent : baseEnd_8209539 < baseStart_8209539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209546 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_8209546 : Nat := 118140960795 + 8209546 * 2 ^ 59
def prefixEnd_8209546 : Nat := 4983230072969 + 3 ^ 40 * 8209546 * 2
def baseEnd_8209546 : Nat := 1405147684398614115739997

theorem tailTrace_8209546 : CollatzResearch.WordTrace tailWord_8209546 prefixEnd_8209546 1405147684398614115739997 := by
  unfold tailWord_8209546
  simp only [CollatzResearch.WordTrace]
  refine ⟨74856685379056098919178123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199617827677482930451141661 74856685379056098919178123)
  ·
    refine ⟨112285028068584148378767185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74856685379056098919178123 112285028068584148378767185)
    ·
      refine ⟨84213771051438111284075389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112285028068584148378767185 84213771051438111284075389)
      ·
        refine ⟨31580164144289291731528271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84213771051438111284075389 31580164144289291731528271)
        ·
          refine ⟨47370246216433937597292407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31580164144289291731528271 47370246216433937597292407)
          ·
            refine ⟨71055369324650906395938611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47370246216433937597292407 71055369324650906395938611)
            ·
              refine ⟨106583053986976359593907917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71055369324650906395938611 106583053986976359593907917)
              ·
                refine ⟨39968645245116134847715469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106583053986976359593907917 39968645245116134847715469)
                ·
                  refine ⟨14988241966918550567893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39968645245116134847715469 14988241966918550567893301)
                  ·
                    refine ⟨1405147684398614115739997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14988241966918550567893301 1405147684398614115739997)
                    ·
                      rfl

theorem cell23_8209546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_8209546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209546 prefixEnd_8209546 := by exact prefixLift 8209546
  have htrace : WordTrace (prefixWord ++ tailWord_8209546) baseStart_8209546 baseEnd_8209546 := by
    simpa [prefixWord, tailWord_8209546, baseEnd_8209546] using wordTrace_append hprefix tailTrace_8209546
  have hstable : (prefixWord ++ tailWord_8209546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209546).length < 2 ^ (prefixWord ++ tailWord_8209546).sum := by decide
  have hdescent : baseEnd_8209546 < baseStart_8209546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209586 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_8209586 : Nat := 118140960795 + 8209586 * 2 ^ 59
def prefixEnd_8209586 : Nat := 4983230072969 + 3 ^ 40 * 8209586 * 2
def baseEnd_8209586 : Nat := 4215463592422022190719807

theorem tailTrace_8209586 : CollatzResearch.WordTrace tailWord_8209586 prefixEnd_8209586 4215463592422022190719807 := by
  unfold tailWord_8209586
  simp only [CollatzResearch.WordTrace]
  refine ⟨74857050109019870627042153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199618800290719655005445741 74857050109019870627042153)
  ·
    refine ⟨56142787581764902970281615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74857050109019870627042153 56142787581764902970281615)
    ·
      refine ⟨84214181372647354455422423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56142787581764902970281615 84214181372647354455422423)
      ·
        refine ⟨126321272058971031683133635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84214181372647354455422423 126321272058971031683133635)
        ·
          refine ⟨189481908088456547524700453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126321272058971031683133635 189481908088456547524700453)
          ·
            refine ⟨35527857766585602660881335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189481908088456547524700453 35527857766585602660881335)
            ·
              refine ⟨53291786649878403991322003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35527857766585602660881335 53291786649878403991322003)
              ·
                refine ⟨79937679974817605986983005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53291786649878403991322003 79937679974817605986983005)
                ·
                  refine ⟨29976629990556602245118627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79937679974817605986983005 29976629990556602245118627)
                  ·
                    refine ⟨44964944985834903367677941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29976629990556602245118627 44964944985834903367677941)
                    ·
                      refine ⟨4215463592422022190719807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44964944985834903367677941 4215463592422022190719807)
                      ·
                        rfl

theorem cell23_8209586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_8209586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209586 prefixEnd_8209586 := by exact prefixLift 8209586
  have htrace : WordTrace (prefixWord ++ tailWord_8209586) baseStart_8209586 baseEnd_8209586 := by
    simpa [prefixWord, tailWord_8209586, baseEnd_8209586] using wordTrace_append hprefix tailTrace_8209586
  have hstable : (prefixWord ++ tailWord_8209586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209586).length < 2 ^ (prefixWord ++ tailWord_8209586).sum := by decide
  have hdescent : baseEnd_8209586 < baseStart_8209586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209593 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_8209593 : Nat := 118140960795 + 8209593 * 2 ^ 59
def prefixEnd_8209593 : Nat := 4983230072969 + 3 ^ 40 * 8209593 * 2
def baseEnd_8209593 : Nat := 1405155728928867887777425

theorem tailTrace_8209593 : CollatzResearch.WordTrace tailWord_8209593 prefixEnd_8209593 1405155728928867887777425 := by
  unfold tailWord_8209593
  simp only [CollatzResearch.WordTrace]
  refine ⟨299428455747054122703673433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199618970498036081802448955 299428455747054122703673433)
  ·
    refine ⟨224571341810290592027755075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299428455747054122703673433 224571341810290592027755075)
    ·
      refine ⟨336857012715435888041632613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224571341810290592027755075 336857012715435888041632613)
      ·
        refine ⟨63160689884144229007806115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336857012715435888041632613 63160689884144229007806115)
        ·
          refine ⟨94741034826216343511709173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63160689884144229007806115 94741034826216343511709173)
          ·
            refine ⟨8881972014957782204222735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94741034826216343511709173 8881972014957782204222735)
            ·
              refine ⟨13322958022436673306334103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881972014957782204222735 13322958022436673306334103)
              ·
                refine ⟨19984437033655009959501155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13322958022436673306334103 19984437033655009959501155)
                ·
                  refine ⟨29976655550482514939251733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19984437033655009959501155 29976655550482514939251733)
                  ·
                    refine ⟨1405155728928867887777425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29976655550482514939251733 1405155728928867887777425)
                    ·
                      rfl

theorem cell23_8209593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_8209593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209593 prefixEnd_8209593 := by exact prefixLift 8209593
  have htrace : WordTrace (prefixWord ++ tailWord_8209593) baseStart_8209593 baseEnd_8209593 := by
    simpa [prefixWord, tailWord_8209593, baseEnd_8209593] using wordTrace_append hprefix tailTrace_8209593
  have hstable : (prefixWord ++ tailWord_8209593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209593).length < 2 ^ (prefixWord ++ tailWord_8209593).sum := by decide
  have hdescent : baseEnd_8209593 < baseStart_8209593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209600 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_8209600 : Nat := 118140960795 + 8209600 * 2 ^ 59
def prefixEnd_8209600 : Nat := 4983230072969 + 3 ^ 40 * 8209600 * 2
def baseEnd_8209600 : Nat := 4215470781151185135944743

theorem tailTrace_8209600 : CollatzResearch.WordTrace tailWord_8209600 prefixEnd_8209600 4215470781151185135944743 := by
  unfold tailWord_8209600
  simp only [CollatzResearch.WordTrace]
  refine ⟨149714355529014381449589127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199619140705352508599452169 149714355529014381449589127)
  ·
    refine ⟨224571533293521572174383691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149714355529014381449589127 224571533293521572174383691)
    ·
      refine ⟨336857299940282358261575537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224571533293521572174383691 336857299940282358261575537)
      ·
        refine ⟨252642974955211768696181653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336857299940282358261575537 252642974955211768696181653)
        ·
          refine ⟨11842639451025551657633515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252642974955211768696181653 11842639451025551657633515)
          ·
            refine ⟨17763959176538327486450273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842639451025551657633515 17763959176538327486450273)
            ·
              refine ⟨13322969382403745614837705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17763959176538327486450273 13322969382403745614837705)
              ·
                refine ⟨9992227036802809211128279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13322969382403745614837705 9992227036802809211128279)
                ·
                  refine ⟨14988340555204213816692419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992227036802809211128279 14988340555204213816692419)
                  ·
                    refine ⟨22482510832806320725038629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14988340555204213816692419 22482510832806320725038629)
                    ·
                      refine ⟨4215470781151185135944743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22482510832806320725038629 4215470781151185135944743)
                      ·
                        rfl

theorem cell23_8209600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_8209600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209600 prefixEnd_8209600 := by exact prefixLift 8209600
  have htrace : WordTrace (prefixWord ++ tailWord_8209600) baseStart_8209600 baseEnd_8209600 := by
    simpa [prefixWord, tailWord_8209600, baseEnd_8209600] using wordTrace_append hprefix tailTrace_8209600
  have hstable : (prefixWord ++ tailWord_8209600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209600).length < 2 ^ (prefixWord ++ tailWord_8209600).sum := by decide
  have hdescent : baseEnd_8209600 < baseStart_8209600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209713 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 7]
def baseStart_8209713 : Nat := 118140960795 + 8209713 * 2 ^ 59
def prefixEnd_8209713 : Nat := 4983230072969 + 3 ^ 40 * 8209713 * 2
def baseEnd_8209713 : Nat := 468392089385015910425747

theorem tailTrace_8209713 : CollatzResearch.WordTrace tailWord_8209713 prefixEnd_8209713 468392089385015910425747 := by
  unfold tailWord_8209713
  simp only [CollatzResearch.WordTrace]
  refine ⟨299432832506619383198041793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199621888337746255465361195 299432832506619383198041793)
  ·
    refine ⟨224574624379964537398531345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299432832506619383198041793 224574624379964537398531345)
    ·
      refine ⟨168430968284973403048898509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224574624379964537398531345 168430968284973403048898509)
      ·
        refine ⟨63161613106865026143336941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168430968284973403048898509 63161613106865026143336941)
        ·
          refine ⟨23685604915074384803751353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63161613106865026143336941 23685604915074384803751353)
          ·
            refine ⟨17764203686305788602813515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23685604915074384803751353 17764203686305788602813515)
            ·
              refine ⟨26646305529458682904220273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17764203686305788602813515 26646305529458682904220273)
              ·
                refine ⟨19984729147094012178165205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26646305529458682904220273 19984729147094012178165205)
                ·
                  refine ⟨468392089385015910425747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19984729147094012178165205 468392089385015910425747)
                  ·
                    rfl

theorem cell23_8209713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_8209713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209713 prefixEnd_8209713 := by exact prefixLift 8209713
  have htrace : WordTrace (prefixWord ++ tailWord_8209713) baseStart_8209713 baseEnd_8209713 := by
    simpa [prefixWord, tailWord_8209713, baseEnd_8209713] using wordTrace_append hprefix tailTrace_8209713
  have hstable : (prefixWord ++ tailWord_8209713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209713).length < 2 ^ (prefixWord ++ tailWord_8209713).sum := by decide
  have hdescent : baseEnd_8209713 < baseStart_8209713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209741 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_8209741 : Nat := 118140960795 + 8209741 * 2 ^ 59
def prefixEnd_8209741 : Nat := 4983230072969 + 3 ^ 40 * 8209741 * 2
def baseEnd_8209741 : Nat := 4215543181923469084281595

theorem tailTrace_8209741 : CollatzResearch.WordTrace tailWord_8209741 prefixEnd_8209741 4215543181923469084281595 := by
  unfold tailWord_8209741
  simp only [CollatzResearch.WordTrace]
  refine ⟨299433853750517943980061077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199622569167011962653374051 299433853750517943980061077)
  ·
    refine ⟨14035961894555528624065363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299433853750517943980061077 14035961894555528624065363)
    ·
      refine ⟨21053942841833292936098045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035961894555528624065363 21053942841833292936098045)
      ·
        refine ⟨7895228565687484851036767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21053942841833292936098045 7895228565687484851036767)
        ·
          refine ⟨11842842848531227276555151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895228565687484851036767 11842842848531227276555151)
          ·
            refine ⟨17764264272796840914832727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842842848531227276555151 17764264272796840914832727)
            ·
              refine ⟨26646396409195261372249091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17764264272796840914832727 26646396409195261372249091)
              ·
                refine ⟨39969594613792892058373637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26646396409195261372249091 39969594613792892058373637)
                ·
                  refine ⟨7494298990086167260945057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39969594613792892058373637 7494298990086167260945057)
                  ·
                    refine ⟨5620724242564625445708793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494298990086167260945057 5620724242564625445708793)
                    ·
                      refine ⟨4215543181923469084281595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620724242564625445708793 4215543181923469084281595)
                      ·
                        rfl

theorem cell23_8209741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_8209741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209741 prefixEnd_8209741 := by exact prefixLift 8209741
  have htrace : WordTrace (prefixWord ++ tailWord_8209741) baseStart_8209741 baseEnd_8209741 := by
    simpa [prefixWord, tailWord_8209741, baseEnd_8209741] using wordTrace_append hprefix tailTrace_8209741
  have hstable : (prefixWord ++ tailWord_8209741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209741).length < 2 ^ (prefixWord ++ tailWord_8209741).sum := by decide
  have hdescent : baseEnd_8209741 < baseStart_8209741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209763 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_8209763 : Nat := 118140960795 + 8209763 * 2 ^ 59
def prefixEnd_8209763 : Nat := 4983230072969 + 3 ^ 40 * 8209763 * 2
def baseEnd_8209763 : Nat := 4215554478497867998206493

theorem tailTrace_8209763 : CollatzResearch.WordTrace tailWord_8209763 prefixEnd_8209763 4215554478497867998206493 := by
  unfold tailWord_8209763
  simp only [CollatzResearch.WordTrace]
  refine ⟨299434656156438241737361943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199623104104292161158241295 299434656156438241737361943)
  ·
    refine ⟨449151984234657362606042915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299434656156438241737361943 449151984234657362606042915)
    ·
      refine ⟨673727976351986043909064373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449151984234657362606042915 673727976351986043909064373)
      ·
        refine ⟨63161997782998691616474785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 673727976351986043909064373 63161997782998691616474785)
        ·
          refine ⟨47371498337249018712356089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63161997782998691616474785 47371498337249018712356089)
          ·
            refine ⟨35528623752936764034267067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47371498337249018712356089 35528623752936764034267067)
            ·
              refine ⟨53292935629405146051400601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35528623752936764034267067 53292935629405146051400601)
              ·
                refine ⟨39969701722053859538550451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53292935629405146051400601 39969701722053859538550451)
                ·
                  refine ⟨59954552583080789307825677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39969701722053859538550451 59954552583080789307825677)
                  ·
                    refine ⟨22482957218655295990434629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59954552583080789307825677 22482957218655295990434629)
                    ·
                      refine ⟨4215554478497867998206493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22482957218655295990434629 4215554478497867998206493)
                      ·
                        rfl

theorem cell23_8209763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_8209763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209763 prefixEnd_8209763 := by exact prefixLift 8209763
  have htrace : WordTrace (prefixWord ++ tailWord_8209763) baseStart_8209763 baseEnd_8209763 := by
    simpa [prefixWord, tailWord_8209763, baseEnd_8209763] using wordTrace_append hprefix tailTrace_8209763
  have hstable : (prefixWord ++ tailWord_8209763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209763).length < 2 ^ (prefixWord ++ tailWord_8209763).sum := by decide
  have hdescent : baseEnd_8209763 < baseStart_8209763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209783 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_8209783 : Nat := 118140960795 + 8209783 * 2 ^ 59
def prefixEnd_8209783 : Nat := 4983230072969 + 3 ^ 40 * 8209783 * 2
def baseEnd_8209783 : Nat := 4215564748110957919956401

theorem tailTrace_8209783 : CollatzResearch.WordTrace tailWord_8209783 prefixEnd_8209783 4215564748110957919956401 := by
  unfold tailWord_8209783
  simp only [CollatzResearch.WordTrace]
  refine ⟨299435385616365785153090003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199623590410910523435393335 299435385616365785153090003)
  ·
    refine ⟨449153078424548677729635005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299435385616365785153090003 449153078424548677729635005)
    ·
      refine ⟨168432404409205754148613127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449153078424548677729635005 168432404409205754148613127)
      ·
        refine ⟨252648606613808631222919691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168432404409205754148613127 252648606613808631222919691)
        ·
          refine ⟨378972909920712946834379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252648606613808631222919691 378972909920712946834379537)
          ·
            refine ⟨284229682440534710125784653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378972909920712946834379537 284229682440534710125784653)
            ·
              refine ⟨106586130915200516297169245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284229682440534710125784653 106586130915200516297169245)
              ·
                refine ⟨39969799093200193611438467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106586130915200516297169245 39969799093200193611438467)
                ·
                  refine ⟨59954698639800290417157701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39969799093200193611438467 59954698639800290417157701)
                  ·
                    refine ⟨11241505994962554453217069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59954698639800290417157701 11241505994962554453217069)
                    ·
                      refine ⟨4215564748110957919956401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11241505994962554453217069 4215564748110957919956401)
                      ·
                        rfl

theorem cell23_8209783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_8209783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209783 prefixEnd_8209783 := by exact prefixLift 8209783
  have htrace : WordTrace (prefixWord ++ tailWord_8209783) baseStart_8209783 baseEnd_8209783 := by
    simpa [prefixWord, tailWord_8209783, baseEnd_8209783] using wordTrace_append hprefix tailTrace_8209783
  have hstable : (prefixWord ++ tailWord_8209783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209783).length < 2 ^ (prefixWord ++ tailWord_8209783).sum := by decide
  have hdescent : baseEnd_8209783 < baseStart_8209783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209800 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_8209800 : Nat := 118140960795 + 8209800 * 2 ^ 59
def prefixEnd_8209800 : Nat := 4983230072969 + 3 ^ 40 * 8209800 * 2
def baseEnd_8209800 : Nat := 4215573477282084353443823

theorem tailTrace_8209800 : CollatzResearch.WordTrace tailWord_8209800 prefixEnd_8209800 4215573477282084353443823 := by
  unfold tailWord_8209800
  simp only [CollatzResearch.WordTrace]
  refine ⟨149718002828652098528229427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199624003771536131370972569 149718002828652098528229427)
  ·
    refine ⟨224577004242978147792344141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149718002828652098528229427 224577004242978147792344141)
    ·
      refine ⟨84216376591116805422129053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224577004242978147792344141 84216376591116805422129053)
      ·
        refine ⟨31581141221668802033298395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84216376591116805422129053 31581141221668802033298395)
        ·
          refine ⟨47371711832503203049947593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31581141221668802033298395 47371711832503203049947593)
          ·
            refine ⟨35528783874377402287460695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47371711832503203049947593 35528783874377402287460695)
            ·
              refine ⟨53293175811566103431191043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35528783874377402287460695 53293175811566103431191043)
              ·
                refine ⟨79939763717349155146786565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53293175811566103431191043 79939763717349155146786565)
                ·
                  refine ⟨14988705697002966590022481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79939763717349155146786565 14988705697002966590022481)
                  ·
                    refine ⟨11241529272752224942516861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14988705697002966590022481 11241529272752224942516861)
                    ·
                      refine ⟨4215573477282084353443823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11241529272752224942516861 4215573477282084353443823)
                      ·
                        rfl

theorem cell23_8209800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_8209800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209800 prefixEnd_8209800 := by exact prefixLift 8209800
  have htrace : WordTrace (prefixWord ++ tailWord_8209800) baseStart_8209800 baseEnd_8209800 := by
    simpa [prefixWord, tailWord_8209800, baseEnd_8209800] using wordTrace_append hprefix tailTrace_8209800
  have hstable : (prefixWord ++ tailWord_8209800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209800).length < 2 ^ (prefixWord ++ tailWord_8209800).sum := by decide
  have hdescent : baseEnd_8209800 < baseStart_8209800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209803 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 6]
def baseStart_8209803 : Nat := 118140960795 + 8209803 * 2 ^ 59
def prefixEnd_8209803 : Nat := 4983230072969 + 3 ^ 40 * 8209803 * 2
def baseEnd_8209803 : Nat := 468397224191560871300701

theorem tailTrace_8209803 : CollatzResearch.WordTrace tailWord_8209803 prefixEnd_8209803 468397224191560871300701 := by
  unfold tailWord_8209803
  simp only [CollatzResearch.WordTrace]
  refine ⟨299436115076293328568818063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199624076717528885712545375 299436115076293328568818063)
  ·
    refine ⟨449154172614439992853227095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299436115076293328568818063 449154172614439992853227095)
    ·
      refine ⟨673731258921659989279840643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449154172614439992853227095 673731258921659989279840643)
      ·
        refine ⟨1010596888382489983919760965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673731258921659989279840643 1010596888382489983919760965)
        ·
          refine ⟨189486916571716871984955181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1010596888382489983919760965 189486916571716871984955181)
          ·
            refine ⟨71057593714393826994358193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189486916571716871984955181 71057593714393826994358193)
            ·
              refine ⟨53293195285795370245768645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71057593714393826994358193 53293195285795370245768645)
              ·
                refine ⟨9992474116086631921081621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53293195285795370245768645 9992474116086631921081621)
                ·
                  refine ⟨468397224191560871300701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9992474116086631921081621 468397224191560871300701)
                  ·
                    rfl

theorem cell23_8209803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 6].length) (baseStart_8209803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209803 prefixEnd_8209803 := by exact prefixLift 8209803
  have htrace : WordTrace (prefixWord ++ tailWord_8209803) baseStart_8209803 baseEnd_8209803 := by
    simpa [prefixWord, tailWord_8209803, baseEnd_8209803] using wordTrace_append hprefix tailTrace_8209803
  have hstable : (prefixWord ++ tailWord_8209803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209803).length < 2 ^ (prefixWord ++ tailWord_8209803).sum := by decide
  have hdescent : baseEnd_8209803 < baseStart_8209803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209863 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 6]
def baseStart_8209863 : Nat := 118140960795 + 8209863 * 2 ^ 59
def prefixEnd_8209863 : Nat := 4983230072969 + 3 ^ 40 * 8209863 * 2
def baseEnd_8209863 : Nat := 1405201942187772535652011

theorem tailTrace_8209863 : CollatzResearch.WordTrace tailWord_8209863 prefixEnd_8209863 1405201942187772535652011 := by
  unfold tailWord_8209863
  simp only [CollatzResearch.WordTrace]
  refine ⟨299438303456075958816002243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199625535637383972544001495 299438303456075958816002243)
  ·
    refine ⟨449157455184113938224003365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299438303456075958816002243 449157455184113938224003365)
    ·
      refine ⟨84217022847021363417000631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449157455184113938224003365 84217022847021363417000631)
      ·
        refine ⟨126325534270532045125500947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84217022847021363417000631 126325534270532045125500947)
        ·
          refine ⟨189488301405798067688251421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126325534270532045125500947 189488301405798067688251421)
          ·
            refine ⟨71058113027174275383094283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189488301405798067688251421 71058113027174275383094283)
            ·
              refine ⟨106587169540761413074641425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71058113027174275383094283 106587169540761413074641425)
              ·
                refine ⟨79940377155571059805981069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106587169540761413074641425 79940377155571059805981069)
                ·
                  refine ⟨29977641433339147427242901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79940377155571059805981069 29977641433339147427242901)
                  ·
                    refine ⟨1405201942187772535652011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29977641433339147427242901 1405201942187772535652011)
                    ·
                      rfl

theorem cell23_8209863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_8209863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209863 prefixEnd_8209863 := by exact prefixLift 8209863
  have htrace : WordTrace (prefixWord ++ tailWord_8209863) baseStart_8209863 baseEnd_8209863 := by
    simpa [prefixWord, tailWord_8209863, baseEnd_8209863] using wordTrace_append hprefix tailTrace_8209863
  have hstable : (prefixWord ++ tailWord_8209863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209863).length < 2 ^ (prefixWord ++ tailWord_8209863).sum := by decide
  have hdescent : baseEnd_8209863 < baseStart_8209863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209864 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_8209864 : Nat := 118140960795 + 8209864 * 2 ^ 59
def prefixEnd_8209864 : Nat := 4983230072969 + 3 ^ 40 * 8209864 * 2
def baseEnd_8209864 : Nat := 4215606340043972103043529

theorem tailTrace_8209864 : CollatzResearch.WordTrace tailWord_8209864 prefixEnd_8209864 4215606340043972103043529 := by
  unfold tailWord_8209864
  simp only [CollatzResearch.WordTrace]
  refine ⟨149719169964536167993394323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199625559952714890657859097 149719169964536167993394323)
  ·
    refine ⟨224578754946804251990091485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149719169964536167993394323 224578754946804251990091485)
    ·
      refine ⟨84217033105051594496284307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224578754946804251990091485 84217033105051594496284307)
      ·
        refine ⟨126325549657577391744426461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84217033105051594496284307 126325549657577391744426461)
        ·
          refine ⟨47372081121591521904159923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126325549657577391744426461 47372081121591521904159923)
          ·
            refine ⟨71058121682387282856239885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47372081121591521904159923 71058121682387282856239885)
            ·
              refine ⟨26646795630895231071089957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71058121682387282856239885 26646795630895231071089957)
              ·
                refine ⟨4996274180792855825829367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26646795630895231071089957 4996274180792855825829367)
                ·
                  refine ⟨7494411271189283738744051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996274180792855825829367 7494411271189283738744051)
                  ·
                    refine ⟨11241616906783925608116077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494411271189283738744051 11241616906783925608116077)
                    ·
                      refine ⟨4215606340043972103043529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11241616906783925608116077 4215606340043972103043529)
                      ·
                        rfl

theorem cell23_8209864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_8209864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209864 prefixEnd_8209864 := by exact prefixLift 8209864
  have htrace : WordTrace (prefixWord ++ tailWord_8209864) baseStart_8209864 baseEnd_8209864 := by
    simpa [prefixWord, tailWord_8209864, baseEnd_8209864] using wordTrace_append hprefix tailTrace_8209864
  have hstable : (prefixWord ++ tailWord_8209864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209864).length < 2 ^ (prefixWord ++ tailWord_8209864).sum := by decide
  have hdescent : baseEnd_8209864 < baseStart_8209864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209870 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_8209870 : Nat := 118140960795 + 8209870 * 2 ^ 59
def prefixEnd_8209870 : Nat := 4983230072969 + 3 ^ 40 * 8209870 * 2
def baseEnd_8209870 : Nat := 4215609420927899079568501

theorem tailTrace_8209870 : CollatzResearch.WordTrace tailWord_8209870 prefixEnd_8209870 4215609420927899079568501 := by
  unfold tailWord_8209870
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429819845881324876438383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199625705844700399341004709 37429819845881324876438383)
  ·
    refine ⟨56144729768821987314657575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37429819845881324876438383 56144729768821987314657575)
    ·
      refine ⟨84217094653232980971986363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56144729768821987314657575 84217094653232980971986363)
      ·
        refine ⟨126325641979849471457979545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84217094653232980971986363 126325641979849471457979545)
        ·
          refine ⟨94744231484887103593484659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126325641979849471457979545 94744231484887103593484659)
          ·
            refine ⟨142116347227330655390226989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94744231484887103593484659 142116347227330655390226989)
            ·
              refine ⟨53293630210248995771335121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142116347227330655390226989 53293630210248995771335121)
              ·
                refine ⟨39970222657686746828501341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53293630210248995771335121 39970222657686746828501341)
                ·
                  refine ⟨14988833496632530060688003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39970222657686746828501341 14988833496632530060688003)
                  ·
                    refine ⟨22483250244948795091032005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14988833496632530060688003 22483250244948795091032005)
                    ·
                      refine ⟨4215609420927899079568501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22483250244948795091032005 4215609420927899079568501)
                      ·
                        rfl

theorem cell23_8209870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_8209870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209870 prefixEnd_8209870 := by exact prefixLift 8209870
  have htrace : WordTrace (prefixWord ++ tailWord_8209870) baseStart_8209870 baseEnd_8209870 := by
    simpa [prefixWord, tailWord_8209870, baseEnd_8209870] using wordTrace_append hprefix tailTrace_8209870
  have hstable : (prefixWord ++ tailWord_8209870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209870).length < 2 ^ (prefixWord ++ tailWord_8209870).sum := by decide
  have hdescent : baseEnd_8209870 < baseStart_8209870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209901 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_8209901 : Nat := 118140960795 + 8209901 * 2 ^ 59
def prefixEnd_8209901 : Nat := 4983230072969 + 3 ^ 40 * 8209901 * 2
def baseEnd_8209901 : Nat := 1405208446276062819426953

theorem tailTrace_8209901 : CollatzResearch.WordTrace tailWord_8209901 prefixEnd_8209901 1405208446276062819426953 := by
  unfold tailWord_8209901
  simp only [CollatzResearch.WordTrace]
  refine ⟨299439689429938291305885557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199626459619958860870590371 299439689429938291305885557)
  ·
    refine ⟨28072470884056714809926771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299439689429938291305885557 28072470884056714809926771)
    ·
      refine ⟨42108706326085072214890157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072470884056714809926771 42108706326085072214890157)
      ·
        refine ⟨15790764872281902080583809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42108706326085072214890157 15790764872281902080583809)
        ·
          refine ⟨11843073654211426560437857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15790764872281902080583809 11843073654211426560437857)
          ·
            refine ⟨8882305240658569920328393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843073654211426560437857 8882305240658569920328393)
            ·
              refine ⟨6661728930493927440246295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882305240658569920328393 6661728930493927440246295)
              ·
                refine ⟨9992593395740891160369443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661728930493927440246295 9992593395740891160369443)
                ·
                  refine ⟨14988890093611336740554165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992593395740891160369443 14988890093611336740554165)
                  ·
                    refine ⟨1405208446276062819426953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14988890093611336740554165 1405208446276062819426953)
                    ·
                      rfl

theorem cell23_8209901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_8209901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209901 prefixEnd_8209901 := by exact prefixLift 8209901
  have htrace : WordTrace (prefixWord ++ tailWord_8209901) baseStart_8209901 baseEnd_8209901 := by
    simpa [prefixWord, tailWord_8209901, baseEnd_8209901] using wordTrace_append hprefix tailTrace_8209901
  have hstable : (prefixWord ++ tailWord_8209901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209901).length < 2 ^ (prefixWord ++ tailWord_8209901).sum := by decide
  have hdescent : baseEnd_8209901 < baseStart_8209901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209904 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4]
def baseStart_8209904 : Nat := 118140960795 + 8209904 * 2 ^ 59
def prefixEnd_8209904 : Nat := 4983230072969 + 3 ^ 40 * 8209904 * 2
def baseEnd_8209904 : Nat := 4215626879270151946543345

theorem tailTrace_8209904 : CollatzResearch.WordTrace tailWord_8209904 prefixEnd_8209904 4215626879270151946543345 := by
  unfold tailWord_8209904
  simp only [CollatzResearch.WordTrace]
  refine ⟨149719899424463711409122383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199626532565951615212163177 149719899424463711409122383)
  ·
    refine ⟨224579849136695567113683575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149719899424463711409122383 224579849136695567113683575)
    ·
      refine ⟨336869773705043350670525363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224579849136695567113683575 336869773705043350670525363)
      ·
        refine ⟨505304660557565026005788045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336869773705043350670525363 505304660557565026005788045)
        ·
          refine ⟨189489247709086884752170517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505304660557565026005788045 189489247709086884752170517)
          ·
            refine ⟨8882308486363447722757993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189489247709086884752170517 8882308486363447722757993)
            ·
              refine ⟨6661731364772585792068495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882308486363447722757993 6661731364772585792068495)
              ·
                refine ⟨9992597047158878688102743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661731364772585792068495 9992597047158878688102743)
                ·
                  refine ⟨14988895570738318032154115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992597047158878688102743 14988895570738318032154115)
                  ·
                    refine ⟨22483343356107477048231173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14988895570738318032154115 22483343356107477048231173)
                    ·
                      refine ⟨4215626879270151946543345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22483343356107477048231173 4215626879270151946543345)
                      ·
                        rfl

theorem cell23_8209904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 1, 4].length) (baseStart_8209904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209904 prefixEnd_8209904 := by exact prefixLift 8209904
  have htrace : WordTrace (prefixWord ++ tailWord_8209904) baseStart_8209904 baseEnd_8209904 := by
    simpa [prefixWord, tailWord_8209904, baseEnd_8209904] using wordTrace_append hprefix tailTrace_8209904
  have hstable : (prefixWord ++ tailWord_8209904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209904).length < 2 ^ (prefixWord ++ tailWord_8209904).sum := by decide
  have hdescent : baseEnd_8209904 < baseStart_8209904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209910 : List Nat := [5, 1, 1, 1, 2, 3, 10]
def baseStart_8209910 : Nat := 118140960795 + 8209910 * 2 ^ 59
def prefixEnd_8209910 : Nat := 4983230072969 + 3 ^ 40 * 8209910 * 2
def baseEnd_8209910 : Nat := 52044814322889863247757

theorem tailTrace_8209910 : CollatzResearch.WordTrace tailWord_8209910 prefixEnd_8209910 52044814322889863247757 := by
  unfold tailWord_8209910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715001105431605365185199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199626678457937123895308789 18715001105431605365185199)
  ·
    refine ⟨28072501658147408047777799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18715001105431605365185199 28072501658147408047777799)
    ·
      refine ⟨42108752487221112071666699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072501658147408047777799 42108752487221112071666699)
      ·
        refine ⟨63163128730831668107500049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108752487221112071666699 63163128730831668107500049)
        ·
          refine ⟨47372346548123751080625037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63163128730831668107500049 47372346548123751080625037)
          ·
            refine ⟨17764629955546406655234389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47372346548123751080625037 17764629955546406655234389)
            ·
              refine ⟨52044814322889863247757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17764629955546406655234389 52044814322889863247757)
              ·
                rfl

theorem cell23_8209910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 10].length) (baseStart_8209910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209910 prefixEnd_8209910 := by exact prefixLift 8209910
  have htrace : WordTrace (prefixWord ++ tailWord_8209910) baseStart_8209910 baseEnd_8209910 := by
    simpa [prefixWord, tailWord_8209910, baseEnd_8209910] using wordTrace_append hprefix tailTrace_8209910
  have hstable : (prefixWord ++ tailWord_8209910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209910).length < 2 ^ (prefixWord ++ tailWord_8209910).sum := by decide
  have hdescent : baseEnd_8209910 < baseStart_8209910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209913 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_8209913 : Nat := 118140960795 + 8209913 * 2 ^ 59
def prefixEnd_8209913 : Nat := 4983230072969 + 3 ^ 40 * 8209913 * 2
def baseEnd_8209913 : Nat := 4215631500596042411330803

theorem tailTrace_8209913 : CollatzResearch.WordTrace tailWord_8209913 prefixEnd_8209913 4215631500596042411330803 := by
  unfold tailWord_8209913
  simp only [CollatzResearch.WordTrace]
  refine ⟨299440127105894817355322393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199626751403929878236881595 299440127105894817355322393)
  ·
    refine ⟨224580095329421113016491795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299440127105894817355322393 224580095329421113016491795)
    ·
      refine ⟨336870142994131669524737693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224580095329421113016491795 336870142994131669524737693)
      ·
        refine ⟨126326303622799376071776635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336870142994131669524737693 126326303622799376071776635)
        ·
          refine ⟨189489455434199064107664953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126326303622799376071776635 189489455434199064107664953)
          ·
            refine ⟨142117091575649298080748715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189489455434199064107664953 142117091575649298080748715)
            ·
              refine ⟨213175637363473947121123073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142117091575649298080748715 213175637363473947121123073)
              ·
                refine ⟨159881728022605460340842305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213175637363473947121123073 159881728022605460340842305)
                ·
                  refine ⟨119911296016954095255631729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159881728022605460340842305 119911296016954095255631729)
                  ·
                    refine ⟨89933472012715571441723797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119911296016954095255631729 89933472012715571441723797)
                    ·
                      refine ⟨4215631500596042411330803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89933472012715571441723797 4215631500596042411330803)
                      ·
                        rfl

theorem cell23_8209913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_8209913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209913 prefixEnd_8209913 := by exact prefixLift 8209913
  have htrace : WordTrace (prefixWord ++ tailWord_8209913) baseStart_8209913 baseEnd_8209913 := by
    simpa [prefixWord, tailWord_8209913, baseEnd_8209913] using wordTrace_append hprefix tailTrace_8209913
  have hstable : (prefixWord ++ tailWord_8209913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209913).length < 2 ^ (prefixWord ++ tailWord_8209913).sum := by decide
  have hdescent : baseEnd_8209913 < baseStart_8209913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209921 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_8209921 : Nat := 118140960795 + 8209921 * 2 ^ 59
def prefixEnd_8209921 : Nat := 4983230072969 + 3 ^ 40 * 8209921 * 2
def baseEnd_8209921 : Nat := 4215635608441278380030767

theorem tailTrace_8209921 : CollatzResearch.WordTrace tailWord_8209921 prefixEnd_8209921 4215635608441278380030767 := by
  unfold tailWord_8209921
  simp only [CollatzResearch.WordTrace]
  refine ⟨299440418889865834721613617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199626945926577223147742411 299440418889865834721613617)
  ·
    refine ⟨224580314167399376041210213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299440418889865834721613617 224580314167399376041210213)
    ·
      refine ⟨42108808906387383007726915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224580314167399376041210213 42108808906387383007726915)
      ·
        refine ⟨63163213359581074511590373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108808906387383007726915 63163213359581074511590373)
        ·
          refine ⟨11843102504921451470923195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63163213359581074511590373 11843102504921451470923195)
          ·
            refine ⟨17764653757382177206384793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843102504921451470923195 17764653757382177206384793)
            ·
              refine ⟨13323490318036632904788595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17764653757382177206384793 13323490318036632904788595)
              ·
                refine ⟨19985235477054949357182893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323490318036632904788595 19985235477054949357182893)
                ·
                  refine ⟨7494463303895606008943585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19985235477054949357182893 7494463303895606008943585)
                  ·
                    refine ⟨5620847477921704506707689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494463303895606008943585 5620847477921704506707689)
                    ·
                      refine ⟨4215635608441278380030767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620847477921704506707689 4215635608441278380030767)
                      ·
                        rfl

theorem cell23_8209921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_8209921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209921 prefixEnd_8209921 := by exact prefixLift 8209921
  have htrace : WordTrace (prefixWord ++ tailWord_8209921) baseStart_8209921 baseEnd_8209921 := by
    simpa [prefixWord, tailWord_8209921, baseEnd_8209921] using wordTrace_append hprefix tailTrace_8209921
  have hstable : (prefixWord ++ tailWord_8209921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209921).length < 2 ^ (prefixWord ++ tailWord_8209921).sum := by decide
  have hdescent : baseEnd_8209921 < baseStart_8209921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209923 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 7]
def baseStart_8209923 : Nat := 118140960795 + 8209923 * 2 ^ 59
def prefixEnd_8209923 : Nat := 4983230072969 + 3 ^ 40 * 8209923 * 2
def baseEnd_8209923 : Nat := 1405212211800862457401919

theorem tailTrace_8209923 : CollatzResearch.WordTrace tailWord_8209923 prefixEnd_8209923 1405212211800862457401919 := by
  unfold tailWord_8209923
  simp only [CollatzResearch.WordTrace]
  refine ⟨299440491835858589063186423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199626994557239059375457615 299440491835858589063186423)
  ·
    refine ⟨449160737753787883594779635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299440491835858589063186423 449160737753787883594779635)
    ·
      refine ⟨673741106630681825392169453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449160737753787883594779635 673741106630681825392169453)
      ·
        refine ⟨252652914986505684522063545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673741106630681825392169453 252652914986505684522063545)
        ·
          refine ⟨189489686239879263391547659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252652914986505684522063545 189489686239879263391547659)
          ·
            refine ⟨284234529359818895087321489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189489686239879263391547659 284234529359818895087321489)
            ·
              refine ⟨213175897019864171315491117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284234529359818895087321489 213175897019864171315491117)
              ·
                refine ⟨79940961382449064243309169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213175897019864171315491117 79940961382449064243309169)
                ·
                  refine ⟨59955721036836798182481877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79940961382449064243309169 59955721036836798182481877)
                  ·
                    refine ⟨1405212211800862457401919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59955721036836798182481877 1405212211800862457401919)
                    ·
                      rfl

theorem cell23_8209923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_8209923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209923 prefixEnd_8209923 := by exact prefixLift 8209923
  have htrace : WordTrace (prefixWord ++ tailWord_8209923) baseStart_8209923 baseEnd_8209923 := by
    simpa [prefixWord, tailWord_8209923, baseEnd_8209923] using wordTrace_append hprefix tailTrace_8209923
  have hstable : (prefixWord ++ tailWord_8209923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209923).length < 2 ^ (prefixWord ++ tailWord_8209923).sum := by decide
  have hdescent : baseEnd_8209923 < baseStart_8209923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209934 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_8209934 : Nat := 118140960795 + 8209934 * 2 ^ 59
def prefixEnd_8209934 : Nat := 4983230072969 + 3 ^ 40 * 8209934 * 2
def baseEnd_8209934 : Nat := 4215642283689786829168207

theorem tailTrace_8209934 : CollatzResearch.WordTrace tailWord_8209934 prefixEnd_8209934 4215642283689786829168207 := by
  unfold tailWord_8209934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37430111629852342242729607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199627262025879158627891237 37430111629852342242729607)
  ·
    refine ⟨56145167444778513364094411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37430111629852342242729607 56145167444778513364094411)
    ·
      refine ⟨84217751167167770046141617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56145167444778513364094411 84217751167167770046141617)
      ·
        refine ⟨63163313375375827534606213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84217751167167770046141617 63163313375375827534606213)
        ·
          refine ⟨11843121257882967662738665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63163313375375827534606213 11843121257882967662738665)
          ·
            refine ⟨8882340943412225747053999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843121257882967662738665 8882340943412225747053999)
            ·
              refine ⟨13323511415118338620580999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882340943412225747053999 13323511415118338620580999)
              ·
                refine ⟨19985267122677507930871499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323511415118338620580999 19985267122677507930871499)
                ·
                  refine ⟨29977900684016261896307249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19985267122677507930871499 29977900684016261896307249)
                  ·
                    refine ⟨22483425513012196422230437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29977900684016261896307249 22483425513012196422230437)
                    ·
                      refine ⟨4215642283689786829168207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22483425513012196422230437 4215642283689786829168207)
                      ·
                        rfl

theorem cell23_8209934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_8209934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209934 prefixEnd_8209934 := by exact prefixLift 8209934
  have htrace : WordTrace (prefixWord ++ tailWord_8209934) baseStart_8209934 baseEnd_8209934 := by
    simpa [prefixWord, tailWord_8209934, baseEnd_8209934] using wordTrace_append hprefix tailTrace_8209934
  have hstable : (prefixWord ++ tailWord_8209934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209934).length < 2 ^ (prefixWord ++ tailWord_8209934).sum := by decide
  have hdescent : baseEnd_8209934 < baseStart_8209934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209944 : List Nat := [2, 1, 2, 3, 5, 1, 2, 7]
def baseStart_8209944 : Nat := 118140960795 + 8209944 * 2 ^ 59
def prefixEnd_8209944 : Nat := 4983230072969 + 3 ^ 40 * 8209944 * 2
def baseEnd_8209944 : Nat := 156135089573938214446043

theorem tailTrace_8209944 : CollatzResearch.WordTrace tailWord_8209944 prefixEnd_8209944 156135089573938214446043 := by
  unfold tailWord_8209944
  simp only [CollatzResearch.WordTrace]
  refine ⟨149720628884391254824850443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199627505179188339766467257 149720628884391254824850443)
  ·
    refine ⟨224580943326586882237275665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149720628884391254824850443 224580943326586882237275665)
    ·
      refine ⟨168435707494940161677956749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224580943326586882237275665 168435707494940161677956749)
      ·
        refine ⟨63163390310602560629233781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168435707494940161677956749 63163390310602560629233781)
        ·
          refine ⟨5921567841618990058990667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63163390310602560629233781 5921567841618990058990667)
          ·
            refine ⟨8882351762428485088486001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921567841618990058990667 8882351762428485088486001)
            ·
              refine ⟨6661763821821363816364501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882351762428485088486001 6661763821821363816364501)
              ·
                refine ⟨156135089573938214446043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6661763821821363816364501 156135089573938214446043)
                ·
                  rfl

theorem cell23_8209944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 7].length) (baseStart_8209944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209944 prefixEnd_8209944 := by exact prefixLift 8209944
  have htrace : WordTrace (prefixWord ++ tailWord_8209944) baseStart_8209944 baseEnd_8209944 := by
    simpa [prefixWord, tailWord_8209944, baseEnd_8209944] using wordTrace_append hprefix tailTrace_8209944
  have hstable : (prefixWord ++ tailWord_8209944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209944).length < 2 ^ (prefixWord ++ tailWord_8209944).sum := by decide
  have hdescent : baseEnd_8209944 < baseStart_8209944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8209955 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 1, 2, 2]
def baseStart_8209955 : Nat := 118140960795 + 8209955 * 2 ^ 59
def prefixEnd_8209955 : Nat := 4983230072969 + 3 ^ 40 * 8209955 * 2
def baseEnd_8209955 : Nat := 4215653066783531247005611

theorem tailTrace_8209955 : CollatzResearch.WordTrace tailWord_8209955 prefixEnd_8209955 4215653066783531247005611 := by
  unfold tailWord_8209955
  simp only [CollatzResearch.WordTrace]
  refine ⟨299441658971742658528351319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199627772647828439018900879 299441658971742658528351319)
  ·
    refine ⟨449162488457613987792526979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299441658971742658528351319 449162488457613987792526979)
    ·
      refine ⟨673743732686420981688790469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449162488457613987792526979 673743732686420981688790469)
      ·
        refine ⟨126326949878703934066648213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673743732686420981688790469 126326949878703934066648213)
        ·
          refine ⟨5921575775564246909374135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126326949878703934066648213 5921575775564246909374135)
          ·
            refine ⟨8882363663346370364061203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921575775564246909374135 8882363663346370364061203)
            ·
              refine ⟨13323545495019555546091805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882363663346370364061203 13323545495019555546091805)
              ·
                refine ⟨4996329560632333329784427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13323545495019555546091805 4996329560632333329784427)
                ·
                  refine ⟨7494494340948499994676641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996329560632333329784427 7494494340948499994676641)
                  ·
                    refine ⟨5620870755711374996007481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494494340948499994676641 5620870755711374996007481)
                    ·
                      refine ⟨4215653066783531247005611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620870755711374996007481 4215653066783531247005611)
                      ·
                        rfl

theorem cell23_8209955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_8209955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8209955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8209955 prefixEnd_8209955 := by exact prefixLift 8209955
  have htrace : WordTrace (prefixWord ++ tailWord_8209955) baseStart_8209955 baseEnd_8209955 := by
    simpa [prefixWord, tailWord_8209955, baseEnd_8209955] using wordTrace_append hprefix tailTrace_8209955
  have hstable : (prefixWord ++ tailWord_8209955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8209955).length < 2 ^ (prefixWord ++ tailWord_8209955).sum := by decide
  have hdescent : baseEnd_8209955 < baseStart_8209955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8209955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210017 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 5]
def baseStart_8210017 : Nat := 118140960795 + 8210017 * 2 ^ 59
def prefixEnd_8210017 : Nat := 4983230072969 + 3 ^ 40 * 8210017 * 2
def baseEnd_8210017 : Nat := 468409433620456667158925

theorem tailTrace_8210017 : CollatzResearch.WordTrace tailWord_8210017 prefixEnd_8210017 468409433620456667158925 := by
  unfold tailWord_8210017
  simp only [CollatzResearch.WordTrace]
  refine ⟨299443920297518043117108305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199629280198345362078072203 299443920297518043117108305)
  ·
    refine ⟨224582940223138532337831229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299443920297518043117108305 224582940223138532337831229)
    ·
      refine ⟨84218602583676949626686711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224582940223138532337831229 84218602583676949626686711)
      ·
        refine ⟨126327903875515424440030067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84218602583676949626686711 126327903875515424440030067)
        ·
          refine ⟨189491855813273136660045101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126327903875515424440030067 189491855813273136660045101)
          ·
            refine ⟨71059445929977426247516913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189491855813273136660045101 71059445929977426247516913)
            ·
              refine ⟨53294584447483069685637685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71059445929977426247516913 53294584447483069685637685)
              ·
                refine ⟨4996367291951537783028533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53294584447483069685637685 4996367291951537783028533)
                ·
                  refine ⟨468409433620456667158925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996367291951537783028533 468409433620456667158925)
                  ·
                    rfl

theorem cell23_8210017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 5].length) (baseStart_8210017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210017 prefixEnd_8210017 := by exact prefixLift 8210017
  have htrace : WordTrace (prefixWord ++ tailWord_8210017) baseStart_8210017 baseEnd_8210017 := by
    simpa [prefixWord, tailWord_8210017, baseEnd_8210017] using wordTrace_append hprefix tailTrace_8210017
  have hstable : (prefixWord ++ tailWord_8210017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210017).length < 2 ^ (prefixWord ++ tailWord_8210017).sum := by decide
  have hdescent : baseEnd_8210017 < baseStart_8210017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210034 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_8210034 : Nat := 118140960795 + 8210034 * 2 ^ 59
def prefixEnd_8210034 : Nat := 4983230072969 + 3 ^ 40 * 8210034 * 2
def baseEnd_8210034 : Nat := 468410403528359604213083

theorem tailTrace_8210034 : CollatzResearch.WordTrace tailWord_8210034 prefixEnd_8210034 468410403528359604213083 := by
  unfold tailWord_8210034
  simp only [CollatzResearch.WordTrace]
  refine ⟨74861135084614113755119289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199629693558970970013651437 74861135084614113755119289)
  ·
    refine ⟨56145851313460585316339467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74861135084614113755119289 56145851313460585316339467)
    ·
      refine ⟨84218776970190877974509201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56145851313460585316339467 84218776970190877974509201)
      ·
        refine ⟨63164082727643158480881901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84218776970190877974509201 63164082727643158480881901)
        ·
          refine ⟨23686531022866184430330713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63164082727643158480881901 23686531022866184430330713)
          ·
            refine ⟨17764898267149638322748035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23686531022866184430330713 17764898267149638322748035)
            ·
              refine ⟨26647347400724457484122053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17764898267149638322748035 26647347400724457484122053)
              ·
                refine ⟨4996377637635835778272885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26647347400724457484122053 4996377637635835778272885)
                ·
                  refine ⟨468410403528359604213083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996377637635835778272885 468410403528359604213083)
                  ·
                    rfl

theorem cell23_8210034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_8210034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210034 prefixEnd_8210034 := by exact prefixLift 8210034
  have htrace : WordTrace (prefixWord ++ tailWord_8210034) baseStart_8210034 baseEnd_8210034 := by
    simpa [prefixWord, tailWord_8210034, baseEnd_8210034] using wordTrace_append hprefix tailTrace_8210034
  have hstable : (prefixWord ++ tailWord_8210034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210034).length < 2 ^ (prefixWord ++ tailWord_8210034).sum := by decide
  have hdescent : baseEnd_8210034 < baseStart_8210034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210067 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 4, 2]
def baseStart_8210067 : Nat := 118140960795 + 8210067 * 2 ^ 59
def prefixEnd_8210067 : Nat := 4983230072969 + 3 ^ 40 * 8210067 * 2
def baseEnd_8210067 : Nat := 4215710576616834808805095

theorem tailTrace_8210067 : CollatzResearch.WordTrace tailWord_8210067 prefixEnd_8210067 4215710576616834808805095 := by
  unfold tailWord_8210067
  simp only [CollatzResearch.WordTrace]
  refine ⟨299445743947336901656428455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199630495964891267770952303 299445743947336901656428455)
  ·
    refine ⟨449168615921005352484642683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299445743947336901656428455 449168615921005352484642683)
    ·
      refine ⟨673752923881508028726964025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449168615921005352484642683 673752923881508028726964025)
      ·
        refine ⟨505314692911131021545223019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673752923881508028726964025 505314692911131021545223019)
        ·
          refine ⟨757972039366696532317834529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505314692911131021545223019 757972039366696532317834529)
          ·
            refine ⟨568479029525022399238375897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757972039366696532317834529 568479029525022399238375897)
            ·
              refine ⟨426359272143766799428781923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568479029525022399238375897 426359272143766799428781923)
              ·
                refine ⟨639538908215650199143172885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426359272143766799428781923 639538908215650199143172885)
                ·
                  refine ⟨29978386322608603084836229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639538908215650199143172885 29978386322608603084836229)
                  ·
                    refine ⟨5620947435489113078406793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29978386322608603084836229 5620947435489113078406793)
                    ·
                      refine ⟨4215710576616834808805095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620947435489113078406793 4215710576616834808805095)
                      ·
                        rfl

theorem cell23_8210067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4, 2].length) (baseStart_8210067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210067 prefixEnd_8210067 := by exact prefixLift 8210067
  have htrace : WordTrace (prefixWord ++ tailWord_8210067) baseStart_8210067 baseEnd_8210067 := by
    simpa [prefixWord, tailWord_8210067, baseEnd_8210067] using wordTrace_append hprefix tailTrace_8210067
  have hstable : (prefixWord ++ tailWord_8210067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210067).length < 2 ^ (prefixWord ++ tailWord_8210067).sum := by decide
  have hdescent : baseEnd_8210067 < baseStart_8210067 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210077 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_8210077 : Nat := 118140960795 + 8210077 * 2 ^ 59
def prefixEnd_8210077 : Nat := 4983230072969 + 3 ^ 40 * 8210077 * 2
def baseEnd_8210077 : Nat := 1405238570474459923226683

theorem tailTrace_8210077 : CollatzResearch.WordTrace tailWord_8210077 prefixEnd_8210077 1405238570474459923226683 := by
  unfold tailWord_8210077
  simp only [CollatzResearch.WordTrace]
  refine ⟨299446108677300673364292485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199630739118200448909528323 299446108677300673364292485)
  ·
    refine ⟨56146145376993876255804841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299446108677300673364292485 56146145376993876255804841)
    ·
      refine ⟨42109609032745407191853631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56146145376993876255804841 42109609032745407191853631)
      ·
        refine ⟨63164413549118110787780447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42109609032745407191853631 63164413549118110787780447)
        ·
          refine ⟨94746620323677166181670671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63164413549118110787780447 94746620323677166181670671)
          ·
            refine ⟨142119930485515749272506007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94746620323677166181670671 142119930485515749272506007)
            ·
              refine ⟨213179895728273623908759011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142119930485515749272506007 213179895728273623908759011)
              ·
                refine ⟨319769843592410435863138517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213179895728273623908759011 319769843592410435863138517)
                ·
                  refine ⟨7494605709197119590542309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319769843592410435863138517 7494605709197119590542309)
                  ·
                    refine ⟨1405238570474459923226683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494605709197119590542309 1405238570474459923226683)
                    ·
                      rfl

theorem cell23_8210077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_8210077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210077 prefixEnd_8210077 := by exact prefixLift 8210077
  have htrace : WordTrace (prefixWord ++ tailWord_8210077) baseStart_8210077 baseEnd_8210077 := by
    simpa [prefixWord, tailWord_8210077, baseEnd_8210077] using wordTrace_append hprefix tailTrace_8210077
  have hstable : (prefixWord ++ tailWord_8210077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210077).length < 2 ^ (prefixWord ++ tailWord_8210077).sum := by decide
  have hdescent : baseEnd_8210077 < baseStart_8210077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210084 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_8210084 : Nat := 118140960795 + 8210084 * 2 ^ 59
def prefixEnd_8210084 : Nat := 4983230072969 + 3 ^ 40 * 8210084 * 2
def baseEnd_8210084 : Nat := 4215719305787961242292517

theorem tailTrace_8210084 : CollatzResearch.WordTrace tailWord_8210084 prefixEnd_8210084 4215719305787961242292517 := by
  unfold tailWord_8210084
  simp only [CollatzResearch.WordTrace]
  refine ⟨149723181994137656779898653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199630909325516875706531537 149723181994137656779898653)
  ·
    refine ⟨56146193247801621292461995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149723181994137656779898653 56146193247801621292461995)
    ·
      refine ⟨84219289871702431938692993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56146193247801621292461995 84219289871702431938692993)
      ·
        refine ⟨63164467403776823954019745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84219289871702431938692993 63164467403776823954019745)
        ·
          refine ⟨47373350552832617965514809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63164467403776823954019745 47373350552832617965514809)
          ·
            refine ⟨35530012914624463474136107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47373350552832617965514809 35530012914624463474136107)
            ·
              refine ⟨53295019371936695211204161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35530012914624463474136107 53295019371936695211204161)
              ·
                refine ⟨39971264528952521408403121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53295019371936695211204161 39971264528952521408403121)
                ·
                  refine ⟨29978448396714391056302341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39971264528952521408403121 29978448396714391056302341)
                  ·
                    refine ⟨5620959074383948323056689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29978448396714391056302341 5620959074383948323056689)
                    ·
                      refine ⟨4215719305787961242292517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5620959074383948323056689 4215719305787961242292517)
                      ·
                        rfl

theorem cell23_8210084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_8210084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210084 prefixEnd_8210084 := by exact prefixLift 8210084
  have htrace : WordTrace (prefixWord ++ tailWord_8210084) baseStart_8210084 baseEnd_8210084 := by
    simpa [prefixWord, tailWord_8210084, baseEnd_8210084] using wordTrace_append hprefix tailTrace_8210084
  have hstable : (prefixWord ++ tailWord_8210084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210084).length < 2 ^ (prefixWord ++ tailWord_8210084).sum := by decide
  have hdescent : baseEnd_8210084 < baseStart_8210084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210144 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2]
def baseStart_8210144 : Nat := 118140960795 + 8210144 * 2 ^ 59
def prefixEnd_8210144 : Nat := 4983230072969 + 3 ^ 40 * 8210144 * 2
def baseEnd_8210144 : Nat := 4215750114627231007542241

theorem tailTrace_8210144 : CollatzResearch.WordTrace tailWord_8210144 prefixEnd_8210144 4215750114627231007542241 := by
  unfold tailWord_8210144
  simp only [CollatzResearch.WordTrace]
  refine ⟨149724276184028971903490743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199632368245371962537987657 149724276184028971903490743)
  ·
    refine ⟨224586414276043457855236115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149724276184028971903490743 224586414276043457855236115)
    ·
      refine ⟨336879621414065186782854173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224586414276043457855236115 336879621414065186782854173)
      ·
        refine ⟨126329858030274445043570315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336879621414065186782854173 126329858030274445043570315)
        ·
          refine ⟨189494787045411667565355473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126329858030274445043570315 189494787045411667565355473)
          ·
            refine ⟨142121090284058750674016605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189494787045411667565355473 142121090284058750674016605)
            ·
              refine ⟨53295408856522031502756227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142121090284058750674016605 53295408856522031502756227)
              ·
                refine ⟨79943113284783047254134341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53295408856522031502756227 79943113284783047254134341)
                ·
                  refine ⟨14989333740896821360150189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79943113284783047254134341 14989333740896821360150189)
                  ·
                    refine ⟨5621000152836308010056321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14989333740896821360150189 5621000152836308010056321)
                    ·
                      refine ⟨4215750114627231007542241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621000152836308010056321 4215750114627231007542241)
                      ·
                        rfl

theorem cell23_8210144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_8210144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210144 prefixEnd_8210144 := by exact prefixLift 8210144
  have htrace : WordTrace (prefixWord ++ tailWord_8210144) baseStart_8210144 baseEnd_8210144 := by
    simpa [prefixWord, tailWord_8210144, baseEnd_8210144] using wordTrace_append hprefix tailTrace_8210144
  have hstable : (prefixWord ++ tailWord_8210144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210144).length < 2 ^ (prefixWord ++ tailWord_8210144).sum := by decide
  have hdescent : baseEnd_8210144 < baseStart_8210144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210177 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_8210177 : Nat := 118140960795 + 8210177 * 2 ^ 59
def prefixEnd_8210177 : Nat := 4983230072969 + 3 ^ 40 * 8210177 * 2
def baseEnd_8210177 : Nat := 4215767059488829378429589

theorem tailTrace_8210177 : CollatzResearch.WordTrace tailWord_8210177 prefixEnd_8210177 4215767059488829378429589 := by
  unfold tailWord_8210177
  simp only [CollatzResearch.WordTrace]
  refine ⟨299449755976938390442932785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199633170651292260295288523 299449755976938390442932785)
  ·
    refine ⟨224587316982703792832199589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299449755976938390442932785 224587316982703792832199589)
    ·
      refine ⟨42110121934256961156037423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224587316982703792832199589 42110121934256961156037423)
      ·
        refine ⟨63165182901385441734056135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42110121934256961156037423 63165182901385441734056135)
        ·
          refine ⟨94747774352078162601084203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63165182901385441734056135 94747774352078162601084203)
          ·
            refine ⟨142121661528117243901626305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94747774352078162601084203 142121661528117243901626305)
            ·
              refine ⟨106591246146087932926219729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142121661528117243901626305 106591246146087932926219729)
              ·
                refine ⟨79943434609565949694664797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106591246146087932926219729 79943434609565949694664797)
                ·
                  refine ⟨29978787978587231135499299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79943434609565949694664797 29978787978587231135499299)
                  ·
                    refine ⟨44968181967880846703248949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29978787978587231135499299 44968181967880846703248949)
                    ·
                      refine ⟨4215767059488829378429589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44968181967880846703248949 4215767059488829378429589)
                      ·
                        rfl

theorem cell23_8210177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_8210177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210177 prefixEnd_8210177 := by exact prefixLift 8210177
  have htrace : WordTrace (prefixWord ++ tailWord_8210177) baseStart_8210177 baseEnd_8210177 := by
    simpa [prefixWord, tailWord_8210177, baseEnd_8210177] using wordTrace_append hprefix tailTrace_8210177
  have hstable : (prefixWord ++ tailWord_8210177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210177).length < 2 ^ (prefixWord ++ tailWord_8210177).sum := by decide
  have hdescent : baseEnd_8210177 < baseStart_8210177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210178 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_8210178 : Nat := 118140960795 + 8210178 * 2 ^ 59
def prefixEnd_8210178 : Nat := 4983230072969 + 3 ^ 40 * 8210178 * 2
def baseEnd_8210178 : Nat := 4215767572969483874517085

theorem tailTrace_8210178 : CollatzResearch.WordTrace tailWord_8210178 prefixEnd_8210178 4215767572969483874517085 := by
  unfold tailWord_8210178
  simp only [CollatzResearch.WordTrace]
  refine ⟨74862448112483691903429797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199633194966623178409146125 74862448112483691903429797)
  ·
    refine ⟨14036709021090692231893087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74862448112483691903429797 14036709021090692231893087)
    ·
      refine ⟨21055063531636038347839631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14036709021090692231893087 21055063531636038347839631)
      ·
        refine ⟨31582595297454057521759447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21055063531636038347839631 31582595297454057521759447)
        ·
          refine ⟨47373892946181086282639171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31582595297454057521759447 47373892946181086282639171)
          ·
            refine ⟨71060839419271629423958757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47373892946181086282639171 71060839419271629423958757)
            ·
              refine ⟨13323907391113430516992267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71060839419271629423958757 13323907391113430516992267)
              ·
                refine ⟨19985861086670145775488401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323907391113430516992267 19985861086670145775488401)
                ·
                  refine ⟨14989395815002609331616301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19985861086670145775488401 14989395815002609331616301)
                  ·
                    refine ⟨5621023430625978499356113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14989395815002609331616301 5621023430625978499356113)
                    ·
                      refine ⟨4215767572969483874517085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621023430625978499356113 4215767572969483874517085)
                      ·
                        rfl

theorem cell23_8210178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_8210178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210178 prefixEnd_8210178 := by exact prefixLift 8210178
  have htrace : WordTrace (prefixWord ++ tailWord_8210178) baseStart_8210178 baseEnd_8210178 := by
    simpa [prefixWord, tailWord_8210178, baseEnd_8210178] using wordTrace_append hprefix tailTrace_8210178
  have hstable : (prefixWord ++ tailWord_8210178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210178).length < 2 ^ (prefixWord ++ tailWord_8210178).sum := by decide
  have hdescent : baseEnd_8210178 < baseStart_8210178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210187 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_8210187 : Nat := 118140960795 + 8210187 * 2 ^ 59
def prefixEnd_8210187 : Nat := 4983230072969 + 3 ^ 40 * 8210187 * 2
def baseEnd_8210187 : Nat := 4215772194295374339304543

theorem tailTrace_8210187 : CollatzResearch.WordTrace tailWord_8210187 prefixEnd_8210187 4215772194295374339304543 := by
  unfold tailWord_8210187
  simp only [CollatzResearch.WordTrace]
  refine ⟨299450120706902162150796815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199633413804601441433864543 299450120706902162150796815)
  ·
    refine ⟨449175181060353243226195223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299450120706902162150796815 449175181060353243226195223)
    ·
      refine ⟨673762771590529864839292835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449175181060353243226195223 673762771590529864839292835)
      ·
        refine ⟨1010644157385794797258939253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673762771590529864839292835 1010644157385794797258939253)
        ·
          refine ⟨94747889754918262243025555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1010644157385794797258939253 94747889754918262243025555)
          ·
            refine ⟨142121834632377393364538333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94747889754918262243025555 142121834632377393364538333)
            ·
              refine ⟨53295687987141522511701875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142121834632377393364538333 53295687987141522511701875)
              ·
                refine ⟨79943531980712283767552813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53295687987141522511701875 79943531980712283767552813)
                ·
                  refine ⟨29978824492767106412832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79943531980712283767552813 29978824492767106412832305)
                  ·
                    refine ⟨22484118369575329809624229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29978824492767106412832305 22484118369575329809624229)
                    ·
                      refine ⟨4215772194295374339304543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22484118369575329809624229 4215772194295374339304543)
                      ·
                        rfl

theorem cell23_8210187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_8210187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210187 prefixEnd_8210187 := by exact prefixLift 8210187
  have htrace : WordTrace (prefixWord ++ tailWord_8210187) baseStart_8210187 baseEnd_8210187 := by
    simpa [prefixWord, tailWord_8210187, baseEnd_8210187] using wordTrace_append hprefix tailTrace_8210187
  have hstable : (prefixWord ++ tailWord_8210187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210187).length < 2 ^ (prefixWord ++ tailWord_8210187).sum := by decide
  have hdescent : baseEnd_8210187 < baseStart_8210187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210196 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8210196 : Nat := 118140960795 + 8210196 * 2 ^ 59
def prefixEnd_8210196 : Nat := 4983230072969 + 3 ^ 40 * 8210196 * 2
def baseEnd_8210196 : Nat := 1405258938540421601364001

theorem tailTrace_8210196 : CollatzResearch.WordTrace tailWord_8210196 prefixEnd_8210196 1405258938540421601364001 := by
  unfold tailWord_8210196
  simp only [CollatzResearch.WordTrace]
  refine ⟨149725224481934778343937221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199633632642579704458582961 149725224481934778343937221)
  ·
    refine ⟨28073479590362770939488229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149725224481934778343937221 28073479590362770939488229)
    ·
      refine ⟨5263777423193019551154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28073479590362770939488229 5263777423193019551154043)
      ·
        refine ⟨7895666134789529326731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263777423193019551154043 7895666134789529326731065)
        ·
          refine ⟨5921749601092146995048299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7895666134789529326731065 5921749601092146995048299)
          ·
            refine ⟨8882624401638220492572449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921749601092146995048299 8882624401638220492572449)
            ·
              refine ⟨6661968301228665369429337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882624401638220492572449 6661968301228665369429337)
              ·
                refine ⟨4996476225921499027072003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6661968301228665369429337 4996476225921499027072003)
                ·
                  refine ⟨7494714338882248540608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996476225921499027072003 7494714338882248540608005)
                  ·
                    refine ⟨1405258938540421601364001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494714338882248540608005 1405258938540421601364001)
                    ·
                      rfl

theorem cell23_8210196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8210196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210196 prefixEnd_8210196 := by exact prefixLift 8210196
  have htrace : WordTrace (prefixWord ++ tailWord_8210196) baseStart_8210196 baseEnd_8210196 := by
    simpa [prefixWord, tailWord_8210196, baseEnd_8210196] using wordTrace_append hprefix tailTrace_8210196
  have hstable : (prefixWord ++ tailWord_8210196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210196).length < 2 ^ (prefixWord ++ tailWord_8210196).sum := by decide
  have hdescent : baseEnd_8210196 < baseStart_8210196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210224 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3]
def baseStart_8210224 : Nat := 118140960795 + 8210224 * 2 ^ 59
def prefixEnd_8210224 : Nat := 4983230072969 + 3 ^ 40 * 8210224 * 2
def baseEnd_8210224 : Nat := 4215791193079590694541873

theorem tailTrace_8210224 : CollatzResearch.WordTrace tailWord_8210224 prefixEnd_8210224 4215791193079590694541873 := by
  unfold tailWord_8210224
  simp only [CollatzResearch.WordTrace]
  refine ⟨149725735103884058734946863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199634313471845411646595817 149725735103884058734946863)
  ·
    refine ⟨224588602655826088102420295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149725735103884058734946863 224588602655826088102420295)
    ·
      refine ⟨336882903983739132153630443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224588602655826088102420295 336882903983739132153630443)
      ·
        refine ⟨505324355975608698230445665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336882903983739132153630443 505324355975608698230445665)
        ·
          refine ⟨378993266981706523672834249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505324355975608698230445665 378993266981706523672834249)
          ·
            refine ⟨284244950236279892754625687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378993266981706523672834249 284244950236279892754625687)
            ·
              refine ⟨426367425354419839131938531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284244950236279892754625687 426367425354419839131938531)
              ·
                refine ⟨639551138031629758697907797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426367425354419839131938531 639551138031629758697907797)
                ·
                  refine ⟨7494739898808161234741107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 639551138031629758697907797 7494739898808161234741107)
                  ·
                    refine ⟨11242109848212241852111661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494739898808161234741107 11242109848212241852111661)
                    ·
                      refine ⟨4215791193079590694541873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242109848212241852111661 4215791193079590694541873)
                      ·
                        rfl

theorem cell23_8210224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 1, 3].length) (baseStart_8210224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210224 prefixEnd_8210224 := by exact prefixLift 8210224
  have htrace : WordTrace (prefixWord ++ tailWord_8210224) baseStart_8210224 baseEnd_8210224 := by
    simpa [prefixWord, tailWord_8210224, baseEnd_8210224] using wordTrace_append hprefix tailTrace_8210224
  have hstable : (prefixWord ++ tailWord_8210224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210224).length < 2 ^ (prefixWord ++ tailWord_8210224).sum := by decide
  have hdescent : baseEnd_8210224 < baseStart_8210224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210258 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_8210258 : Nat := 118140960795 + 8210258 * 2 ^ 59
def prefixEnd_8210258 : Nat := 4983230072969 + 3 ^ 40 * 8210258 * 2
def baseEnd_8210258 : Nat := 4215808651421843561516717

theorem tailTrace_8210258 : CollatzResearch.WordTrace tailWord_8210258 prefixEnd_8210258 4215808651421843561516717 := by
  unfold tailWord_8210258
  simp only [CollatzResearch.WordTrace]
  refine ⟨74863177572411235319157857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199635140193096627517754285 74863177572411235319157857)
  ·
    refine ⟨56147383179308426489368393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74863177572411235319157857 56147383179308426489368393)
    ·
      refine ⟨42110537384481319867026295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56147383179308426489368393 42110537384481319867026295)
      ·
        refine ⟨63165806076721979800539443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42110537384481319867026295 63165806076721979800539443)
        ·
          refine ⟨94748709115082969700809165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63165806076721979800539443 94748709115082969700809165)
          ·
            refine ⟨35530765918156113637803437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94748709115082969700809165 35530765918156113637803437)
            ·
              refine ⟨13324037219308542614176289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35530765918156113637803437 13324037219308542614176289)
              ·
                refine ⟨9993027914481406960632217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324037219308542614176289 9993027914481406960632217)
                ·
                  refine ⟨7494770935861055220474163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993027914481406960632217 7494770935861055220474163)
                  ·
                    refine ⟨11242156403791582830711245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494770935861055220474163 11242156403791582830711245)
                    ·
                      refine ⟨4215808651421843561516717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242156403791582830711245 4215808651421843561516717)
                      ·
                        rfl

theorem cell23_8210258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_8210258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210258 prefixEnd_8210258 := by exact prefixLift 8210258
  have htrace : WordTrace (prefixWord ++ tailWord_8210258) baseStart_8210258 baseEnd_8210258 := by
    simpa [prefixWord, tailWord_8210258, baseEnd_8210258] using wordTrace_append hprefix tailTrace_8210258
  have hstable : (prefixWord ++ tailWord_8210258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210258).length < 2 ^ (prefixWord ++ tailWord_8210258).sum := by decide
  have hdescent : baseEnd_8210258 < baseStart_8210258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210264 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_8210264 : Nat := 118140960795 + 8210264 * 2 ^ 59
def prefixEnd_8210264 : Nat := 4983230072969 + 3 ^ 40 * 8210264 * 2
def baseEnd_8210264 : Nat := 4215811732305770538041689

theorem tailTrace_8210264 : CollatzResearch.WordTrace tailWord_8210264 prefixEnd_8210264 4215811732305770538041689 := by
  unfold tailWord_8210264
  simp only [CollatzResearch.WordTrace]
  refine ⟨149726464563811602150674923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199635286085082136200899897 149726464563811602150674923)
  ·
    refine ⟨224589696845717403226012385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149726464563811602150674923 224589696845717403226012385)
    ·
      refine ⟨168442272634288052419509289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224589696845717403226012385 168442272634288052419509289)
      ·
        refine ⟨126331704475716039314631967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168442272634288052419509289 126331704475716039314631967)
        ·
          refine ⟨189497556713574058971947951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126331704475716039314631967 189497556713574058971947951)
          ·
            refine ⟨284246335070361088457921927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189497556713574058971947951 284246335070361088457921927)
            ·
              refine ⟨426369502605541632686882891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284246335070361088457921927 426369502605541632686882891)
              ·
                refine ⟨639554253908312449030324337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426369502605541632686882891 639554253908312449030324337)
                ·
                  refine ⟨479665690431234336772743253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639554253908312449030324337 479665690431234336772743253)
                  ·
                    refine ⟨5621082309741027384055585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 479665690431234336772743253 5621082309741027384055585)
                    ·
                      refine ⟨4215811732305770538041689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621082309741027384055585 4215811732305770538041689)
                      ·
                        rfl

theorem cell23_8210264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_8210264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210264 prefixEnd_8210264 := by exact prefixLift 8210264
  have htrace : WordTrace (prefixWord ++ tailWord_8210264) baseStart_8210264 baseEnd_8210264 := by
    simpa [prefixWord, tailWord_8210264, baseEnd_8210264] using wordTrace_append hprefix tailTrace_8210264
  have hstable : (prefixWord ++ tailWord_8210264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210264).length < 2 ^ (prefixWord ++ tailWord_8210264).sum := by decide
  have hdescent : baseEnd_8210264 < baseStart_8210264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210275 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 2, 1, 3]
def baseStart_8210275 : Nat := 118140960795 + 8210275 * 2 ^ 59
def prefixEnd_8210275 : Nat := 4983230072969 + 3 ^ 40 * 8210275 * 2
def baseEnd_8210275 : Nat := 4215817380592969995004139

theorem tailTrace_8210275 : CollatzResearch.WordTrace tailWord_8210275 prefixEnd_8210275 4215817380592969995004139 := by
  unfold tailWord_8210275
  simp only [CollatzResearch.WordTrace]
  refine ⟨299453330330583353180000279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199635553553722235453333519 299453330330583353180000279)
  ·
    refine ⟨449179995495875029770000419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299453330330583353180000279 449179995495875029770000419)
    ·
      refine ⟨673769993243812544655000629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449179995495875029770000419 673769993243812544655000629)
      ·
        refine ⟨63165936866607426061406309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 673769993243812544655000629 63165936866607426061406309)
        ·
          refine ⟨11843613162488892386513683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63165936866607426061406309 11843613162488892386513683)
          ·
            refine ⟨17765419743733338579770525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843613162488892386513683 17765419743733338579770525)
            ·
              refine ⟨6662032403900001967413947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17765419743733338579770525 6662032403900001967413947)
              ·
                refine ⟨9993048605850002951120921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662032403900001967413947 9993048605850002951120921)
                ·
                  refine ⟨7494786454387502213340691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993048605850002951120921 7494786454387502213340691)
                  ·
                    refine ⟨11242179681581253320011037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494786454387502213340691 11242179681581253320011037)
                    ·
                      refine ⟨4215817380592969995004139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242179681581253320011037 4215817380592969995004139)
                      ·
                        rfl

theorem cell23_8210275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_8210275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210275 prefixEnd_8210275 := by exact prefixLift 8210275
  have htrace : WordTrace (prefixWord ++ tailWord_8210275) baseStart_8210275 baseEnd_8210275 := by
    simpa [prefixWord, tailWord_8210275, baseEnd_8210275] using wordTrace_append hprefix tailTrace_8210275
  have hstable : (prefixWord ++ tailWord_8210275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210275).length < 2 ^ (prefixWord ++ tailWord_8210275).sum := by decide
  have hdescent : baseEnd_8210275 < baseStart_8210275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210326 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_8210326 : Nat := 118140960795 + 8210326 * 2 ^ 59
def prefixEnd_8210326 : Nat := 4983230072969 + 3 ^ 40 * 8210326 * 2
def baseEnd_8210326 : Nat := 4215843568106349295466405

theorem tailTrace_8210326 : CollatzResearch.WordTrace tailWord_8210326 prefixEnd_8210326 4215843568106349295466405 := by
  unfold tailWord_8210326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715949403337411805631677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199636793635599059260071221 18715949403337411805631677)
  ·
    refine ⟨7018481026251529427111879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18715949403337411805631677 7018481026251529427111879)
    ·
      refine ⟨10527721539377294140667819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018481026251529427111879 10527721539377294140667819)
      ·
        refine ⟨15791582309065941211001729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527721539377294140667819 15791582309065941211001729)
        ·
          refine ⟨11843686731799455908251297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15791582309065941211001729 11843686731799455908251297)
          ·
            refine ⟨8882765048849591931188473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843686731799455908251297 8882765048849591931188473)
            ·
              refine ⟨6662073786637193948391355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882765048849591931188473 6662073786637193948391355)
              ·
                refine ⟨9993110679955790922587033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662073786637193948391355 9993110679955790922587033)
                ·
                  refine ⟨7494833009966843191940275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993110679955790922587033 7494833009966843191940275)
                  ·
                    refine ⟨11242249514950264787910413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494833009966843191940275 11242249514950264787910413)
                    ·
                      refine ⟨4215843568106349295466405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242249514950264787910413 4215843568106349295466405)
                      ·
                        rfl

theorem cell23_8210326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_8210326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210326 prefixEnd_8210326 := by exact prefixLift 8210326
  have htrace : WordTrace (prefixWord ++ tailWord_8210326) baseStart_8210326 baseEnd_8210326 := by
    simpa [prefixWord, tailWord_8210326, baseEnd_8210326] using wordTrace_append hprefix tailTrace_8210326
  have hstable : (prefixWord ++ tailWord_8210326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210326).length < 2 ^ (prefixWord ++ tailWord_8210326).sum := by decide
  have hdescent : baseEnd_8210326 < baseStart_8210326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210332 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_8210332 : Nat := 118140960795 + 8210332 * 2 ^ 59
def prefixEnd_8210332 : Nat := 4983230072969 + 3 ^ 40 * 8210332 * 2
def baseEnd_8210332 : Nat := 4215846648990276271991377

theorem tailTrace_8210332 : CollatzResearch.WordTrace tailWord_8210332 prefixEnd_8210332 4215846648990276271991377 := by
  unfold tailWord_8210332
  simp only [CollatzResearch.WordTrace]
  refine ⟨149727704645688425957412625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199636939527584567943216833 149727704645688425957412625)
  ·
    refine ⟨112295778484266319468059469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149727704645688425957412625 112295778484266319468059469)
    ·
      refine ⟨42110916931599869800522301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112295778484266319468059469 42110916931599869800522301)
      ·
        refine ⟨15791593849349951175195863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42110916931599869800522301 15791593849349951175195863)
        ·
          refine ⟨23687390774024926762793795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15791593849349951175195863 23687390774024926762793795)
          ·
            refine ⟨35531086161037390144190693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23687390774024926762793795 35531086161037390144190693)
            ·
              refine ⟨6662078655194510652035755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35531086161037390144190693 6662078655194510652035755)
              ·
                refine ⟨9993117982791765978053633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662078655194510652035755 9993117982791765978053633)
                ·
                  refine ⟨7494838487093824483540225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993117982791765978053633 7494838487093824483540225)
                  ·
                    refine ⟨5621128865320368362655169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494838487093824483540225 5621128865320368362655169)
                    ·
                      refine ⟨4215846648990276271991377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621128865320368362655169 4215846648990276271991377)
                      ·
                        rfl

theorem cell23_8210332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_8210332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210332 prefixEnd_8210332 := by exact prefixLift 8210332
  have htrace : WordTrace (prefixWord ++ tailWord_8210332) baseStart_8210332 baseEnd_8210332 := by
    simpa [prefixWord, tailWord_8210332, baseEnd_8210332] using wordTrace_append hprefix tailTrace_8210332
  have hstable : (prefixWord ++ tailWord_8210332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210332).length < 2 ^ (prefixWord ++ tailWord_8210332).sum := by decide
  have hdescent : baseEnd_8210332 < baseStart_8210332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210354 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_8210354 : Nat := 118140960795 + 8210354 * 2 ^ 59
def prefixEnd_8210354 : Nat := 4983230072969 + 3 ^ 40 * 8210354 * 2
def baseEnd_8210354 : Nat := 4215857945564675185916275

theorem tailTrace_8210354 : CollatzResearch.WordTrace tailWord_8210354 prefixEnd_8210354 4215857945564675185916275 := by
  unfold tailWord_8210354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74864052924324287418031529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199637474464864766448084077 74864052924324287418031529)
  ·
    refine ⟨56148039693243215563523647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74864052924324287418031529 56148039693243215563523647)
    ·
      refine ⟨84222059539864823345285471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56148039693243215563523647 84222059539864823345285471)
      ·
        refine ⟨126333089309797235017928207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84222059539864823345285471 126333089309797235017928207)
        ·
          refine ⟨189499633964695852526892311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126333089309797235017928207 189499633964695852526892311)
          ·
            refine ⟨284249450947043778790338467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189499633964695852526892311 284249450947043778790338467)
            ·
              refine ⟨426374176420565668185507701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284249450947043778790338467 426374176420565668185507701)
              ·
                refine ⟨39972579039428031392391347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426374176420565668185507701 39972579039428031392391347)
                ·
                  refine ⟨59958868559142047088587021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39972579039428031392391347 59958868559142047088587021)
                  ·
                    refine ⟨22484575709678267658220133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59958868559142047088587021 22484575709678267658220133)
                    ·
                      refine ⟨4215857945564675185916275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22484575709678267658220133 4215857945564675185916275)
                      ·
                        rfl

theorem cell23_8210354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_8210354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210354 prefixEnd_8210354 := by exact prefixLift 8210354
  have htrace : WordTrace (prefixWord ++ tailWord_8210354) baseStart_8210354 baseEnd_8210354 := by
    simpa [prefixWord, tailWord_8210354, baseEnd_8210354] using wordTrace_append hprefix tailTrace_8210354
  have hstable : (prefixWord ++ tailWord_8210354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210354).length < 2 ^ (prefixWord ++ tailWord_8210354).sum := by decide
  have hdescent : baseEnd_8210354 < baseStart_8210354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210388 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_8210388 : Nat := 118140960795 + 8210388 * 2 ^ 59
def prefixEnd_8210388 : Nat := 4983230072969 + 3 ^ 40 * 8210388 * 2
def baseEnd_8210388 : Nat := 4215875403906928052891119

theorem tailTrace_8210388 : CollatzResearch.WordTrace tailWord_8210388 prefixEnd_8210388 4215875403906928052891119 := by
  unfold tailWord_8210388
  simp only [CollatzResearch.WordTrace]
  refine ⟨149728725889586986739431909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199638301186115982319242545 149728725889586986739431909)
  ·
    refine ⟨28074136104297560013643483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149728725889586986739431909 28074136104297560013643483)
    ·
      refine ⟨42111204156446340020465225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28074136104297560013643483 42111204156446340020465225)
      ·
        refine ⟨31583403117334755015348919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42111204156446340020465225 31583403117334755015348919)
        ·
          refine ⟨47375104676002132523023379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31583403117334755015348919 47375104676002132523023379)
          ·
            refine ⟨71062657014003198784535069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47375104676002132523023379 71062657014003198784535069)
            ·
              refine ⟨26648496380251199544200651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71062657014003198784535069 26648496380251199544200651)
              ·
                refine ⟨39972744570376799316300977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26648496380251199544200651 39972744570376799316300977)
                ·
                  refine ⟨29979558427782599487225733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39972744570376799316300977 29979558427782599487225733)
                  ·
                    refine ⟨5621167205209237403854825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29979558427782599487225733 5621167205209237403854825)
                    ·
                      refine ⟨4215875403906928052891119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621167205209237403854825 4215875403906928052891119)
                      ·
                        rfl

theorem cell23_8210388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_8210388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210388 prefixEnd_8210388 := by exact prefixLift 8210388
  have htrace : WordTrace (prefixWord ++ tailWord_8210388) baseStart_8210388 baseEnd_8210388 := by
    simpa [prefixWord, tailWord_8210388, baseEnd_8210388] using wordTrace_append hprefix tailTrace_8210388
  have hstable : (prefixWord ++ tailWord_8210388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210388).length < 2 ^ (prefixWord ++ tailWord_8210388).sum := by decide
  have hdescent : baseEnd_8210388 < baseStart_8210388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210402 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8210402 : Nat := 118140960795 + 8210402 * 2 ^ 59
def prefixEnd_8210402 : Nat := 4983230072969 + 3 ^ 40 * 8210402 * 2
def baseEnd_8210402 : Nat := 1405294197545363666038685

theorem tailTrace_8210402 : CollatzResearch.WordTrace tailWord_8210402 prefixEnd_8210402 1405294197545363666038685 := by
  unfold tailWord_8210402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74864490600280813467468365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199638641600748835913248973 74864490600280813467468365)
  ·
    refine ⟨28074183975105305050300637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74864490600280813467468365 28074183975105305050300637)
    ·
      refine ⟨10527818990664489393862739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28074183975105305050300637 10527818990664489393862739)
      ·
        refine ⟨15791728485996734090794109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527818990664489393862739 15791728485996734090794109)
        ·
          refine ⟨5921898182248775284047791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15791728485996734090794109 5921898182248775284047791)
          ·
            refine ⟨8882847273373162926071687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921898182248775284047791 8882847273373162926071687)
            ·
              refine ⟨13324270910059744389107531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882847273373162926071687 13324270910059744389107531)
              ·
                refine ⟨19986406365089616583661297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324270910059744389107531 19986406365089616583661297)
                ·
                  refine ⟨14989804773817212437745973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19986406365089616583661297 14989804773817212437745973)
                  ·
                    refine ⟨1405294197545363666038685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14989804773817212437745973 1405294197545363666038685)
                    ·
                      rfl

theorem cell23_8210402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8210402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210402 prefixEnd_8210402 := by exact prefixLift 8210402
  have htrace : WordTrace (prefixWord ++ tailWord_8210402) baseStart_8210402 baseEnd_8210402 := by
    simpa [prefixWord, tailWord_8210402, baseEnd_8210402] using wordTrace_append hprefix tailTrace_8210402
  have hstable : (prefixWord ++ tailWord_8210402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210402).length < 2 ^ (prefixWord ++ tailWord_8210402).sum := by decide
  have hdescent : baseEnd_8210402 < baseStart_8210402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210458 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_8210458 : Nat := 118140960795 + 8210458 * 2 ^ 59
def prefixEnd_8210458 : Nat := 4983230072969 + 3 ^ 40 * 8210458 * 2
def baseEnd_8210458 : Nat := 1405303782517580926338599

theorem tailTrace_8210458 : CollatzResearch.WordTrace tailWord_8210458 prefixEnd_8210458 1405303782517580926338599 := by
  unfold tailWord_8210458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74865001222230093858478007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199640003259280250289274685 74865001222230093858478007)
  ·
    refine ⟨112297501833345140787717011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74865001222230093858478007 112297501833345140787717011)
    ·
      refine ⟨168446252750017711181575517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112297501833345140787717011 168446252750017711181575517)
      ·
        refine ⟨63167344781256641693090819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168446252750017711181575517 63167344781256641693090819)
        ·
          refine ⟨94751017171884962539636229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63167344781256641693090819 94751017171884962539636229)
          ·
            refine ⟨17765815719728430476181793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94751017171884962539636229 17765815719728430476181793)
            ·
              refine ⟨13324361789796322857136345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17765815719728430476181793 13324361789796322857136345)
              ·
                refine ⟨9993271342347242142852259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324361789796322857136345 9993271342347242142852259)
                ·
                  refine ⟨14989907013520863214278389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993271342347242142852259 14989907013520863214278389)
                  ·
                    refine ⟨1405303782517580926338599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14989907013520863214278389 1405303782517580926338599)
                    ·
                      rfl

theorem cell23_8210458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_8210458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210458 prefixEnd_8210458 := by exact prefixLift 8210458
  have htrace : WordTrace (prefixWord ++ tailWord_8210458) baseStart_8210458 baseEnd_8210458 := by
    simpa [prefixWord, tailWord_8210458, baseEnd_8210458] using wordTrace_append hprefix tailTrace_8210458
  have hstable : (prefixWord ++ tailWord_8210458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210458).length < 2 ^ (prefixWord ++ tailWord_8210458).sum := by decide
  have hdescent : baseEnd_8210458 < baseStart_8210458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210481 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_8210481 : Nat := 118140960795 + 8210481 * 2 ^ 59
def prefixEnd_8210481 : Nat := 4983230072969 + 3 ^ 40 * 8210481 * 2
def baseEnd_8210481 : Nat := 4215923157607796189028191

theorem tailTrace_8210481 : CollatzResearch.WordTrace tailWord_8210481 prefixEnd_8210481 4215923157607796189028191 := by
  unfold tailWord_8210481
  simp only [CollatzResearch.WordTrace]
  refine ⟨299460843767837050361999297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199640562511891366907999531 299460843767837050361999297)
  ·
    refine ⟨224595632825877787771499473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299460843767837050361999297 224595632825877787771499473)
    ·
      refine ⟨168446724619408340828624605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224595632825877787771499473 168446724619408340828624605)
      ·
        refine ⟨63167521732278127810734227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168446724619408340828624605 63167521732278127810734227)
        ·
          refine ⟨94751282598417191716101341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63167521732278127810734227 94751282598417191716101341)
          ·
            refine ⟨35531730974406446893538003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94751282598417191716101341 35531730974406446893538003)
            ·
              refine ⟨53297596461609670340307005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35531730974406446893538003 53297596461609670340307005)
              ·
                refine ⟨19986598673103626377615127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53297596461609670340307005 19986598673103626377615127)
                ·
                  refine ⟨29979898009655439566422691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19986598673103626377615127 29979898009655439566422691)
                  ·
                    refine ⟨44969847014483159349634037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29979898009655439566422691 44969847014483159349634037)
                    ·
                      refine ⟨4215923157607796189028191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44969847014483159349634037 4215923157607796189028191)
                      ·
                        rfl

theorem cell23_8210481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_8210481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210481 prefixEnd_8210481 := by exact prefixLift 8210481
  have htrace : WordTrace (prefixWord ++ tailWord_8210481) baseStart_8210481 baseEnd_8210481 := by
    simpa [prefixWord, tailWord_8210481, baseEnd_8210481] using wordTrace_append hprefix tailTrace_8210481
  have hstable : (prefixWord ++ tailWord_8210481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210481).length < 2 ^ (prefixWord ++ tailWord_8210481).sum := by decide
  have hdescent : baseEnd_8210481 < baseStart_8210481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210489 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 1, 1, 3]
def baseStart_8210489 : Nat := 118140960795 + 8210489 * 2 ^ 59
def prefixEnd_8210489 : Nat := 4983230072969 + 3 ^ 40 * 8210489 * 2
def baseEnd_8210489 : Nat := 4215927265453032157728155

theorem tailTrace_8210489 : CollatzResearch.WordTrace tailWord_8210489 prefixEnd_8210489 4215927265453032157728155 := by
  unfold tailWord_8210489
  simp only [CollatzResearch.WordTrace]
  refine ⟨299461135551808067728290521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199640757034538711818860347 299461135551808067728290521)
  ·
    refine ⟨224595851663856050796217891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299461135551808067728290521 224595851663856050796217891)
    ·
      refine ⟨336893777495784076194326837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224595851663856050796217891 336893777495784076194326837)
      ·
        refine ⟨31583791640229757143218141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336893777495784076194326837 31583791640229757143218141)
        ·
          refine ⟨11843921865086158928706803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31583791640229757143218141 11843921865086158928706803)
          ·
            refine ⟨17765882797629238393060205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843921865086158928706803 17765882797629238393060205)
            ·
              refine ⟨6662206049110964397397577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17765882797629238393060205 6662206049110964397397577)
              ·
                refine ⟨4996654536833223298048183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662206049110964397397577 4996654536833223298048183)
                ·
                  refine ⟨7494981805249834947072275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996654536833223298048183 7494981805249834947072275)
                  ·
                    refine ⟨11242472707874752420608413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7494981805249834947072275 11242472707874752420608413)
                    ·
                      refine ⟨4215927265453032157728155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242472707874752420608413 4215927265453032157728155)
                      ·
                        rfl

theorem cell23_8210489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_8210489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210489 prefixEnd_8210489 := by exact prefixLift 8210489
  have htrace : WordTrace (prefixWord ++ tailWord_8210489) baseStart_8210489 baseEnd_8210489 := by
    simpa [prefixWord, tailWord_8210489, baseEnd_8210489] using wordTrace_append hprefix tailTrace_8210489
  have hstable : (prefixWord ++ tailWord_8210489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210489).length < 2 ^ (prefixWord ++ tailWord_8210489).sum := by decide
  have hdescent : baseEnd_8210489 < baseStart_8210489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210495 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 3, 2, 2]
def baseStart_8210495 : Nat := 118140960795 + 8210495 * 2 ^ 59
def prefixEnd_8210495 : Nat := 4983230072969 + 3 ^ 40 * 8210495 * 2
def baseEnd_8210495 : Nat := 4215930346336959134253127

theorem tailTrace_8210495 : CollatzResearch.WordTrace tailWord_8210495 prefixEnd_8210495 4215930346336959134253127 := by
  unfold tailWord_8210495
  simp only [CollatzResearch.WordTrace]
  refine ⟨299461354389786330753008939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199640902926524220502005959 299461354389786330753008939)
  ·
    refine ⟨449192031584679496129513409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299461354389786330753008939 449192031584679496129513409)
    ·
      refine ⟨336894023688509622097135057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449192031584679496129513409 336894023688509622097135057)
      ·
        refine ⟨252670517766382216572851293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336894023688509622097135057 252670517766382216572851293)
        ·
          refine ⟨94751444162393331214819235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252670517766382216572851293 94751444162393331214819235)
          ·
            refine ⟨142127166243589996822228853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94751444162393331214819235 142127166243589996822228853)
            ·
              refine ⟨13324421835336562202083955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142127166243589996822228853 13324421835336562202083955)
              ·
                refine ⟨19986632753004843303125933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324421835336562202083955 19986632753004843303125933)
                ·
                  refine ⟨7494987282376816238672225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19986632753004843303125933 7494987282376816238672225)
                  ·
                    refine ⟨5621240461782612179004169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7494987282376816238672225 5621240461782612179004169)
                    ·
                      refine ⟨4215930346336959134253127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621240461782612179004169 4215930346336959134253127)
                      ·
                        rfl

theorem cell23_8210495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_8210495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210495 prefixEnd_8210495 := by exact prefixLift 8210495
  have htrace : WordTrace (prefixWord ++ tailWord_8210495) baseStart_8210495 baseEnd_8210495 := by
    simpa [prefixWord, tailWord_8210495, baseEnd_8210495] using wordTrace_append hprefix tailTrace_8210495
  have hstable : (prefixWord ++ tailWord_8210495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210495).length < 2 ^ (prefixWord ++ tailWord_8210495).sum := by decide
  have hdescent : baseEnd_8210495 < baseStart_8210495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210525 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_8210525 : Nat := 118140960795 + 8210525 * 2 ^ 59
def prefixEnd_8210525 : Nat := 4983230072969 + 3 ^ 40 * 8210525 * 2
def baseEnd_8210525 : Nat := 4215945750756594016877989

theorem tailTrace_8210525 : CollatzResearch.WordTrace tailWord_8210525 prefixEnd_8210525 4215945750756594016877989 := by
  unfold tailWord_8210525
  simp only [CollatzResearch.WordTrace]
  refine ⟨299462448579677645876601029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199641632386451763917734019 299462448579677645876601029)
  ·
    refine ⟨56149209108689558601862693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299462448579677645876601029 56149209108689558601862693)
    ·
      refine ⟨10527976707879292237849255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56149209108689558601862693 10527976707879292237849255)
      ·
        refine ⟨15791965061818938356773883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527976707879292237849255 15791965061818938356773883)
        ·
          refine ⟨23687947592728407535160825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15791965061818938356773883 23687947592728407535160825)
          ·
            refine ⟨17765960694546305651370619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23687947592728407535160825 17765960694546305651370619)
            ·
              refine ⟨26648941041819458477055929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17765960694546305651370619 26648941041819458477055929)
              ·
                refine ⟨19986705781364593857791947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26648941041819458477055929 19986705781364593857791947)
                ·
                  refine ⟨29980058672046890786687921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19986705781364593857791947 29980058672046890786687921)
                  ·
                    refine ⟨22485044004035168090015941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29980058672046890786687921 22485044004035168090015941)
                    ·
                      refine ⟨4215945750756594016877989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22485044004035168090015941 4215945750756594016877989)
                      ·
                        rfl

theorem cell23_8210525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_8210525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210525 prefixEnd_8210525 := by exact prefixLift 8210525
  have htrace : WordTrace (prefixWord ++ tailWord_8210525) baseStart_8210525 baseEnd_8210525 := by
    simpa [prefixWord, tailWord_8210525, baseEnd_8210525] using wordTrace_append hprefix tailTrace_8210525
  have hstable : (prefixWord ++ tailWord_8210525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210525).length < 2 ^ (prefixWord ++ tailWord_8210525).sum := by decide
  have hdescent : baseEnd_8210525 < baseStart_8210525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210528 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_8210528 : Nat := 118140960795 + 8210528 * 2 ^ 59
def prefixEnd_8210528 : Nat := 4983230072969 + 3 ^ 40 * 8210528 * 2
def baseEnd_8210528 : Nat := 4215947291198557505140475

theorem tailTrace_8210528 : CollatzResearch.WordTrace tailWord_8210528 prefixEnd_8210528 4215947291198557505140475 := by
  unfold tailWord_8210528
  simp only [CollatzResearch.WordTrace]
  refine ⟨149731278999333388694480119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199641705332444518259306825 149731278999333388694480119)
  ·
    refine ⟨224596918499000083041720179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149731278999333388694480119 224596918499000083041720179)
    ·
      refine ⟨336895377748500124562580269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224596918499000083041720179 336895377748500124562580269)
      ·
        refine ⟨126335766655687546710967601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336895377748500124562580269 126335766655687546710967601)
        ·
          refine ⟨94751824991765660033225701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126335766655687546710967601 94751824991765660033225701)
          ·
            refine ⟨17765967185956061256229819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94751824991765660033225701 17765967185956061256229819)
            ·
              refine ⟨26648950778934091884344729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17765967185956061256229819 26648950778934091884344729)
              ·
                refine ⟨19986713084200568913258547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26648950778934091884344729 19986713084200568913258547)
                ·
                  refine ⟨29980069626300853369887821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19986713084200568913258547 29980069626300853369887821)
                  ·
                    refine ⟨11242526109862820013707933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29980069626300853369887821 11242526109862820013707933)
                    ·
                      refine ⟨4215947291198557505140475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242526109862820013707933 4215947291198557505140475)
                      ·
                        rfl

theorem cell23_8210528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_8210528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210528 prefixEnd_8210528 := by exact prefixLift 8210528
  have htrace : WordTrace (prefixWord ++ tailWord_8210528) baseStart_8210528 baseEnd_8210528 := by
    simpa [prefixWord, tailWord_8210528, baseEnd_8210528] using wordTrace_append hprefix tailTrace_8210528
  have hstable : (prefixWord ++ tailWord_8210528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210528).length < 2 ^ (prefixWord ++ tailWord_8210528).sum := by decide
  have hdescent : baseEnd_8210528 < baseStart_8210528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210545 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_8210545 : Nat := 118140960795 + 8210545 * 2 ^ 59
def prefixEnd_8210545 : Nat := 4983230072969 + 3 ^ 40 * 8210545 * 2
def baseEnd_8210545 : Nat := 4215956020369683938627897

theorem tailTrace_8210545 : CollatzResearch.WordTrace tailWord_8210545 prefixEnd_8210545 4215956020369683938627897 := by
  unfold tailWord_8210545
  simp only [CollatzResearch.WordTrace]
  refine ⟨299463178039605189292329089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199642118693070126194886059 299463178039605189292329089)
  ·
    refine ⟨224597383529703891969246817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299463178039605189292329089 224597383529703891969246817)
    ·
      refine ⟨168448037647277918976935113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224597383529703891969246817 168448037647277918976935113)
      ·
        refine ⟨126336028235458439232701335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168448037647277918976935113 126336028235458439232701335)
        ·
          refine ⟨189504042353187658849052003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126336028235458439232701335 189504042353187658849052003)
          ·
            refine ⟨284256063529781488273578005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189504042353187658849052003 284256063529781488273578005)
            ·
              refine ⟨13324502977958507262823969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284256063529781488273578005 13324502977958507262823969)
              ·
                refine ⟨9993377233468880447117977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13324502977958507262823969 9993377233468880447117977)
                ·
                  refine ⟨7495032925101660335338483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993377233468880447117977 7495032925101660335338483)
                  ·
                    refine ⟨11242549387652490503007725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495032925101660335338483 11242549387652490503007725)
                    ·
                      refine ⟨4215956020369683938627897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242549387652490503007725 4215956020369683938627897)
                      ·
                        rfl

theorem cell23_8210545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_8210545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210545 prefixEnd_8210545 := by exact prefixLift 8210545
  have htrace : WordTrace (prefixWord ++ tailWord_8210545) baseStart_8210545 baseEnd_8210545 := by
    simpa [prefixWord, tailWord_8210545, baseEnd_8210545] using wordTrace_append hprefix tailTrace_8210545
  have hstable : (prefixWord ++ tailWord_8210545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210545).length < 2 ^ (prefixWord ++ tailWord_8210545).sum := by decide
  have hdescent : baseEnd_8210545 < baseStart_8210545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210546 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_8210546 : Nat := 118140960795 + 8210546 * 2 ^ 59
def prefixEnd_8210546 : Nat := 4983230072969 + 3 ^ 40 * 8210546 * 2
def baseEnd_8210546 : Nat := 4215956533850338434715393

theorem tailTrace_8210546 : CollatzResearch.WordTrace tailWord_8210546 prefixEnd_8210546 4215956533850338434715393 := by
  unfold tailWord_8210546
  simp only [CollatzResearch.WordTrace]
  refine ⟨74865803628150391615778873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199642143008401044308743661 74865803628150391615778873)
  ·
    refine ⟨56149352721112793711834155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74865803628150391615778873 56149352721112793711834155)
    ·
      refine ⟨84224029081669190567751233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149352721112793711834155 84224029081669190567751233)
      ·
        refine ⟨63168021811251892925813425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84224029081669190567751233 63168021811251892925813425)
        ·
          refine ⟨47376016358438919694360069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63168021811251892925813425 47376016358438919694360069)
          ·
            refine ⟨8883003067207297442692513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47376016358438919694360069 8883003067207297442692513)
            ·
              refine ⟨6662252300405473082019385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8883003067207297442692513 6662252300405473082019385)
              ·
                refine ⟨4996689225304104811514539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662252300405473082019385 4996689225304104811514539)
                ·
                  refine ⟨7495033837956157217271809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996689225304104811514539 7495033837956157217271809)
                  ·
                    refine ⟨5621275378467117912953857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7495033837956157217271809 5621275378467117912953857)
                    ·
                      refine ⟨4215956533850338434715393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621275378467117912953857 4215956533850338434715393)
                      ·
                        rfl

theorem cell23_8210546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_8210546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210546 prefixEnd_8210546 := by exact prefixLift 8210546
  have htrace : WordTrace (prefixWord ++ tailWord_8210546) baseStart_8210546 baseEnd_8210546 := by
    simpa [prefixWord, tailWord_8210546, baseEnd_8210546] using wordTrace_append hprefix tailTrace_8210546
  have hstable : (prefixWord ++ tailWord_8210546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210546).length < 2 ^ (prefixWord ++ tailWord_8210546).sum := by decide
  have hdescent : baseEnd_8210546 < baseStart_8210546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210551 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_8210551 : Nat := 118140960795 + 8210551 * 2 ^ 59
def prefixEnd_8210551 : Nat := 4983230072969 + 3 ^ 40 * 8210551 * 2
def baseEnd_8210551 : Nat := 4215959101253610915152869

theorem tailTrace_8210551 : CollatzResearch.WordTrace tailWord_8210551 prefixEnd_8210551 4215959101253610915152869 := by
  unfold tailWord_8210551
  simp only [CollatzResearch.WordTrace]
  refine ⟨299463396877583452317047507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199642264585055634878031671 299463396877583452317047507)
  ·
    refine ⟨449195095316375178475571261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299463396877583452317047507 449195095316375178475571261)
    ·
      refine ⟨168448160743640691928339223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449195095316375178475571261 168448160743640691928339223)
      ·
        refine ⟨252672241115461037892508835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168448160743640691928339223 252672241115461037892508835)
        ·
          refine ⟨379008361673191556838763253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252672241115461037892508835 379008361673191556838763253)
          ·
            refine ⟨35532033906861708453634055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379008361673191556838763253 35532033906861708453634055)
            ·
              refine ⟨53298050860292562680451083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35532033906861708453634055 53298050860292562680451083)
              ·
                refine ⟨79947076290438844020676625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53298050860292562680451083 79947076290438844020676625)
                ·
                  refine ⟨59960307217829133015507469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79947076290438844020676625 59960307217829133015507469)
                  ·
                    refine ⟨22485115206685924880815301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59960307217829133015507469 22485115206685924880815301)
                    ·
                      refine ⟨4215959101253610915152869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22485115206685924880815301 4215959101253610915152869)
                      ·
                        rfl

theorem cell23_8210551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_8210551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210551 prefixEnd_8210551 := by exact prefixLift 8210551
  have htrace : WordTrace (prefixWord ++ tailWord_8210551) baseStart_8210551 baseEnd_8210551 := by
    simpa [prefixWord, tailWord_8210551, baseEnd_8210551] using wordTrace_append hprefix tailTrace_8210551
  have hstable : (prefixWord ++ tailWord_8210551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210551).length < 2 ^ (prefixWord ++ tailWord_8210551).sum := by decide
  have hdescent : baseEnd_8210551 < baseStart_8210551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210581 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_8210581 : Nat := 118140960795 + 8210581 * 2 ^ 59
def prefixEnd_8210581 : Nat := 4983230072969 + 3 ^ 40 * 8210581 * 2
def baseEnd_8210581 : Nat := 4215974505673245797777731

theorem tailTrace_8210581 : CollatzResearch.WordTrace tailWord_8210581 prefixEnd_8210581 4215974505673245797777731 := by
  unfold tailWord_8210581
  simp only [CollatzResearch.WordTrace]
  refine ⟨299464491067474767440639597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199642994044983178293759731 299464491067474767440639597)
  ·
    refine ⟨112299184150303037790239849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299464491067474767440639597 112299184150303037790239849)
    ·
      refine ⟨84224388112727278342679887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112299184150303037790239849 84224388112727278342679887)
      ·
        refine ⟨126336582169090917514019831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84224388112727278342679887 126336582169090917514019831)
        ·
          refine ⟨189504873253636376271029747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126336582169090917514019831 189504873253636376271029747)
          ·
            refine ⟨284257309880454564406544621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189504873253636376271029747 284257309880454564406544621)
            ·
              refine ⟨106596491205170461652454233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284257309880454564406544621 106596491205170461652454233)
              ·
                refine ⟨79947368403877846239340675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106596491205170461652454233 79947368403877846239340675)
                ·
                  refine ⟨119921052605816769359011013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79947368403877846239340675 119921052605816769359011013)
                  ·
                    refine ⟨22485197363590644254814565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119921052605816769359011013 22485197363590644254814565)
                    ·
                      refine ⟨4215974505673245797777731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22485197363590644254814565 4215974505673245797777731)
                      ·
                        rfl

theorem cell23_8210581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_8210581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210581 prefixEnd_8210581 := by exact prefixLift 8210581
  have htrace : WordTrace (prefixWord ++ tailWord_8210581) baseStart_8210581 baseEnd_8210581 := by
    simpa [prefixWord, tailWord_8210581, baseEnd_8210581] using wordTrace_append hprefix tailTrace_8210581
  have hstable : (prefixWord ++ tailWord_8210581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210581).length < 2 ^ (prefixWord ++ tailWord_8210581).sum := by decide
  have hdescent : baseEnd_8210581 < baseStart_8210581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210589 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_8210589 : Nat := 118140960795 + 8210589 * 2 ^ 59
def prefixEnd_8210589 : Nat := 4983230072969 + 3 ^ 40 * 8210589 * 2
def baseEnd_8210589 : Nat := 4215978613518481766477695

theorem tailTrace_8210589 : CollatzResearch.WordTrace tailWord_8210589 prefixEnd_8210589 4215978613518481766477695 := by
  unfold tailWord_8210589
  simp only [CollatzResearch.WordTrace]
  refine ⟨299464782851445784806930821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199643188567630523204620547 299464782851445784806930821)
  ·
    refine ⟨56149646784646084651299529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299464782851445784806930821 56149646784646084651299529)
    ·
      refine ⟨42112235088484563488474647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56149646784646084651299529 42112235088484563488474647)
      ·
        refine ⟨63168352632726845232711971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42112235088484563488474647 63168352632726845232711971)
        ·
          refine ⟨94752528949090267849067957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63168352632726845232711971 94752528949090267849067957)
          ·
            refine ⟨8883049588977212610850121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94752528949090267849067957 8883049588977212610850121)
            ·
              refine ⟨6662287191732909458137591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8883049588977212610850121 6662287191732909458137591)
              ·
                refine ⟨9993430787599364187206387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662287191732909458137591 9993430787599364187206387)
                ·
                  refine ⟨14990146181399046280809581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993430787599364187206387 14990146181399046280809581)
                  ·
                    refine ⟨5621304818024642355303593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14990146181399046280809581 5621304818024642355303593)
                    ·
                      refine ⟨4215978613518481766477695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621304818024642355303593 4215978613518481766477695)
                      ·
                        rfl

theorem cell23_8210589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_8210589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210589 prefixEnd_8210589 := by exact prefixLift 8210589
  have htrace : WordTrace (prefixWord ++ tailWord_8210589) baseStart_8210589 baseEnd_8210589 := by
    simpa [prefixWord, tailWord_8210589, baseEnd_8210589] using wordTrace_append hprefix tailTrace_8210589
  have hstable : (prefixWord ++ tailWord_8210589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210589).length < 2 ^ (prefixWord ++ tailWord_8210589).sum := by decide
  have hdescent : baseEnd_8210589 < baseStart_8210589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210618 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_8210618 : Nat := 118140960795 + 8210618 * 2 ^ 59
def prefixEnd_8210618 : Nat := 4983230072969 + 3 ^ 40 * 8210618 * 2
def baseEnd_8210618 : Nat := 4215993504457462153015061

theorem tailTrace_8210618 : CollatzResearch.WordTrace tailWord_8210618 prefixEnd_8210618 4215993504457462153015061 := by
  unfold tailWord_8210618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74866460142085180689934127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199643893712227148506491005 74866460142085180689934127)
  ·
    refine ⟨112299690213127771034901191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74866460142085180689934127 112299690213127771034901191)
    ·
      refine ⟨168449535319691656552351787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112299690213127771034901191 168449535319691656552351787)
      ·
        refine ⟨252674302979537484828527681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168449535319691656552351787 252674302979537484828527681)
        ·
          refine ⟨189505727234653113621395761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252674302979537484828527681 189505727234653113621395761)
          ·
            refine ⟨142129295425989835216046821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189505727234653113621395761 142129295425989835216046821)
            ·
              refine ⟨26649242892373094103008779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142129295425989835216046821 26649242892373094103008779)
              ·
                refine ⟨39973864338559641154513169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26649242892373094103008779 39973864338559641154513169)
                ·
                  refine ⟨29980398253919730865884877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39973864338559641154513169 29980398253919730865884877)
                  ·
                    refine ⟨11242649345219899074706829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29980398253919730865884877 11242649345219899074706829)
                    ·
                      refine ⟨4215993504457462153015061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242649345219899074706829 4215993504457462153015061)
                      ·
                        rfl

theorem cell23_8210618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_8210618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210618 prefixEnd_8210618 := by exact prefixLift 8210618
  have htrace : WordTrace (prefixWord ++ tailWord_8210618) baseStart_8210618 baseEnd_8210618 := by
    simpa [prefixWord, tailWord_8210618, baseEnd_8210618] using wordTrace_append hprefix tailTrace_8210618
  have hstable : (prefixWord ++ tailWord_8210618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210618).length < 2 ^ (prefixWord ++ tailWord_8210618).sum := by decide
  have hdescent : baseEnd_8210618 < baseStart_8210618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210631 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_8210631 : Nat := 118140960795 + 8210631 * 2 ^ 59
def prefixEnd_8210631 : Nat := 4983230072969 + 3 ^ 40 * 8210631 * 2
def baseEnd_8210631 : Nat := 4216000179705970602152501

theorem tailTrace_8210631 : CollatzResearch.WordTrace tailWord_8210631 prefixEnd_8210631 4216000179705970602152501 := by
  unfold tailWord_8210631
  simp only [CollatzResearch.WordTrace]
  refine ⟨299466314717293625979959747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199644209811529083986639831 299466314717293625979959747)
  ·
    refine ⟨449199472075940438969939621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299466314717293625979959747 449199472075940438969939621)
    ·
      refine ⟨84224901014238832306863679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449199472075940438969939621 84224901014238832306863679)
      ·
        refine ⟨126337351521358248460295519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84224901014238832306863679 126337351521358248460295519)
        ·
          refine ⟨189506027282037372690443279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126337351521358248460295519 189506027282037372690443279)
          ·
            refine ⟨284259040923056059035664919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189506027282037372690443279 284259040923056059035664919)
            ·
              refine ⟨426388561384584088553497379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284259040923056059035664919 426388561384584088553497379)
              ·
                refine ⟨639582842076876132830246069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426388561384584088553497379 639582842076876132830246069)
                ·
                  refine ⟨59960891444707137452835569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639582842076876132830246069 59960891444707137452835569)
                  ·
                    refine ⟨44970668583530353089626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59960891444707137452835569 44970668583530353089626677)
                    ·
                      refine ⟨4216000179705970602152501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44970668583530353089626677 4216000179705970602152501)
                      ·
                        rfl

theorem cell23_8210631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_8210631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210631 prefixEnd_8210631 := by exact prefixLift 8210631
  have htrace : WordTrace (prefixWord ++ tailWord_8210631) baseStart_8210631 baseEnd_8210631 := by
    simpa [prefixWord, tailWord_8210631, baseEnd_8210631] using wordTrace_append hprefix tailTrace_8210631
  have hstable : (prefixWord ++ tailWord_8210631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210631).length < 2 ^ (prefixWord ++ tailWord_8210631).sum := by decide
  have hdescent : baseEnd_8210631 < baseStart_8210631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210638 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_8210638 : Nat := 118140960795 + 8210638 * 2 ^ 59
def prefixEnd_8210638 : Nat := 4983230072969 + 3 ^ 40 * 8210638 * 2
def baseEnd_8210638 : Nat := 1405334591356850691588323

theorem tailTrace_8210638 : CollatzResearch.WordTrace tailWord_8210638 prefixEnd_8210638 1405334591356850691588323 := by
  unfold tailWord_8210638
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433321253533533271933071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199644380018845510783643045 37433321253533533271933071)
  ·
    refine ⟨56149981880300299907899607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37433321253533533271933071 56149981880300299907899607)
    ·
      refine ⟨84224972820450449861849411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149981880300299907899607 84224972820450449861849411)
      ·
        refine ⟨126337459230675674792774117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84224972820450449861849411 126337459230675674792774117)
        ·
          refine ⟨23688273605751689023645147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126337459230675674792774117 23688273605751689023645147)
          ·
            refine ⟨35532410408627533535467721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23688273605751689023645147 35532410408627533535467721)
            ·
              refine ⟨26649307806470650151600791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35532410408627533535467721 26649307806470650151600791)
              ·
                refine ⟨39973961709705975227401187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26649307806470650151600791 39973961709705975227401187)
                ·
                  refine ⟨59960942564558962841101781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39973961709705975227401187 59960942564558962841101781)
                  ·
                    refine ⟨1405334591356850691588323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59960942564558962841101781 1405334591356850691588323)
                    ·
                      rfl

theorem cell23_8210638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_8210638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210638 prefixEnd_8210638 := by exact prefixLift 8210638
  have htrace : WordTrace (prefixWord ++ tailWord_8210638) baseStart_8210638 baseEnd_8210638 := by
    simpa [prefixWord, tailWord_8210638, baseEnd_8210638] using wordTrace_append hprefix tailTrace_8210638
  have hstable : (prefixWord ++ tailWord_8210638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210638).length < 2 ^ (prefixWord ++ tailWord_8210638).sum := by decide
  have hdescent : baseEnd_8210638 < baseStart_8210638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210642 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_8210642 : Nat := 118140960795 + 8210642 * 2 ^ 59
def prefixEnd_8210642 : Nat := 4983230072969 + 3 ^ 40 * 8210642 * 2
def baseEnd_8210642 : Nat := 468445091999241117679439

theorem tailTrace_8210642 : CollatzResearch.WordTrace tailWord_8210642 prefixEnd_8210642 468445091999241117679439 := by
  unfold tailWord_8210642
  simp only [CollatzResearch.WordTrace]
  refine ⟨74866678980063443714652545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199644477280169183239073453 74866678980063443714652545)
  ·
    refine ⟨56150009235047582785989409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74866678980063443714652545 56150009235047582785989409)
    ·
      refine ⟨42112506926285687089492057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56150009235047582785989409 42112506926285687089492057)
      ·
        refine ⟨31584380194714265317119043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42112506926285687089492057 31584380194714265317119043)
        ·
          refine ⟨47376570292071397975678565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31584380194714265317119043 47376570292071397975678565)
          ·
            refine ⟨8883106929763387120439731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47376570292071397975678565 8883106929763387120439731)
            ·
              refine ⟨13324660394645080680659597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883106929763387120439731 13324660394645080680659597)
              ·
                refine ⟨4996747647991905255247349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324660394645080680659597 4996747647991905255247349)
                ·
                  refine ⟨468445091999241117679439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996747647991905255247349 468445091999241117679439)
                  ·
                    rfl

theorem cell23_8210642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_8210642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210642 prefixEnd_8210642 := by exact prefixLift 8210642
  have htrace : WordTrace (prefixWord ++ tailWord_8210642) baseStart_8210642 baseEnd_8210642 := by
    simpa [prefixWord, tailWord_8210642, baseEnd_8210642] using wordTrace_append hprefix tailTrace_8210642
  have hstable : (prefixWord ++ tailWord_8210642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210642).length < 2 ^ (prefixWord ++ tailWord_8210642).sum := by decide
  have hdescent : baseEnd_8210642 < baseStart_8210642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210659 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 5]
def baseStart_8210659 : Nat := 118140960795 + 8210659 * 2 ^ 59
def prefixEnd_8210659 : Nat := 4983230072969 + 3 ^ 40 * 8210659 * 2
def baseEnd_8210659 : Nat := 468446061907144054733597

theorem tailTrace_8210659 : CollatzResearch.WordTrace tailWord_8210659 prefixEnd_8210659 468446061907144054733597 := by
  unfold tailWord_8210659
  simp only [CollatzResearch.WordTrace]
  refine ⟨299467335961192186761979031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199644890640794791174652687 299467335961192186761979031)
  ·
    refine ⟨449201003941788280142968547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299467335961192186761979031 449201003941788280142968547)
    ·
      refine ⟨673801505912682420214452821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449201003941788280142968547 673801505912682420214452821)
      ·
        refine ⟨7896111397414247111888119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 673801505912682420214452821 7896111397414247111888119)
        ·
          refine ⟨11844167096121370667832179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896111397414247111888119 11844167096121370667832179)
          ·
            refine ⟨17766250644182056001748269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844167096121370667832179 17766250644182056001748269)
            ·
              refine ⟨6662343991568271000655601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17766250644182056001748269 6662343991568271000655601)
              ·
                refine ⟨4996757993676203250491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662343991568271000655601 4996757993676203250491701)
                ·
                  refine ⟨468446061907144054733597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996757993676203250491701 468446061907144054733597)
                  ·
                    rfl

theorem cell23_8210659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 5].length) (baseStart_8210659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210659 prefixEnd_8210659 := by exact prefixLift 8210659
  have htrace : WordTrace (prefixWord ++ tailWord_8210659) baseStart_8210659 baseEnd_8210659 := by
    simpa [prefixWord, tailWord_8210659, baseEnd_8210659] using wordTrace_append hprefix tailTrace_8210659
  have hstable : (prefixWord ++ tailWord_8210659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210659).length < 2 ^ (prefixWord ++ tailWord_8210659).sum := by decide
  have hdescent : baseEnd_8210659 < baseStart_8210659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210681 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 10]
def baseStart_8210681 : Nat := 118140960795 + 8210681 * 2 ^ 59
def prefixEnd_8210681 : Nat := 4983230072969 + 3 ^ 40 * 8210681 * 2
def baseEnd_8210681 : Nat := 468447317082077267391919

theorem tailTrace_8210681 : CollatzResearch.WordTrace tailWord_8210681 prefixEnd_8210681 468447317082077267391919 := by
  unfold tailWord_8210681
  simp only [CollatzResearch.WordTrace]
  refine ⟨299468138367112484519279897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199645425578074989679519931 299468138367112484519279897)
  ·
    refine ⟨224601103775334363389459923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299468138367112484519279897 224601103775334363389459923)
    ·
      refine ⟨336901655663001545084189885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224601103775334363389459923 336901655663001545084189885)
      ·
        refine ⟨126338120873625579406571207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336901655663001545084189885 126338120873625579406571207)
        ·
          refine ⟨189507181310438369109856811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126338120873625579406571207 189507181310438369109856811)
          ·
            refine ⟨284260771965657553664785217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189507181310438369109856811 284260771965657553664785217)
            ·
              refine ⟨213195578974243165248588913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284260771965657553664785217 213195578974243165248588913)
              ·
                refine ⟨159896684230682373936441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213195578974243165248588913 159896684230682373936441685)
                ·
                  refine ⟨468447317082077267391919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159896684230682373936441685 468447317082077267391919)
                  ·
                    rfl

theorem cell23_8210681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_8210681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210681 prefixEnd_8210681 := by exact prefixLift 8210681
  have htrace : WordTrace (prefixWord ++ tailWord_8210681) baseStart_8210681 baseEnd_8210681 := by
    simpa [prefixWord, tailWord_8210681, baseEnd_8210681] using wordTrace_append hprefix tailTrace_8210681
  have hstable : (prefixWord ++ tailWord_8210681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210681).length < 2 ^ (prefixWord ++ tailWord_8210681).sum := by decide
  have hdescent : baseEnd_8210681 < baseStart_8210681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210692 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_8210692 : Nat := 118140960795 + 8210692 * 2 ^ 59
def prefixEnd_8210692 : Nat := 4983230072969 + 3 ^ 40 * 8210692 * 2
def baseEnd_8210692 : Nat := 4216031502025894863489721

theorem tailTrace_8210692 : CollatzResearch.WordTrace tailWord_8210692 prefixEnd_8210692 4216031502025894863489721 := by
  unfold tailWord_8210692
  simp only [CollatzResearch.WordTrace]
  refine ⟨149734269785036316698965165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199645693046715088931953553 149734269785036316698965165)
  ·
    refine ⟨56150351169388618762111937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149734269785036316698965165 56150351169388618762111937)
    ·
      refine ⟨42112763377041464071583953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56150351169388618762111937 42112763377041464071583953)
      ·
        refine ⟨31584572532781098053687965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42112763377041464071583953 31584572532781098053687965)
        ·
          refine ⟨11844214699792911770132987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31584572532781098053687965 11844214699792911770132987)
          ·
            refine ⟨17766322049689367655199481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11844214699792911770132987 17766322049689367655199481)
            ·
              refine ⟨13324741537267025741399611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17766322049689367655199481 13324741537267025741399611)
              ·
                refine ⟨19987112305900538612099417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324741537267025741399611 19987112305900538612099417)
                ·
                  refine ⟨14990334229425403959074563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19987112305900538612099417 14990334229425403959074563)
                  ·
                    refine ⟨22485501344138105938611845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14990334229425403959074563 22485501344138105938611845)
                    ·
                      refine ⟨4216031502025894863489721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22485501344138105938611845 4216031502025894863489721)
                      ·
                        rfl

theorem cell23_8210692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_8210692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210692 prefixEnd_8210692 := by exact prefixLift 8210692
  have htrace : WordTrace (prefixWord ++ tailWord_8210692) baseStart_8210692 baseEnd_8210692 := by
    simpa [prefixWord, tailWord_8210692, baseEnd_8210692] using wordTrace_append hprefix tailTrace_8210692
  have hstable : (prefixWord ++ tailWord_8210692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210692).length < 2 ^ (prefixWord ++ tailWord_8210692).sum := by decide
  have hdescent : baseEnd_8210692 < baseStart_8210692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210702 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_8210702 : Nat := 118140960795 + 8210702 * 2 ^ 59
def prefixEnd_8210702 : Nat := 4983230072969 + 3 ^ 40 * 8210702 * 2
def baseEnd_8210702 : Nat := 1405345545610813274788225

theorem tailTrace_8210702 : CollatzResearch.WordTrace tailWord_8210702 prefixEnd_8210702 1405345545610813274788225 := by
  unfold tailWord_8210702
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433613037504550638224295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199645936200024270070529573 37433613037504550638224295)
  ·
    refine ⟨56150419556256825957336443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37433613037504550638224295 56150419556256825957336443)
    ·
      refine ⟨84225629334385238936004665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56150419556256825957336443 84225629334385238936004665)
      ·
        refine ⟨63169222000788929202003499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84225629334385238936004665 63169222000788929202003499)
        ·
          refine ⟨94753833001183393803005249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63169222000788929202003499 94753833001183393803005249)
          ·
            refine ⟨71065374750887545352253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94753833001183393803005249 71065374750887545352253937)
            ·
              refine ⟨53299031063165659014190453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71065374750887545352253937 53299031063165659014190453)
              ·
                refine ⟨4996784162171780532580355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53299031063165659014190453 4996784162171780532580355)
                ·
                  refine ⟨7495176243257670798870533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996784162171780532580355 7495176243257670798870533)
                  ·
                    refine ⟨1405345545610813274788225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495176243257670798870533 1405345545610813274788225)
                    ·
                      rfl

theorem cell23_8210702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_8210702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210702 prefixEnd_8210702 := by exact prefixLift 8210702
  have htrace : WordTrace (prefixWord ++ tailWord_8210702) baseStart_8210702 baseEnd_8210702 := by
    simpa [prefixWord, tailWord_8210702, baseEnd_8210702] using wordTrace_append hprefix tailTrace_8210702
  have hstable : (prefixWord ++ tailWord_8210702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210702).length < 2 ^ (prefixWord ++ tailWord_8210702).sum := by decide
  have hdescent : baseEnd_8210702 < baseStart_8210702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210719 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 1, 4]
def baseStart_8210719 : Nat := 118140960795 + 8210719 * 2 ^ 59
def prefixEnd_8210719 : Nat := 4983230072969 + 3 ^ 40 * 8210719 * 2
def baseEnd_8210719 : Nat := 1405348455334522085950699

theorem tailTrace_8210719 : CollatzResearch.WordTrace tailWord_8210719 prefixEnd_8210719 1405348455334522085950699 := by
  unfold tailWord_8210719
  simp only [CollatzResearch.WordTrace]
  refine ⟨299469524340974817009163211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199646349560649878006108807 299469524340974817009163211)
  ·
    refine ⟨449204286511462225513744817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299469524340974817009163211 449204286511462225513744817)
    ·
      refine ⟨336903214883596669135308613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449204286511462225513744817 336903214883596669135308613)
      ·
        refine ⟨63169352790674375462870365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336903214883596669135308613 63169352790674375462870365)
        ·
          refine ⟨23688507296502890798576387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63169352790674375462870365 23688507296502890798576387)
          ·
            refine ⟨35532760944754336197864581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23688507296502890798576387 35532760944754336197864581)
            ·
              refine ⟨6662392677141438037099609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35532760944754336197864581 6662392677141438037099609)
              ·
                refine ⟨4996794507856078527824707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662392677141438037099609 4996794507856078527824707)
                ·
                  refine ⟨7495191761784117791737061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996794507856078527824707 7495191761784117791737061)
                  ·
                    refine ⟨1405348455334522085950699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495191761784117791737061 1405348455334522085950699)
                    ·
                      rfl

theorem cell23_8210719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_8210719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210719 prefixEnd_8210719 := by exact prefixLift 8210719
  have htrace : WordTrace (prefixWord ++ tailWord_8210719) baseStart_8210719 baseEnd_8210719 := by
    simpa [prefixWord, tailWord_8210719, baseEnd_8210719] using wordTrace_append hprefix tailTrace_8210719
  have hstable : (prefixWord ++ tailWord_8210719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210719).length < 2 ^ (prefixWord ++ tailWord_8210719).sum := by decide
  have hdescent : baseEnd_8210719 < baseStart_8210719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210735 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 4, 3, 2]
def baseStart_8210735 : Nat := 118140960795 + 8210735 * 2 ^ 59
def prefixEnd_8210735 : Nat := 4983230072969 + 3 ^ 40 * 8210735 * 2
def baseEnd_8210735 : Nat := 4216053581694038195252023

theorem tailTrace_8210735 : CollatzResearch.WordTrace tailWord_8210735 prefixEnd_8210735 4216053581694038195252023 := by
  unfold tailWord_8210735
  simp only [CollatzResearch.WordTrace]
  refine ⟨299470107908916851741745659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199646738605944567827830439 299470107908916851741745659)
  ·
    refine ⟨449205161863375277612618489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299470107908916851741745659 449205161863375277612618489)
    ·
      refine ⟨336903871397531458209463867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449205161863375277612618489 336903871397531458209463867)
      ·
        refine ⟨505355807096297187314195801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336903871397531458209463867 505355807096297187314195801)
        ·
          refine ⟨379016855322222890485646851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505355807096297187314195801 379016855322222890485646851)
          ·
            refine ⟨568525282983334335728470277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379016855322222890485646851 568525282983334335728470277)
            ·
              refine ⟨106598490559375187949088177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568525282983334335728470277 106598490559375187949088177)
              ·
                refine ⟨79948867919531390961816133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106598490559375187949088177 79948867919531390961816133)
                ·
                  refine ⟨14990412734912135805340525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79948867919531390961816133 14990412734912135805340525)
                  ·
                    refine ⟨5621404775592050927002697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14990412734912135805340525 5621404775592050927002697)
                    ·
                      refine ⟨4216053581694038195252023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621404775592050927002697 4216053581694038195252023)
                      ·
                        rfl

theorem cell23_8210735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3, 2].length) (baseStart_8210735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210735 prefixEnd_8210735 := by exact prefixLift 8210735
  have htrace : WordTrace (prefixWord ++ tailWord_8210735) baseStart_8210735 baseEnd_8210735 := by
    simpa [prefixWord, tailWord_8210735, baseEnd_8210735] using wordTrace_append hprefix tailTrace_8210735
  have hstable : (prefixWord ++ tailWord_8210735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210735).length < 2 ^ (prefixWord ++ tailWord_8210735).sum := by decide
  have hdescent : baseEnd_8210735 < baseStart_8210735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210745 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_8210745 : Nat := 118140960795 + 8210745 * 2 ^ 59
def prefixEnd_8210745 : Nat := 4983230072969 + 3 ^ 40 * 8210745 * 2
def baseEnd_8210745 : Nat := 1405352905500194385375659

theorem tailTrace_8210745 : CollatzResearch.WordTrace tailWord_8210745 prefixEnd_8210745 1405352905500194385375659 := by
  unfold tailWord_8210745
  simp only [CollatzResearch.WordTrace]
  refine ⟨299470472638880623449609689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199646981759253748966406459 299470472638880623449609689)
  ·
    refine ⟨224602854479160467587207267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299470472638880623449609689 224602854479160467587207267)
    ·
      refine ⟨336904281718740701380810901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224602854479160467587207267 336904281718740701380810901)
      ·
        refine ⟨15792388205565970377225511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336904281718740701380810901 15792388205565970377225511)
        ·
          refine ⟨23688582308348955565838267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15792388205565970377225511 23688582308348955565838267)
          ·
            refine ⟨35532873462523433348757401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23688582308348955565838267 35532873462523433348757401)
            ·
              refine ⟨26649655096892575011568051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35532873462523433348757401 26649655096892575011568051)
              ·
                refine ⟨39974482645338862517352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26649655096892575011568051 39974482645338862517352077)
                ·
                  refine ⟨14990430992002073444007029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39974482645338862517352077 14990430992002073444007029)
                  ·
                    refine ⟨1405352905500194385375659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14990430992002073444007029 1405352905500194385375659)
                    ·
                      rfl

theorem cell23_8210745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_8210745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210745 prefixEnd_8210745 := by exact prefixLift 8210745
  have htrace : WordTrace (prefixWord ++ tailWord_8210745) baseStart_8210745 baseEnd_8210745 := by
    simpa [prefixWord, tailWord_8210745, baseEnd_8210745] using wordTrace_append hprefix tailTrace_8210745
  have hstable : (prefixWord ++ tailWord_8210745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210745).length < 2 ^ (prefixWord ++ tailWord_8210745).sum := by decide
  have hdescent : baseEnd_8210745 < baseStart_8210745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210759 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_8210759 : Nat := 118140960795 + 8210759 * 2 ^ 59
def prefixEnd_8210759 : Nat := 4983230072969 + 3 ^ 40 * 8210759 * 2
def baseEnd_8210759 : Nat := 4216065905229746101351913

theorem tailTrace_8210759 : CollatzResearch.WordTrace tailWord_8210759 prefixEnd_8210759 4216065905229746101351913 := by
  unfold tailWord_8210759
  simp only [CollatzResearch.WordTrace]
  refine ⟨299470983260829903840619331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199647322173886602560412887 299470983260829903840619331)
  ·
    refine ⟨449206474891244855760928997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299470983260829903840619331 449206474891244855760928997)
    ·
      refine ⟨84226214042108410455174187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449206474891244855760928997 84226214042108410455174187)
      ·
        refine ⟨126339321063162615682761281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84226214042108410455174187 126339321063162615682761281)
        ·
          refine ⟨94754490797371961762070961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126339321063162615682761281 94754490797371961762070961)
          ·
            refine ⟨71065868098028971321553221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94754490797371961762070961 71065868098028971321553221)
            ·
              refine ⟨13324850268380432122791229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71065868098028971321553221 13324850268380432122791229)
              ·
                refine ⟨4996818850642662046046711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13324850268380432122791229 4996818850642662046046711)
                ·
                  refine ⟨7495228275963993069070067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996818850642662046046711 7495228275963993069070067)
                  ·
                    refine ⟨11242842413945989603605101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495228275963993069070067 11242842413945989603605101)
                    ·
                      refine ⟨4216065905229746101351913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242842413945989603605101 4216065905229746101351913)
                      ·
                        rfl

theorem cell23_8210759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_8210759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210759 prefixEnd_8210759 := by exact prefixLift 8210759
  have htrace : WordTrace (prefixWord ++ tailWord_8210759) baseStart_8210759 baseEnd_8210759 := by
    simpa [prefixWord, tailWord_8210759, baseEnd_8210759] using wordTrace_append hprefix tailTrace_8210759
  have hstable : (prefixWord ++ tailWord_8210759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210759).length < 2 ^ (prefixWord ++ tailWord_8210759).sum := by decide
  have hdescent : baseEnd_8210759 < baseStart_8210759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210775 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 4, 4]
def baseStart_8210775 : Nat := 118140960795 + 8210775 * 2 ^ 59
def prefixEnd_8210775 : Nat := 4983230072969 + 3 ^ 40 * 8210775 * 2
def baseEnd_8210775 : Nat := 1405358040306739346250613

theorem tailTrace_8210775 : CollatzResearch.WordTrace tailWord_8210775 prefixEnd_8210775 1405358040306739346250613 := by
  unfold tailWord_8210775
  simp only [CollatzResearch.WordTrace]
  refine ⟨299471566828771938573201779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199647711219181292382134519 299471566828771938573201779)
  ·
    refine ⟨449207350243157907859802669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299471566828771938573201779 449207350243157907859802669)
    ·
      refine ⟨168452756341184215447426001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449207350243157907859802669 168452756341184215447426001)
      ·
        refine ⟨126339567255888161585569501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168452756341184215447426001 126339567255888161585569501)
        ·
          refine ⟨47377337720958060594588563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126339567255888161585569501 47377337720958060594588563)
          ·
            refine ⟨71066006581437090891882845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47377337720958060594588563 71066006581437090891882845)
            ·
              refine ⟨26649752468038909084456067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71066006581437090891882845 26649752468038909084456067)
              ·
                refine ⟨39974628702058363626684101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26649752468038909084456067 39974628702058363626684101)
                ·
                  refine ⟨7495242881635943180003269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39974628702058363626684101 7495242881635943180003269)
                  ·
                    refine ⟨1405358040306739346250613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495242881635943180003269 1405358040306739346250613)
                    ·
                      rfl

theorem cell23_8210775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_8210775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210775 prefixEnd_8210775 := by exact prefixLift 8210775
  have htrace : WordTrace (prefixWord ++ tailWord_8210775) baseStart_8210775 baseEnd_8210775 := by
    simpa [prefixWord, tailWord_8210775, baseEnd_8210775] using wordTrace_append hprefix tailTrace_8210775
  have hstable : (prefixWord ++ tailWord_8210775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210775).length < 2 ^ (prefixWord ++ tailWord_8210775).sum := by decide
  have hdescent : baseEnd_8210775 < baseStart_8210775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210778 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_8210778 : Nat := 118140960795 + 8210778 * 2 ^ 59
def prefixEnd_8210778 : Nat := 4983230072969 + 3 ^ 40 * 8210778 * 2
def baseEnd_8210778 : Nat := 4216075661362181527014325

theorem tailTrace_8210778 : CollatzResearch.WordTrace tailWord_8210778 prefixEnd_8210778 4216075661362181527014325 := by
  unfold tailWord_8210778
  simp only [CollatzResearch.WordTrace]
  refine ⟨74867919061940267521390247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199647784165174046723707325 74867919061940267521390247)
  ·
    refine ⟨112301878592910401282085371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74867919061940267521390247 112301878592910401282085371)
    ·
      refine ⟨168452817889365601923128057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112301878592910401282085371 168452817889365601923128057)
      ·
        refine ⟨126339613417024201442346043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168452817889365601923128057 126339613417024201442346043)
        ·
          refine ⟨189509420125536302163519065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126339613417024201442346043 189509420125536302163519065)
          ·
            refine ⟨142132065094152226622639299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189509420125536302163519065 142132065094152226622639299)
            ·
              refine ⟨213198097641228339933958949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142132065094152226622639299 213198097641228339933958949)
              ·
                refine ⟨39974643307730313737617303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213198097641228339933958949 39974643307730313737617303)
                ·
                  refine ⟨59961964961595470606425955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39974643307730313737617303 59961964961595470606425955)
                  ·
                    refine ⟨89942947442393205909638933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59961964961595470606425955 89942947442393205909638933)
                    ·
                      refine ⟨4216075661362181527014325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89942947442393205909638933 4216075661362181527014325)
                      ·
                        rfl

theorem cell23_8210778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_8210778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210778 prefixEnd_8210778 := by exact prefixLift 8210778
  have htrace : WordTrace (prefixWord ++ tailWord_8210778) baseStart_8210778 baseEnd_8210778 := by
    simpa [prefixWord, tailWord_8210778, baseEnd_8210778] using wordTrace_append hprefix tailTrace_8210778
  have hstable : (prefixWord ++ tailWord_8210778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210778).length < 2 ^ (prefixWord ++ tailWord_8210778).sum := by decide
  have hdescent : baseEnd_8210778 < baseStart_8210778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210788 : List Nat := [2, 3, 1, 1, 3, 1, 2, 10]
def baseStart_8210788 : Nat := 118140960795 + 8210788 * 2 ^ 59
def prefixEnd_8210788 : Nat := 4983230072969 + 3 ^ 40 * 8210788 * 2
def baseEnd_8210788 : Nat := 156151140598841721773677

theorem tailTrace_8210788 : CollatzResearch.WordTrace tailWord_8210788 prefixEnd_8210788 156151140598841721773677 := by
  unfold tailWord_8210788
  simp only [CollatzResearch.WordTrace]
  refine ⟨149736020488862420896712509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199648027318483227862283345 149736020488862420896712509)
  ·
    refine ⟨56151007683323407836267191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149736020488862420896712509 56151007683323407836267191)
    ·
      refine ⟨84226511524985111754400787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56151007683323407836267191 84226511524985111754400787)
      ·
        refine ⟨126339767287477667631601181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84226511524985111754400787 126339767287477667631601181)
        ·
          refine ⟨47377412732804125361850443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126339767287477667631601181 47377412732804125361850443)
          ·
            refine ⟨71066119099206188042775665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47377412732804125361850443 71066119099206188042775665)
            ·
              refine ⟨53299589324404641032081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71066119099206188042775665 53299589324404641032081749)
              ·
                refine ⟨156151140598841721773677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53299589324404641032081749 156151140598841721773677)
                ·
                  rfl

theorem cell23_8210788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 10].length) (baseStart_8210788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210788 prefixEnd_8210788 := by exact prefixLift 8210788
  have htrace : WordTrace (prefixWord ++ tailWord_8210788) baseStart_8210788 baseEnd_8210788 := by
    simpa [prefixWord, tailWord_8210788, baseEnd_8210788] using wordTrace_append hprefix tailTrace_8210788
  have hstable : (prefixWord ++ tailWord_8210788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210788).length < 2 ^ (prefixWord ++ tailWord_8210788).sum := by decide
  have hdescent : baseEnd_8210788 < baseStart_8210788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210792 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_8210792 : Nat := 118140960795 + 8210792 * 2 ^ 59
def prefixEnd_8210792 : Nat := 4983230072969 + 3 ^ 40 * 8210792 * 2
def baseEnd_8210792 : Nat := 1405360950030448157413087

theorem tailTrace_8210792 : CollatzResearch.WordTrace tailWord_8210792 prefixEnd_8210792 1405360950030448157413087 := by
  unfold tailWord_8210792
  simp only [CollatzResearch.WordTrace]
  refine ⟨149736093434855175238285315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199648124579806900317713753 149736093434855175238285315)
  ·
    refine ⟨224604140152282762857427973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149736093434855175238285315 224604140152282762857427973)
    ·
      refine ⟨42113276278553018035767745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224604140152282762857427973 42113276278553018035767745)
      ·
        refine ⟨31584957208914763526825809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42113276278553018035767745 31584957208914763526825809)
        ·
          refine ⟨23688717906686072645119357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31584957208914763526825809 23688717906686072645119357)
          ·
            refine ⟨8883269215007277241919759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23688717906686072645119357 8883269215007277241919759)
            ·
              refine ⟨13324903822510915862879639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883269215007277241919759 13324903822510915862879639)
              ·
                refine ⟨19987355733766373794319459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324903822510915862879639 19987355733766373794319459)
                ·
                  refine ⟨29981033600649560691479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19987355733766373794319459 29981033600649560691479189)
                  ·
                    refine ⟨1405360950030448157413087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29981033600649560691479189 1405360950030448157413087)
                    ·
                      rfl

theorem cell23_8210792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_8210792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210792 prefixEnd_8210792 := by exact prefixLift 8210792
  have htrace : WordTrace (prefixWord ++ tailWord_8210792) baseStart_8210792 baseEnd_8210792 := by
    simpa [prefixWord, tailWord_8210792, baseEnd_8210792] using wordTrace_append hprefix tailTrace_8210792
  have hstable : (prefixWord ++ tailWord_8210792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210792).length < 2 ^ (prefixWord ++ tailWord_8210792).sum := by decide
  have hdescent : baseEnd_8210792 < baseStart_8210792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210802 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_8210802 : Nat := 118140960795 + 8210802 * 2 ^ 59
def prefixEnd_8210802 : Nat := 4983230072969 + 3 ^ 40 * 8210802 * 2
def baseEnd_8210802 : Nat := 4216087984897889433114215

theorem tailTrace_8210802 : CollatzResearch.WordTrace tailWord_8210802 prefixEnd_8210802 4216087984897889433114215 := by
  unfold tailWord_8210802
  simp only [CollatzResearch.WordTrace]
  refine ⟨74868137899918530546108665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199648367733116081456289773 74868137899918530546108665)
  ·
    refine ⟨56151103424938897909581499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74868137899918530546108665 56151103424938897909581499)
    ·
      refine ⟨84226655137408346864372249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56151103424938897909581499 84226655137408346864372249)
      ·
        refine ⟨63169991353056260148279187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84226655137408346864372249 63169991353056260148279187)
        ·
          refine ⟨94754987029584390222418781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63169991353056260148279187 94754987029584390222418781)
          ·
            refine ⟨35533120136094146333407043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94754987029584390222418781 35533120136094146333407043)
            ·
              refine ⟨53299680204141219500110565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35533120136094146333407043 53299680204141219500110565)
              ·
                refine ⟨9993690038276478656270731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53299680204141219500110565 9993690038276478656270731)
                ·
                  refine ⟨14990535057414717984406097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993690038276478656270731 14990535057414717984406097)
                  ·
                    refine ⟨11242901293061038488304573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14990535057414717984406097 11242901293061038488304573)
                    ·
                      refine ⟨4216087984897889433114215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11242901293061038488304573 4216087984897889433114215)
                      ·
                        rfl

theorem cell23_8210802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_8210802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210802 prefixEnd_8210802 := by exact prefixLift 8210802
  have htrace : WordTrace (prefixWord ++ tailWord_8210802) baseStart_8210802 baseEnd_8210802 := by
    simpa [prefixWord, tailWord_8210802, baseEnd_8210802] using wordTrace_append hprefix tailTrace_8210802
  have hstable : (prefixWord ++ tailWord_8210802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210802).length < 2 ^ (prefixWord ++ tailWord_8210802).sum := by decide
  have hdescent : baseEnd_8210802 < baseStart_8210802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210805 : List Nat := [1, 3, 4, 1, 2, 2, 1, 9]
def baseStart_8210805 : Nat := 118140960795 + 8210805 * 2 ^ 59
def prefixEnd_8210805 : Nat := 4983230072969 + 3 ^ 40 * 8210805 * 2
def baseEnd_8210805 : Nat := 156151463901476034125063

theorem tailTrace_8210805 : CollatzResearch.WordTrace tailWord_8210805 prefixEnd_8210805 156151463901476034125063 := by
  unfold tailWord_8210805
  simp only [CollatzResearch.WordTrace]
  refine ⟨299472661018663253696793869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199648440679108835797862579 299472661018663253696793869)
  ·
    refine ⟨112302247881998720136297701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299472661018663253696793869 112302247881998720136297701)
    ·
      refine ⟨21056671477874760025555819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112302247881998720136297701 21056671477874760025555819)
      ·
        refine ⟨31585007216812140038333729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056671477874760025555819 31585007216812140038333729)
        ·
          refine ⟨23688755412609105028750297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31585007216812140038333729 23688755412609105028750297)
          ·
            refine ⟨17766566559456828771562723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23688755412609105028750297 17766566559456828771562723)
            ·
              refine ⟨26649849839185243157344085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17766566559456828771562723 26649849839185243157344085)
              ·
                refine ⟨156151463901476034125063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26649849839185243157344085 156151463901476034125063)
                ·
                  rfl

theorem cell23_8210805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 9].length) (baseStart_8210805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210805 prefixEnd_8210805 := by exact prefixLift 8210805
  have htrace : WordTrace (prefixWord ++ tailWord_8210805) baseStart_8210805 baseEnd_8210805 := by
    simpa [prefixWord, tailWord_8210805, baseEnd_8210805] using wordTrace_append hprefix tailTrace_8210805
  have hstable : (prefixWord ++ tailWord_8210805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210805).length < 2 ^ (prefixWord ++ tailWord_8210805).sum := by decide
  have hdescent : baseEnd_8210805 < baseStart_8210805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210889 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 2, 2, 2]
def baseStart_8210889 : Nat := 118140960795 + 8210889 * 2 ^ 59
def prefixEnd_8210889 : Nat := 4983230072969 + 3 ^ 40 * 8210889 * 2
def baseEnd_8210889 : Nat := 4216132657714830592726315

theorem tailTrace_8210889 : CollatzResearch.WordTrace tailWord_8210889 prefixEnd_8210889 4216132657714830592726315 := by
  unfold tailWord_8210889
  simp only [CollatzResearch.WordTrace]
  refine ⟨299475724750358936042851721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199650483166905957361901147 299475724750358936042851721)
  ·
    refine ⟨224606793562769202032138791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299475724750358936042851721 224606793562769202032138791)
    ·
      refine ⟨336910190344153803048208187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224606793562769202032138791 336910190344153803048208187)
      ·
        refine ⟨505365285516230704572312281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336910190344153803048208187 505365285516230704572312281)
        ·
          refine ⟨379023964137173028429234211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505365285516230704572312281 379023964137173028429234211)
          ·
            refine ⟨568535946205759542643851317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379023964137173028429234211 568535946205759542643851317)
            ·
              refine ⟨53300244956789957122861061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 568535946205759542643851317 53300244956789957122861061)
              ·
                refine ⟨9993795929398116960536449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53300244956789957122861061 9993795929398116960536449)
                ·
                  refine ⟨7495346947048587720402337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993795929398116960536449 7495346947048587720402337)
                  ·
                    refine ⟨5621510210286440790301753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7495346947048587720402337 5621510210286440790301753)
                    ·
                      refine ⟨4216132657714830592726315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621510210286440790301753 4216132657714830592726315)
                      ·
                        rfl

theorem cell23_8210889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2, 2].length) (baseStart_8210889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210889 prefixEnd_8210889 := by exact prefixLift 8210889
  have htrace : WordTrace (prefixWord ++ tailWord_8210889) baseStart_8210889 baseEnd_8210889 := by
    simpa [prefixWord, tailWord_8210889, baseEnd_8210889] using wordTrace_append hprefix tailTrace_8210889
  have hstable : (prefixWord ++ tailWord_8210889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210889).length < 2 ^ (prefixWord ++ tailWord_8210889).sum := by decide
  have hdescent : baseEnd_8210889 < baseStart_8210889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210957 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_8210957 : Nat := 118140960795 + 8210957 * 2 ^ 59
def prefixEnd_8210957 : Nat := 4983230072969 + 3 ^ 40 * 8210957 * 2
def baseEnd_8210957 : Nat := 4216167574399336326676003

theorem tailTrace_8210957 : CollatzResearch.WordTrace tailWord_8210957 prefixEnd_8210957 4216167574399336326676003 := by
  unfold tailWord_8210957
  simp only [CollatzResearch.WordTrace]
  refine ⟨299478204914112583656327125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199652136609408389104218083 299478204914112583656327125)
  ·
    refine ⟨7019020427674513679445167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 299478204914112583656327125 7019020427674513679445167)
    ·
      refine ⟨10528530641511770519167751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7019020427674513679445167 10528530641511770519167751)
      ·
        refine ⟨15792795962267655778751627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10528530641511770519167751 15792795962267655778751627)
        ·
          refine ⟨23689193943401483668127441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15792795962267655778751627 23689193943401483668127441)
          ·
            refine ⟨17766895457551112751095581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23689193943401483668127441 17766895457551112751095581)
            ·
              refine ⟨6662585796581667281660843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17766895457551112751095581 6662585796581667281660843)
              ·
                refine ⟨9993878694872500922491265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662585796581667281660843 9993878694872500922491265)
                ·
                  refine ⟨7495409021154375691868449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9993878694872500922491265 7495409021154375691868449)
                  ·
                    refine ⟨5621556765865781768901337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7495409021154375691868449 5621556765865781768901337)
                    ·
                      refine ⟨4216167574399336326676003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621556765865781768901337 4216167574399336326676003)
                      ·
                        rfl

theorem cell23_8210957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_8210957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210957 prefixEnd_8210957 := by exact prefixLift 8210957
  have htrace : WordTrace (prefixWord ++ tailWord_8210957) baseStart_8210957 baseEnd_8210957 := by
    simpa [prefixWord, tailWord_8210957, baseEnd_8210957] using wordTrace_append hprefix tailTrace_8210957
  have hstable : (prefixWord ++ tailWord_8210957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210957).length < 2 ^ (prefixWord ++ tailWord_8210957).sum := by decide
  have hdescent : baseEnd_8210957 < baseStart_8210957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8210975 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_8210975 : Nat := 118140960795 + 8210975 * 2 ^ 59
def prefixEnd_8210975 : Nat := 4983230072969 + 3 ^ 40 * 8210975 * 2
def baseEnd_8210975 : Nat := 4216176817051117256250919

theorem tailTrace_8210975 : CollatzResearch.WordTrace tailWord_8210975 prefixEnd_8210975 4216176817051117256250919 := by
  unfold tailWord_8210975
  simp only [CollatzResearch.WordTrace]
  refine ⟨299478861428047372730482379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199652574285364915153654919 299478861428047372730482379)
  ·
    refine ⟨449218292142071059095723569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299478861428047372730482379 449218292142071059095723569)
    ·
      refine ⟨336913719106553294321792677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449218292142071059095723569 336913719106553294321792677)
      ·
        refine ⟨63171322332478742685336127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336913719106553294321792677 63171322332478742685336127)
        ·
          refine ⟨94756983498718114028004191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63171322332478742685336127 94756983498718114028004191)
          ·
            refine ⟨142135475248077171042006287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94756983498718114028004191 142135475248077171042006287)
            ·
              refine ⟨213203212872115756563009431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142135475248077171042006287 213203212872115756563009431)
              ·
                refine ⟨319804819308173634844514147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213203212872115756563009431 319804819308173634844514147)
                ·
                  refine ⟨479707228962260452266771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319804819308173634844514147 479707228962260452266771221)
                  ·
                    refine ⟨22486276357605958700004901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 479707228962260452266771221 22486276357605958700004901)
                    ·
                      refine ⟨4216176817051117256250919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22486276357605958700004901 4216176817051117256250919)
                      ·
                        rfl

theorem cell23_8210975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_8210975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8210975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8210975 prefixEnd_8210975 := by exact prefixLift 8210975
  have htrace : WordTrace (prefixWord ++ tailWord_8210975) baseStart_8210975 baseEnd_8210975 := by
    simpa [prefixWord, tailWord_8210975, baseEnd_8210975] using wordTrace_append hprefix tailTrace_8210975
  have hstable : (prefixWord ++ tailWord_8210975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8210975).length < 2 ^ (prefixWord ++ tailWord_8210975).sum := by decide
  have hdescent : baseEnd_8210975 < baseStart_8210975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8210975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211029 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_8211029 : Nat := 118140960795 + 8211029 * 2 ^ 59
def prefixEnd_8211029 : Nat := 4983230072969 + 3 ^ 40 * 8211029 * 2
def baseEnd_8211029 : Nat := 4216204545006460044975671

theorem tailTrace_8211029 : CollatzResearch.WordTrace tailWord_8211029 prefixEnd_8211029 4216204545006460044975671 := by
  unfold tailWord_8211029
  simp only [CollatzResearch.WordTrace]
  refine ⟨299480830969851739952948141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199653887313234493301965427 299480830969851739952948141)
  ·
    refine ⟨112305311613694402482355553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299480830969851739952948141 112305311613694402482355553)
    ·
      refine ⟨84228983710270801861766665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112305311613694402482355553 84228983710270801861766665)
      ·
        refine ⟨63171737782703101396324999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84228983710270801861766665 63171737782703101396324999)
        ·
          refine ⟨94757606674054652094487499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63171737782703101396324999 94757606674054652094487499)
          ·
            refine ⟨142136410011081978141731249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94757606674054652094487499 142136410011081978141731249)
            ·
              refine ⟨106602307508311483606298437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142136410011081978141731249 106602307508311483606298437)
              ·
                refine ⟨19987932657808403176180957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106602307508311483606298437 19987932657808403176180957)
                ·
                  refine ⟨7495474746678151191067859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19987932657808403176180957 7495474746678151191067859)
                  ·
                    refine ⟨11243212120017226786601789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495474746678151191067859 11243212120017226786601789)
                    ·
                      refine ⟨4216204545006460044975671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11243212120017226786601789 4216204545006460044975671)
                      ·
                        rfl

theorem cell23_8211029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_8211029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211029 prefixEnd_8211029 := by exact prefixLift 8211029
  have htrace : WordTrace (prefixWord ++ tailWord_8211029) baseStart_8211029 baseEnd_8211029 := by
    simpa [prefixWord, tailWord_8211029, baseEnd_8211029] using wordTrace_append hprefix tailTrace_8211029
  have hstable : (prefixWord ++ tailWord_8211029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211029).length < 2 ^ (prefixWord ++ tailWord_8211029).sum := by decide
  have hdescent : baseEnd_8211029 < baseStart_8211029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211063 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 1, 1, 3]
def baseStart_8211063 : Nat := 118140960795 + 8211063 * 2 ^ 59
def prefixEnd_8211063 : Nat := 4983230072969 + 3 ^ 40 * 8211063 * 2
def baseEnd_8211063 : Nat := 4216222003348712911950515

theorem tailTrace_8211063 : CollatzResearch.WordTrace tailWord_8211063 prefixEnd_8211063 4216222003348712911950515 := by
  unfold tailWord_8211063
  simp only [CollatzResearch.WordTrace]
  refine ⟨299482071051728563759685843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199654714034485709173123895 299482071051728563759685843)
  ·
    refine ⟨449223106577592845639528765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299482071051728563759685843 449223106577592845639528765)
    ·
      refine ⟨168458664966597317114823287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449223106577592845639528765 168458664966597317114823287)
      ·
        refine ⟨252687997449895975672234931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168458664966597317114823287 252687997449895975672234931)
        ·
          refine ⟨379031996174843963508352397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252687997449895975672234931 379031996174843963508352397)
          ·
            refine ⟨142136998565566486315632149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379031996174843963508352397 142136998565566486315632149)
            ·
              refine ⟨6662671807760929046045257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142136998565566486315632149 6662671807760929046045257)
              ·
                refine ⟨4997003855820696784533943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6662671807760929046045257 4997003855820696784533943)
                ·
                  refine ⟨7495505783731045176800915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997003855820696784533943 7495505783731045176800915)
                  ·
                    refine ⟨11243258675596567765201373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495505783731045176800915 11243258675596567765201373)
                    ·
                      refine ⟨4216222003348712911950515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11243258675596567765201373 4216222003348712911950515)
                      ·
                        rfl

theorem cell23_8211063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 1, 3].length) (baseStart_8211063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211063 prefixEnd_8211063 := by exact prefixLift 8211063
  have htrace : WordTrace (prefixWord ++ tailWord_8211063) baseStart_8211063 baseEnd_8211063 := by
    simpa [prefixWord, tailWord_8211063, baseEnd_8211063] using wordTrace_append hprefix tailTrace_8211063
  have hstable : (prefixWord ++ tailWord_8211063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211063).length < 2 ^ (prefixWord ++ tailWord_8211063).sum := by decide
  have hdescent : baseEnd_8211063 < baseStart_8211063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211079 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 2, 4]
def baseStart_8211079 : Nat := 118140960795 + 8211079 * 2 ^ 59
def prefixEnd_8211079 : Nat := 4983230072969 + 3 ^ 40 * 8211079 * 2
def baseEnd_8211079 : Nat := 1405410073013061616450147

theorem tailTrace_8211079 : CollatzResearch.WordTrace tailWord_8211079 prefixEnd_8211079 1405410073013061616450147 := by
  unfold tailWord_8211079
  simp only [CollatzResearch.WordTrace]
  refine ⟨299482654619670598492268291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199655103079780398994845527 299482654619670598492268291)
  ·
    refine ⟨449223981929505897738402437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299482654619670598492268291 449223981929505897738402437)
    ·
      refine ⟨84229496611782355825950457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449223981929505897738402437 84229496611782355825950457)
      ·
        refine ⟨63172122458836766869462843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84229496611782355825950457 63172122458836766869462843)
        ·
          refine ⟨94758183688255150304194265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63172122458836766869462843 94758183688255150304194265)
          ·
            refine ⟨71068637766191362728145699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94758183688255150304194265 71068637766191362728145699)
            ·
              refine ⟨106602956649287044092218549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71068637766191362728145699 106602956649287044092218549)
              ·
                refine ⟨9994027185870660383645489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106602956649287044092218549 9994027185870660383645489)
                ·
                  refine ⟨7495520389402995287734117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994027185870660383645489 7495520389402995287734117)
                  ·
                    refine ⟨1405410073013061616450147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495520389402995287734117 1405410073013061616450147)
                    ·
                      rfl

theorem cell23_8211079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_8211079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211079 prefixEnd_8211079 := by exact prefixLift 8211079
  have htrace : WordTrace (prefixWord ++ tailWord_8211079) baseStart_8211079 baseEnd_8211079 := by
    simpa [prefixWord, tailWord_8211079, baseEnd_8211079] using wordTrace_append hprefix tailTrace_8211079
  have hstable : (prefixWord ++ tailWord_8211079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211079).length < 2 ^ (prefixWord ++ tailWord_8211079).sum := by decide
  have hdescent : baseEnd_8211079 < baseStart_8211079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211136 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_8211136 : Nat := 118140960795 + 8211136 * 2 ^ 59
def prefixEnd_8211136 : Nat := 4983230072969 + 3 ^ 40 * 8211136 * 2
def baseEnd_8211136 : Nat := 4216259487436491126337679

theorem tailTrace_8211136 : CollatzResearch.WordTrace tailWord_8211136 prefixEnd_8211136 4216259487436491126337679 := by
  unfold tailWord_8211136
  simp only [CollatzResearch.WordTrace]
  refine ⟨149742366790232048613546631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199656489053642731484728841 149742366790232048613546631)
  ·
    refine ⟨224613550185348072920319947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149742366790232048613546631 224613550185348072920319947)
    ·
      refine ⟨336920325278022109380479921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224613550185348072920319947 336920325278022109380479921)
      ·
        refine ⟨252690243958516582035359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336920325278022109380479921 252690243958516582035359941)
        ·
          refine ⟨47379420742221859131629989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252690243958516582035359941 47379420742221859131629989)
          ·
            refine ⟨8883641389166598587180623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47379420742221859131629989 8883641389166598587180623)
            ·
              refine ⟨13325462083749897880770935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883641389166598587180623 13325462083749897880770935)
              ·
                refine ⟨19988193125624846821156403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13325462083749897880770935 19988193125624846821156403)
                ·
                  refine ⟨29982289688437270231734605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19988193125624846821156403 29982289688437270231734605)
                  ·
                    refine ⟨11243358633163976336900477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29982289688437270231734605 11243358633163976336900477)
                    ·
                      refine ⟨4216259487436491126337679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11243358633163976336900477 4216259487436491126337679)
                      ·
                        rfl

theorem cell23_8211136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_8211136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211136 prefixEnd_8211136 := by exact prefixLift 8211136
  have htrace : WordTrace (prefixWord ++ tailWord_8211136) baseStart_8211136 baseEnd_8211136 := by
    simpa [prefixWord, tailWord_8211136, baseEnd_8211136] using wordTrace_append hprefix tailTrace_8211136
  have hstable : (prefixWord ++ tailWord_8211136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211136).length < 2 ^ (prefixWord ++ tailWord_8211136).sum := by decide
  have hdescent : baseEnd_8211136 < baseStart_8211136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211154 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_8211154 : Nat := 118140960795 + 8211154 * 2 ^ 59
def prefixEnd_8211154 : Nat := 4983230072969 + 3 ^ 40 * 8211154 * 2
def baseEnd_8211154 : Nat := 4216268730088272055912597

theorem tailTrace_8211154 : CollatzResearch.WordTrace tailWord_8211154 prefixEnd_8211154 4216268730088272055912597 := by
  unfold tailWord_8211154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74871347523599721575312129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199656926729599257534165677 74871347523599721575312129)
  ·
    refine ⟨56153510642699791181484097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74871347523599721575312129 56153510642699791181484097)
    ·
      refine ⟨42115132982024843386113073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56153510642699791181484097 42115132982024843386113073)
      ·
        refine ⟨31586349736518632539584805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42115132982024843386113073 31586349736518632539584805)
        ·
          refine ⟨5922440575597243601172151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31586349736518632539584805 5922440575597243601172151)
          ·
            refine ⟨8883660863395865401758227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922440575597243601172151 8883660863395865401758227)
            ·
              refine ⟨13325491295093798102637341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883660863395865401758227 13325491295093798102637341)
              ·
                refine ⟨4997059235660174288489003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13325491295093798102637341 4997059235660174288489003)
                ·
                  refine ⟨7495588853490261432733505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997059235660174288489003 7495588853490261432733505)
                  ·
                    refine ⟨5621691640117696074550129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7495588853490261432733505 5621691640117696074550129)
                    ·
                      refine ⟨4216268730088272055912597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621691640117696074550129 4216268730088272055912597)
                      ·
                        rfl

theorem cell23_8211154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_8211154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211154 prefixEnd_8211154 := by exact prefixLift 8211154
  have htrace : WordTrace (prefixWord ++ tailWord_8211154) baseStart_8211154 baseEnd_8211154 := by
    simpa [prefixWord, tailWord_8211154, baseEnd_8211154] using wordTrace_append hprefix tailTrace_8211154
  have hstable : (prefixWord ++ tailWord_8211154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211154).length < 2 ^ (prefixWord ++ tailWord_8211154).sum := by decide
  have hdescent : baseEnd_8211154 < baseStart_8211154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211249 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_8211249 : Nat := 118140960795 + 8211249 * 2 ^ 59
def prefixEnd_8211249 : Nat := 4983230072969 + 3 ^ 40 * 8211249 * 2
def baseEnd_8211249 : Nat := 4216317510750449184224659

theorem tailTrace_8211249 : CollatzResearch.WordTrace tailWord_8211249 prefixEnd_8211249 4216317510750449184224659 := by
  unfold tailWord_8211249
  simp only [CollatzResearch.WordTrace]
  refine ⟨299488855029054717525956801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199659236686036478350637867 299488855029054717525956801)
  ·
    refine ⟨224616641271791038144467601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299488855029054717525956801 224616641271791038144467601)
    ·
      refine ⟨168462480953843278608350701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224616641271791038144467601 168462480953843278608350701)
      ·
        refine ⟨63173430357691229478131513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168462480953843278608350701 63173430357691229478131513)
        ·
          refine ⟨47380072768268422108598635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63173430357691229478131513 47380072768268422108598635)
          ·
            refine ⟨71070109152402633162897953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47380072768268422108598635 71070109152402633162897953)
            ·
              refine ⟨53302581864301974872173465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71070109152402633162897953 53302581864301974872173465)
              ·
                refine ⟨39976936398226481154130099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53302581864301974872173465 39976936398226481154130099)
                ·
                  refine ⟨59965404597339721731195149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39976936398226481154130099 59965404597339721731195149)
                  ·
                    refine ⟨22487026724002395649198181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59965404597339721731195149 22487026724002395649198181)
                    ·
                      refine ⟨4216317510750449184224659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22487026724002395649198181 4216317510750449184224659)
                      ·
                        rfl

theorem cell23_8211249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_8211249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211249 prefixEnd_8211249 := by exact prefixLift 8211249
  have htrace : WordTrace (prefixWord ++ tailWord_8211249) baseStart_8211249 baseEnd_8211249 := by
    simpa [prefixWord, tailWord_8211249, baseEnd_8211249] using wordTrace_append hprefix tailTrace_8211249
  have hstable : (prefixWord ++ tailWord_8211249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211249).length < 2 ^ (prefixWord ++ tailWord_8211249).sum := by decide
  have hdescent : baseEnd_8211249 < baseStart_8211249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211289 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 8]
def baseStart_8211289 : Nat := 118140960795 + 8211289 * 2 ^ 59
def prefixEnd_8211289 : Nat := 4983230072969 + 3 ^ 40 * 8211289 * 2
def baseEnd_8211289 : Nat := 468482005552958780858275

theorem tailTrace_8211289 : CollatzResearch.WordTrace tailWord_8211289 prefixEnd_8211289 468482005552958780858275 := by
  unfold tailWord_8211289
  simp only [CollatzResearch.WordTrace]
  refine ⟨299490313948909804357412921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199660209299273202904941947 299490313948909804357412921)
  ·
    refine ⟨224617735461682353268059691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299490313948909804357412921 224617735461682353268059691)
    ·
      refine ⟨336926603192523529902089537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224617735461682353268059691 336926603192523529902089537)
      ·
        refine ⟨252694952394392647426567153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336926603192523529902089537 252694952394392647426567153)
        ·
          refine ⟨189521214295794485569925365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252694952394392647426567153 189521214295794485569925365)
          ·
            refine ⟨17767613840230733022180503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189521214295794485569925365 17767613840230733022180503)
            ·
              refine ⟨26651420760346099533270755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17767613840230733022180503 26651420760346099533270755)
              ·
                refine ⟨39977131140519149299906133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26651420760346099533270755 39977131140519149299906133)
                ·
                  refine ⟨468482005552958780858275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39977131140519149299906133 468482005552958780858275)
                  ·
                    rfl

theorem cell23_8211289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_8211289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211289 prefixEnd_8211289 := by exact prefixLift 8211289
  have htrace : WordTrace (prefixWord ++ tailWord_8211289) baseStart_8211289 baseEnd_8211289 := by
    simpa [prefixWord, tailWord_8211289, baseEnd_8211289] using wordTrace_append hprefix tailTrace_8211289
  have hstable : (prefixWord ++ tailWord_8211289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211289).length < 2 ^ (prefixWord ++ tailWord_8211289).sum := by decide
  have hdescent : baseEnd_8211289 < baseStart_8211289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211309 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_8211309 : Nat := 118140960795 + 8211309 * 2 ^ 59
def prefixEnd_8211309 : Nat := 4983230072969 + 3 ^ 40 * 8211309 * 2
def baseEnd_8211309 : Nat := 4216348319589718949474383

theorem tailTrace_8211309 : CollatzResearch.WordTrace tailWord_8211309 prefixEnd_8211309 4216348319589718949474383 := by
  unfold tailWord_8211309
  simp only [CollatzResearch.WordTrace]
  refine ⟨299491043408837347773140981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199660695605891565182093987 299491043408837347773140981)
  ·
    refine ⟨28077285319578501353731967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299491043408837347773140981 28077285319578501353731967)
    ·
      refine ⟨42115927979367752030597951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077285319578501353731967 42115927979367752030597951)
      ·
        refine ⟨63173891969051628045896927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42115927979367752030597951 63173891969051628045896927)
        ·
          refine ⟨94760837953577442068845391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63173891969051628045896927 94760837953577442068845391)
          ·
            refine ⟨142141256930366163103268087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94760837953577442068845391 142141256930366163103268087)
            ·
              refine ⟨213211885395549244654902131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142141256930366163103268087 213211885395549244654902131)
              ·
                refine ⟨319817828093323866982353197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213211885395549244654902131 319817828093323866982353197)
                ·
                  refine ⟨119931685534996450118382449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319817828093323866982353197 119931685534996450118382449)
                  ·
                    refine ⟨89948764151247337588786837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119931685534996450118382449 89948764151247337588786837)
                    ·
                      refine ⟨4216348319589718949474383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89948764151247337588786837 4216348319589718949474383)
                      ·
                        rfl

theorem cell23_8211309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_8211309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211309 prefixEnd_8211309 := by exact prefixLift 8211309
  have htrace : WordTrace (prefixWord ++ tailWord_8211309) baseStart_8211309 baseEnd_8211309 := by
    simpa [prefixWord, tailWord_8211309, baseEnd_8211309] using wordTrace_append hprefix tailTrace_8211309
  have hstable : (prefixWord ++ tailWord_8211309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211309).length < 2 ^ (prefixWord ++ tailWord_8211309).sum := by decide
  have hdescent : baseEnd_8211309 < baseStart_8211309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211319 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 3, 5]
def baseStart_8211319 : Nat := 118140960795 + 8211319 * 2 ^ 59
def prefixEnd_8211319 : Nat := 4983230072969 + 3 ^ 40 * 8211319 * 2
def baseEnd_8211319 : Nat := 1405451151465421303449779

theorem tailTrace_8211319 : CollatzResearch.WordTrace tailWord_8211319 prefixEnd_8211319 1405451151465421303449779 := by
  unfold tailWord_8211319
  simp only [CollatzResearch.WordTrace]
  refine ⟨299491408138801119481005011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199660938759200746320670007 299491408138801119481005011)
  ·
    refine ⟨449237112208201679221507517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299491408138801119481005011 449237112208201679221507517)
    ·
      refine ⟨168463917078075629708065319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449237112208201679221507517 168463917078075629708065319)
      ·
        refine ⟨252695875617113444562097979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168463917078075629708065319 252695875617113444562097979)
        ·
          refine ⟨379043813425670166843146969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252695875617113444562097979 379043813425670166843146969)
          ·
            refine ⟨284282860069252625132360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379043813425670166843146969 284282860069252625132360227)
            ·
              refine ⟨426424290103878937698540341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284282860069252625132360227 426424290103878937698540341)
              ·
                refine ⟨39977277197238650409238157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426424290103878937698540341 39977277197238650409238157)
                ·
                  refine ⟨14991478948964493903464309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39977277197238650409238157 14991478948964493903464309)
                  ·
                    refine ⟨1405451151465421303449779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14991478948964493903464309 1405451151465421303449779)
                    ·
                      rfl

theorem cell23_8211319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_8211319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211319 prefixEnd_8211319 := by exact prefixLift 8211319
  have htrace : WordTrace (prefixWord ++ tailWord_8211319) baseStart_8211319 baseEnd_8211319 := by
    simpa [prefixWord, tailWord_8211319, baseEnd_8211319] using wordTrace_append hprefix tailTrace_8211319
  have hstable : (prefixWord ++ tailWord_8211319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211319).length < 2 ^ (prefixWord ++ tailWord_8211319).sum := by decide
  have hdescent : baseEnd_8211319 < baseStart_8211319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211369 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_8211369 : Nat := 118140960795 + 8211369 * 2 ^ 59
def prefixEnd_8211369 : Nat := 4983230072969 + 3 ^ 40 * 8211369 * 2
def baseEnd_8211369 : Nat := 4216379128428988714724107

theorem tailTrace_8211369 : CollatzResearch.WordTrace tailWord_8211369 prefixEnd_8211369 4216379128428988714724107 := by
  unfold tailWord_8211369
  simp only [CollatzResearch.WordTrace]
  refine ⟨299493231788619978020325161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199662154525746652013550107 299493231788619978020325161)
  ·
    refine ⟨224619923841464983515243871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299493231788619978020325161 224619923841464983515243871)
    ·
      refine ⟨336929885762197475272865807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224619923841464983515243871 336929885762197475272865807)
      ·
        refine ⟨505394828643296212909298711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336929885762197475272865807 505394828643296212909298711)
        ·
          refine ⟨758092242964944319363948067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505394828643296212909298711 758092242964944319363948067)
          ·
            refine ⟨1137138364447416479045922101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758092242964944319363948067 1137138364447416479045922101)
            ·
              refine ⟨106606721666945294910555197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1137138364447416479045922101 106606721666945294910555197)
              ·
                refine ⟨39977520625104485591458199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106606721666945294910555197 39977520625104485591458199)
                ·
                  refine ⟨59966280937656728387187299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39977520625104485591458199 59966280937656728387187299)
                  ·
                    refine ⟨89949421406485092580780949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59966280937656728387187299 89949421406485092580780949)
                    ·
                      refine ⟨4216379128428988714724107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89949421406485092580780949 4216379128428988714724107)
                      ·
                        rfl

theorem cell23_8211369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_8211369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211369 prefixEnd_8211369 := by exact prefixLift 8211369
  have htrace : WordTrace (prefixWord ++ tailWord_8211369) baseStart_8211369 baseEnd_8211369 := by
    simpa [prefixWord, tailWord_8211369, baseEnd_8211369] using wordTrace_append hprefix tailTrace_8211369
  have hstable : (prefixWord ++ tailWord_8211369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211369).length < 2 ^ (prefixWord ++ tailWord_8211369).sum := by decide
  have hdescent : baseEnd_8211369 < baseStart_8211369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211386 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_8211386 : Nat := 118140960795 + 8211386 * 2 ^ 59
def prefixEnd_8211386 : Nat := 4983230072969 + 3 ^ 40 * 8211386 * 2
def baseEnd_8211386 : Nat := 4216387857600115148211529

theorem tailTrace_8211386 : CollatzResearch.WordTrace tailWord_8211386 prefixEnd_8211386 4216387857600115148211529 := by
  unfold tailWord_8211386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74873462957389597480923503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199662567886372259949129341 74873462957389597480923503)
  ·
    refine ⟨112310194436084396221385255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74873462957389597480923503 112310194436084396221385255)
    ·
      refine ⟨168465291654126594332077883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112310194436084396221385255 168465291654126594332077883)
      ·
        refine ⟨252697937481189891498116825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168465291654126594332077883 252697937481189891498116825)
        ·
          refine ⟨189523453110892418623587619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252697937481189891498116825 189523453110892418623587619)
          ·
            refine ⟨284285179666338627935381429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189523453110892418623587619 284285179666338627935381429)
            ·
              refine ⟨26651735593719246368942009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284285179666338627935381429 26651735593719246368942009)
              ·
                refine ⟨19988801695289434776706507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26651735593719246368942009 19988801695289434776706507)
                ·
                  refine ⟨29983202542934152165059761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19988801695289434776706507 29983202542934152165059761)
                  ·
                    refine ⟨22487401907200614123794821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29983202542934152165059761 22487401907200614123794821)
                    ·
                      refine ⟨4216387857600115148211529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22487401907200614123794821 4216387857600115148211529)
                      ·
                        rfl

theorem cell23_8211386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_8211386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211386 prefixEnd_8211386 := by exact prefixLift 8211386
  have htrace : WordTrace (prefixWord ++ tailWord_8211386) baseStart_8211386 baseEnd_8211386 := by
    simpa [prefixWord, tailWord_8211386, baseEnd_8211386] using wordTrace_append hprefix tailTrace_8211386
  have hstable : (prefixWord ++ tailWord_8211386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211386).length < 2 ^ (prefixWord ++ tailWord_8211386).sum := by decide
  have hdescent : baseEnd_8211386 < baseStart_8211386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211390 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_8211390 : Nat := 118140960795 + 8211390 * 2 ^ 59
def prefixEnd_8211390 : Nat := 4983230072969 + 3 ^ 40 * 8211390 * 2
def baseEnd_8211390 : Nat := 4216389911522733132561511

theorem tailTrace_8211390 : CollatzResearch.WordTrace tailWord_8211390 prefixEnd_8211390 4216389911522733132561511 := by
  unfold tailWord_8211390
  simp only [CollatzResearch.WordTrace]
  refine ⟨37436749715192987325854953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199662665147695932404559749 37436749715192987325854953)
  ·
    refine ⟨28077562286394740494391215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37436749715192987325854953 28077562286394740494391215)
    ·
      refine ⟨42116343429592110741586823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28077562286394740494391215 42116343429592110741586823)
      ·
        refine ⟨63174515144388166112380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42116343429592110741586823 63174515144388166112380235)
        ·
          refine ⟨94761772716582249168570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63174515144388166112380235 94761772716582249168570353)
          ·
            refine ⟨71071329537436686876427765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94761772716582249168570353 71071329537436686876427765)
            ·
              refine ⟨6662937144134689394665103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71071329537436686876427765 6662937144134689394665103)
              ·
                refine ⟨9994405716202034091997655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662937144134689394665103 9994405716202034091997655)
                ·
                  refine ⟨14991608574303051137996483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994405716202034091997655 14991608574303051137996483)
                  ·
                    refine ⟨22487412861454576706994725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14991608574303051137996483 22487412861454576706994725)
                    ·
                      refine ⟨4216389911522733132561511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22487412861454576706994725 4216389911522733132561511)
                      ·
                        rfl

theorem cell23_8211390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_8211390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211390 prefixEnd_8211390 := by exact prefixLift 8211390
  have htrace : WordTrace (prefixWord ++ tailWord_8211390) baseStart_8211390 baseEnd_8211390 := by
    simpa [prefixWord, tailWord_8211390, baseEnd_8211390] using wordTrace_append hprefix tailTrace_8211390
  have hstable : (prefixWord ++ tailWord_8211390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211390).length < 2 ^ (prefixWord ++ tailWord_8211390).sum := by decide
  have hdescent : baseEnd_8211390 < baseStart_8211390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211396 : List Nat := [2, 3, 3, 3, 12]
def baseStart_8211396 : Nat := 118140960795 + 8211396 * 2 ^ 59
def prefixEnd_8211396 : Nat := 4983230072969 + 3 ^ 40 * 8211396 * 2
def baseEnd_8211396 : Nat := 5783803830461810849227

theorem tailTrace_8211396 : CollatzResearch.WordTrace tailWord_8211396 prefixEnd_8211396 5783803830461810849227 := by
  unfold tailWord_8211396
  simp only [CollatzResearch.WordTrace]
  refine ⟨149747108279761080815779021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199662811039681441087705361 149747108279761080815779021)
  ·
    refine ⟨56155165604910405305917133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149747108279761080815779021 56155165604910405305917133)
    ·
      refine ⟨21058187101841401989718925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56155165604910405305917133 21058187101841401989718925)
      ·
        refine ⟨7896820163190525746144597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21058187101841401989718925 7896820163190525746144597)
        ·
          refine ⟨5783803830461810849227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7896820163190525746144597 5783803830461810849227)
          ·
            rfl

theorem cell23_8211396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 12].length) (baseStart_8211396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211396 prefixEnd_8211396 := by exact prefixLift 8211396
  have htrace : WordTrace (prefixWord ++ tailWord_8211396) baseStart_8211396 baseEnd_8211396 := by
    simpa [prefixWord, tailWord_8211396, baseEnd_8211396] using wordTrace_append hprefix tailTrace_8211396
  have hstable : (prefixWord ++ tailWord_8211396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211396).length < 2 ^ (prefixWord ++ tailWord_8211396).sum := by decide
  have hdescent : baseEnd_8211396 < baseStart_8211396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211400 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_8211400 : Nat := 118140960795 + 8211400 * 2 ^ 59
def prefixEnd_8211400 : Nat := 4983230072969 + 3 ^ 40 * 8211400 * 2
def baseEnd_8211400 : Nat := 1405465015443092697812155

theorem tailTrace_8211400 : CollatzResearch.WordTrace tailWord_8211400 prefixEnd_8211400 1405465015443092697812155 := by
  unfold tailWord_8211400
  simp only [CollatzResearch.WordTrace]
  refine ⟨149747181225753835157351827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199662908301005113543135769 149747181225753835157351827)
  ·
    refine ⟨224620771838630752736027741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149747181225753835157351827 224620771838630752736027741)
    ·
      refine ⟨84232789439486532276010403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224620771838630752736027741 84232789439486532276010403)
      ·
        refine ⟨126349184159229798414015605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84232789439486532276010403 126349184159229798414015605)
        ·
          refine ⟨11845236014927793601313963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126349184159229798414015605 11845236014927793601313963)
          ·
            refine ⟨17767854022391690401970945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845236014927793601313963 17767854022391690401970945)
            ·
              refine ⟨13325890516793767801478209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17767854022391690401970945 13325890516793767801478209)
              ·
                refine ⟨9994417887595325851108657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13325890516793767801478209 9994417887595325851108657)
                ·
                  refine ⟨7495813415696494388331493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994417887595325851108657 7495813415696494388331493)
                  ·
                    refine ⟨1405465015443092697812155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495813415696494388331493 1405465015443092697812155)
                    ·
                      rfl

theorem cell23_8211400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_8211400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211400 prefixEnd_8211400 := by exact prefixLift 8211400
  have htrace : WordTrace (prefixWord ++ tailWord_8211400) baseStart_8211400 baseEnd_8211400 := by
    simpa [prefixWord, tailWord_8211400, baseEnd_8211400] using wordTrace_append hprefix tailTrace_8211400
  have hstable : (prefixWord ++ tailWord_8211400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211400).length < 2 ^ (prefixWord ++ tailWord_8211400).sum := by decide
  have hdescent : baseEnd_8211400 < baseStart_8211400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211407 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 1, 2, 2]
def baseStart_8211407 : Nat := 118140960795 + 8211407 * 2 ^ 59
def prefixEnd_8211407 : Nat := 4983230072969 + 3 ^ 40 * 8211407 * 2
def baseEnd_8211407 : Nat := 4216398640693859566048933

theorem tailTrace_8211407 : CollatzResearch.WordTrace tailWord_8211407 prefixEnd_8211407 4216398640693859566048933 := by
  unfold tailWord_8211407
  simp only [CollatzResearch.WordTrace]
  refine ⟨299494617762482310510208475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199663078508321540340138983 299494617762482310510208475)
  ·
    refine ⟨449241926643723465765312713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299494617762482310510208475 449241926643723465765312713)
    ·
      refine ⟨336931444982792599323984535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449241926643723465765312713 336931444982792599323984535)
      ·
        refine ⟨505397167474188898985976803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336931444982792599323984535 505397167474188898985976803)
        ·
          refine ⟨758095751211283348478965205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505397167474188898985976803 758095751211283348478965205)
          ·
            refine ⟨17767869169014453479975747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 758095751211283348478965205 17767869169014453479975747)
            ·
              refine ⟨26651803753521680219963621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17767869169014453479975747 26651803753521680219963621)
              ·
                refine ⟨4997213203785315041243179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26651803753521680219963621 4997213203785315041243179)
                ·
                  refine ⟨7495819805677972561864769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997213203785315041243179 7495819805677972561864769)
                  ·
                    refine ⟨5621864854258479421398577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7495819805677972561864769 5621864854258479421398577)
                    ·
                      refine ⟨4216398640693859566048933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621864854258479421398577 4216398640693859566048933)
                      ·
                        rfl

theorem cell23_8211407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 2, 2].length) (baseStart_8211407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211407 prefixEnd_8211407 := by exact prefixLift 8211407
  have htrace : WordTrace (prefixWord ++ tailWord_8211407) baseStart_8211407 baseEnd_8211407 := by
    simpa [prefixWord, tailWord_8211407, baseEnd_8211407] using wordTrace_append hprefix tailTrace_8211407
  have hstable : (prefixWord ++ tailWord_8211407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211407).length < 2 ^ (prefixWord ++ tailWord_8211407).sum := by decide
  have hdescent : baseEnd_8211407 < baseStart_8211407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211409 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_8211409 : Nat := 118140960795 + 8211409 * 2 ^ 59
def prefixEnd_8211409 : Nat := 4983230072969 + 3 ^ 40 * 8211409 * 2
def baseEnd_8211409 : Nat := 1405466555885056186074641

theorem tailTrace_8211409 : CollatzResearch.WordTrace tailWord_8211409 prefixEnd_8211409 1405466555885056186074641 := by
  unfold tailWord_8211409
  simp only [CollatzResearch.WordTrace]
  refine ⟨299494690708475064851781281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199663127138983376567854187 299494690708475064851781281)
  ·
    refine ⟨224621018031356298638835961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299494690708475064851781281 224621018031356298638835961)
    ·
      refine ⟨168465763523517223979126971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224621018031356298638835961 168465763523517223979126971)
      ·
        refine ⟨252698645285275835968690457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168465763523517223979126971 252698645285275835968690457)
        ·
          refine ⟨189523983963956876976517843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252698645285275835968690457 189523983963956876976517843)
          ·
            refine ⟨284285975945935315464776765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189523983963956876976517843 284285975945935315464776765)
            ·
              refine ⟨106607240979725743299291287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284285975945935315464776765 106607240979725743299291287)
              ·
                refine ⟨159910861469588614948936931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106607240979725743299291287 159910861469588614948936931)
                ·
                  refine ⟨239866292204382922423405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159910861469588614948936931 239866292204382922423405397)
                  ·
                    refine ⟨1405466555885056186074641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239866292204382922423405397 1405466555885056186074641)
                    ·
                      rfl

theorem cell23_8211409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_8211409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211409 prefixEnd_8211409 := by exact prefixLift 8211409
  have htrace : WordTrace (prefixWord ++ tailWord_8211409) baseStart_8211409 baseEnd_8211409 := by
    simpa [prefixWord, tailWord_8211409, baseEnd_8211409] using wordTrace_append hprefix tailTrace_8211409
  have hstable : (prefixWord ++ tailWord_8211409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211409).length < 2 ^ (prefixWord ++ tailWord_8211409).sum := by decide
  have hdescent : baseEnd_8211409 < baseStart_8211409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211413 : List Nat := [1, 3, 2, 3, 3, 2, 1, 8]
def baseStart_8211413 : Nat := 118140960795 + 8211413 * 2 ^ 59
def prefixEnd_8211413 : Nat := 4983230072969 + 3 ^ 40 * 8211413 * 2
def baseEnd_8211413 : Nat := 156163026725103205280515

theorem tailTrace_8211413 : CollatzResearch.WordTrace tailWord_8211413 prefixEnd_8211413 156163026725103205280515 := by
  unfold tailWord_8211413
  simp only [CollatzResearch.WordTrace]
  refine ⟨299494836600460573534926893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199663224400307049023284595 299494836600460573534926893)
  ·
    refine ⟨112310563725172715075597585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299494836600460573534926893 112310563725172715075597585)
    ·
      refine ⟨84232922793879536306698189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112310563725172715075597585 84232922793879536306698189)
      ·
        refine ⟨31587346047704826115011821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84232922793879536306698189 31587346047704826115011821)
        ·
          refine ⟨11845254767889309793129433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31587346047704826115011821 11845254767889309793129433)
          ·
            refine ⟨8883941075916982344847075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11845254767889309793129433 8883941075916982344847075)
            ·
              refine ⟨13325911613875473517270613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883941075916982344847075 13325911613875473517270613)
              ·
                refine ⟨156163026725103205280515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13325911613875473517270613 156163026725103205280515)
                ·
                  rfl

theorem cell23_8211413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 8].length) (baseStart_8211413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211413 prefixEnd_8211413 := by exact prefixLift 8211413
  have htrace : WordTrace (prefixWord ++ tailWord_8211413) baseStart_8211413 baseEnd_8211413 := by
    simpa [prefixWord, tailWord_8211413, baseEnd_8211413] using wordTrace_append hprefix tailTrace_8211413
  have hstable : (prefixWord ++ tailWord_8211413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211413).length < 2 ^ (prefixWord ++ tailWord_8211413).sum := by decide
  have hdescent : baseEnd_8211413 < baseStart_8211413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211457 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_8211457 : Nat := 118140960795 + 8211457 * 2 ^ 59
def prefixEnd_8211457 : Nat := 4983230072969 + 3 ^ 40 * 8211457 * 2
def baseEnd_8211457 : Nat := 4216424314726584370423703

theorem tailTrace_8211457 : CollatzResearch.WordTrace tailWord_8211457 prefixEnd_8211457 4216424314726584370423703 := by
  unfold tailWord_8211457
  simp only [CollatzResearch.WordTrace]
  refine ⟨299496441412301169049528625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199664294274867446033019083 299496441412301169049528625)
  ·
    refine ⟨224622331059225876787146469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299496441412301169049528625 224622331059225876787146469)
    ·
      refine ⟨42116687073604851897589963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224622331059225876787146469 42116687073604851897589963)
      ·
        refine ⟨63175030610407277846384945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42116687073604851897589963 63175030610407277846384945)
        ·
          refine ⟨47381272957805458384788709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63175030610407277846384945 47381272957805458384788709)
          ·
            refine ⟨8883988679588523447147883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47381272957805458384788709 8883988679588523447147883)
            ·
              refine ⟨13325983019382785170721825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883988679588523447147883 13325983019382785170721825)
              ·
                refine ⟨9994487264537088878041369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13325983019382785170721825 9994487264537088878041369)
                ·
                  refine ⟨7495865448402816658531027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994487264537088878041369 7495865448402816658531027)
                  ·
                    refine ⟨11243798172604224987796541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7495865448402816658531027 11243798172604224987796541)
                    ·
                      refine ⟨4216424314726584370423703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11243798172604224987796541 4216424314726584370423703)
                      ·
                        rfl

theorem cell23_8211457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_8211457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211457 prefixEnd_8211457 := by exact prefixLift 8211457
  have htrace : WordTrace (prefixWord ++ tailWord_8211457) baseStart_8211457 baseEnd_8211457 := by
    simpa [prefixWord, tailWord_8211457, baseEnd_8211457] using wordTrace_append hprefix tailTrace_8211457
  have hstable : (prefixWord ++ tailWord_8211457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211457).length < 2 ^ (prefixWord ++ tailWord_8211457).sum := by decide
  have hdescent : baseEnd_8211457 < baseStart_8211457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211480 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_8211480 : Nat := 118140960795 + 8211480 * 2 ^ 59
def prefixEnd_8211480 : Nat := 4983230072969 + 3 ^ 40 * 8211480 * 2
def baseEnd_8211480 : Nat := 4216436124781637780436097

theorem tailTrace_8211480 : CollatzResearch.WordTrace tailWord_8211480 prefixEnd_8211480 4216436124781637780436097 := by
  unfold tailWord_8211480
  simp only [CollatzResearch.WordTrace]
  refine ⟨149748640145608921988807947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199664853527478562651743929 149748640145608921988807947)
  ·
    refine ⟨224622960218413382983211921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149748640145608921988807947 224622960218413382983211921)
    ·
      refine ⟨168467220163810037237408941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224622960218413382983211921 168467220163810037237408941)
      ·
        refine ⟨63175207561428763964028353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168467220163810037237408941 63175207561428763964028353)
        ·
          refine ⟨47381405671071572973021265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63175207561428763964028353 47381405671071572973021265)
          ·
            refine ⟨35536054253303679729765949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47381405671071572973021265 35536054253303679729765949)
            ·
              refine ⟨13326020344988879898662231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35536054253303679729765949 13326020344988879898662231)
              ·
                refine ⟨19989030517483319847993347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326020344988879898662231 19989030517483319847993347)
                ·
                  refine ⟨29983545776224979771990021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19989030517483319847993347 29983545776224979771990021)
                  ·
                    refine ⟨5621914833042183707248129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29983545776224979771990021 5621914833042183707248129)
                    ·
                      refine ⟨4216436124781637780436097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621914833042183707248129 4216436124781637780436097)
                      ·
                        rfl

theorem cell23_8211480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_8211480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211480 prefixEnd_8211480 := by exact prefixLift 8211480
  have htrace : WordTrace (prefixWord ++ tailWord_8211480) baseStart_8211480 baseEnd_8211480 := by
    simpa [prefixWord, tailWord_8211480, baseEnd_8211480] using wordTrace_append hprefix tailTrace_8211480
  have hstable : (prefixWord ++ tailWord_8211480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211480).length < 2 ^ (prefixWord ++ tailWord_8211480).sum := by decide
  have hdescent : baseEnd_8211480 < baseStart_8211480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211520 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 5]
def baseStart_8211520 : Nat := 118140960795 + 8211520 * 2 ^ 59
def prefixEnd_8211520 : Nat := 4983230072969 + 3 ^ 40 * 8211520 * 2
def baseEnd_8211520 : Nat := 468495184889757513770657

theorem tailTrace_8211520 : CollatzResearch.WordTrace tailWord_8211520 prefixEnd_8211520 468495184889757513770657 := by
  unfold tailWord_8211520
  simp only [CollatzResearch.WordTrace]
  refine ⟨149749369605536465404536007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199665826140715287206048009 149749369605536465404536007)
  ·
    refine ⟨224624054408304698106804011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149749369605536465404536007 224624054408304698106804011)
    ·
      refine ⟨336936081612457047160206017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224624054408304698106804011 336936081612457047160206017)
      ·
        refine ⟨252702061209342785370154513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336936081612457047160206017 252702061209342785370154513)
        ·
          refine ⟨189526545907007089027615885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252702061209342785370154513 189526545907007089027615885)
          ·
            refine ⟨71072454715127658385355957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189526545907007089027615885 71072454715127658385355957)
            ·
              refine ⟨6663042629543217973627121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71072454715127658385355957 6663042629543217973627121)
              ·
                refine ⟨4997281972157413480220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663042629543217973627121 4997281972157413480220341)
                ·
                  refine ⟨468495184889757513770657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997281972157413480220341 468495184889757513770657)
                  ·
                    rfl

theorem cell23_8211520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 5].length) (baseStart_8211520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211520 prefixEnd_8211520 := by exact prefixLift 8211520
  have htrace : WordTrace (prefixWord ++ tailWord_8211520) baseStart_8211520 baseEnd_8211520 := by
    simpa [prefixWord, tailWord_8211520, baseEnd_8211520] using wordTrace_append hprefix tailTrace_8211520
  have hstable : (prefixWord ++ tailWord_8211520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211520).length < 2 ^ (prefixWord ++ tailWord_8211520).sum := by decide
  have hdescent : baseEnd_8211520 < baseStart_8211520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211523 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 5, 2]
def baseStart_8211523 : Nat := 118140960795 + 8211523 * 2 ^ 59
def prefixEnd_8211523 : Nat := 4983230072969 + 3 ^ 40 * 8211523 * 2
def baseEnd_8211523 : Nat := 4216458204449781112198399

theorem tailTrace_8211523 : CollatzResearch.WordTrace tailWord_8211523 prefixEnd_8211523 4216458204449781112198399 := by
  unfold tailWord_8211523
  simp only [CollatzResearch.WordTrace]
  refine ⟨299498848630062062321431223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199665899086708041547620815 299498848630062062321431223)
  ·
    refine ⟨449248272945093093482146835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299498848630062062321431223 449248272945093093482146835)
    ·
      refine ⟨673872409417639640223220253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449248272945093093482146835 673872409417639640223220253)
      ·
        refine ⟨252702153531614865083707595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673872409417639640223220253 252702153531614865083707595)
        ·
          refine ⟨379053230297422297625561393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252702153531614865083707595 379053230297422297625561393)
          ·
            refine ⟨284289922723066723219171045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379053230297422297625561393 284289922723066723219171045)
            ·
              refine ⟨53304360510575010603594571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284289922723066723219171045 53304360510575010603594571)
              ·
                refine ⟨79956540765862515905391857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53304360510575010603594571 79956540765862515905391857)
                ·
                  refine ⟨59967405574396886929043893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79956540765862515905391857 59967405574396886929043893)
                  ·
                    refine ⟨5621944272599708149597865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59967405574396886929043893 5621944272599708149597865)
                    ·
                      refine ⟨4216458204449781112198399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621944272599708149597865 4216458204449781112198399)
                      ·
                        rfl

theorem cell23_8211523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_8211523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211523 prefixEnd_8211523 := by exact prefixLift 8211523
  have htrace : WordTrace (prefixWord ++ tailWord_8211523) baseStart_8211523 baseEnd_8211523 := by
    simpa [prefixWord, tailWord_8211523, baseEnd_8211523] using wordTrace_append hprefix tailTrace_8211523
  have hstable : (prefixWord ++ tailWord_8211523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211523).length < 2 ^ (prefixWord ++ tailWord_8211523).sum := by decide
  have hdescent : baseEnd_8211523 < baseStart_8211523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211536 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_8211536 : Nat := 118140960795 + 8211536 * 2 ^ 59
def prefixEnd_8211536 : Nat := 4983230072969 + 3 ^ 40 * 8211536 * 2
def baseEnd_8211536 : Nat := 4216464879698289561335839

theorem tailTrace_8211536 : CollatzResearch.WordTrace tailWord_8211536 prefixEnd_8211536 4216464879698289561335839 := by
  unfold tailWord_8211536
  simp only [CollatzResearch.WordTrace]
  refine ⟨149749661389507482770827231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199666215186009977027769641 149749661389507482770827231)
  ·
    refine ⟨224624492084261224156240847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149749661389507482770827231 224624492084261224156240847)
    ·
      refine ⟨336936738126391836234361271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224624492084261224156240847 336936738126391836234361271)
      ·
        refine ⟨505405107189587754351541907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336936738126391836234361271 505405107189587754351541907)
        ·
          refine ⟨758107660784381631527312861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505405107189587754351541907 758107660784381631527312861)
          ·
            refine ⟨284290372794143111822742323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758107660784381631527312861 284290372794143111822742323)
            ·
              refine ⟨426435559191214667734113485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284290372794143111822742323 426435559191214667734113485)
              ·
                refine ⟨159913334696705500400292557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426435559191214667734113485 159913334696705500400292557)
                ·
                  refine ⟨59967500511264562650109709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159913334696705500400292557 59967500511264562650109709)
                  ·
                    refine ⟨22487812691724210993791141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59967500511264562650109709 22487812691724210993791141)
                    ·
                      refine ⟨4216464879698289561335839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22487812691724210993791141 4216464879698289561335839)
                      ·
                        rfl

theorem cell23_8211536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_8211536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211536 prefixEnd_8211536 := by exact prefixLift 8211536
  have htrace : WordTrace (prefixWord ++ tailWord_8211536) baseStart_8211536 baseEnd_8211536 := by
    simpa [prefixWord, tailWord_8211536, baseEnd_8211536] using wordTrace_append hprefix tailTrace_8211536
  have hstable : (prefixWord ++ tailWord_8211536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211536).length < 2 ^ (prefixWord ++ tailWord_8211536).sum := by decide
  have hdescent : baseEnd_8211536 < baseStart_8211536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211553 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_8211553 : Nat := 118140960795 + 8211553 * 2 ^ 59
def prefixEnd_8211553 : Nat := 4983230072969 + 3 ^ 40 * 8211553 * 2
def baseEnd_8211553 : Nat := 4216473608869415994823261

theorem tailTrace_8211553 : CollatzResearch.WordTrace tailWord_8211553 prefixEnd_8211553 4216473608869415994823261 := by
  unfold tailWord_8211553
  simp only [CollatzResearch.WordTrace]
  refine ⟨299499942819953377445023313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199666628546635584963348875 299499942819953377445023313)
  ·
    refine ⟨224624957114965033083767485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299499942819953377445023313 224624957114965033083767485)
    ·
      refine ⟨84234358918111887406412807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224624957114965033083767485 84234358918111887406412807)
      ·
        refine ⟨126351538377167831109619211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84234358918111887406412807 126351538377167831109619211)
        ·
          refine ⟨189527307565751746664428817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126351538377167831109619211 189527307565751746664428817)
          ·
            refine ⟨142145480674313809998321613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189527307565751746664428817 142145480674313809998321613)
            ·
              refine ⟨53304555252867678749370605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142145480674313809998321613 53304555252867678749370605)
              ·
                refine ⟨19989208219825379531013977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53304555252867678749370605 19989208219825379531013977)
                ·
                  refine ⟨14991906164869034648260483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19989208219825379531013977 14991906164869034648260483)
                  ·
                    refine ⟨22487859247303551972390725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14991906164869034648260483 22487859247303551972390725)
                    ·
                      refine ⟨4216473608869415994823261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22487859247303551972390725 4216473608869415994823261)
                      ·
                        rfl

theorem cell23_8211553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_8211553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211553 prefixEnd_8211553 := by exact prefixLift 8211553
  have htrace : WordTrace (prefixWord ++ tailWord_8211553) baseStart_8211553 baseEnd_8211553 := by
    simpa [prefixWord, tailWord_8211553, baseEnd_8211553] using wordTrace_append hprefix tailTrace_8211553
  have hstable : (prefixWord ++ tailWord_8211553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211553).length < 2 ^ (prefixWord ++ tailWord_8211553).sum := by decide
  have hdescent : baseEnd_8211553 < baseStart_8211553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211570 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_8211570 : Nat := 118140960795 + 8211570 * 2 ^ 59
def prefixEnd_8211570 : Nat := 4983230072969 + 3 ^ 40 * 8211570 * 2
def baseEnd_8211570 : Nat := 4216482338040542428310683

theorem tailTrace_8211570 : CollatzResearch.WordTrace tailWord_8211570 prefixEnd_8211570 4216482338040542428310683 := by
  unfold tailWord_8211570
  simp only [CollatzResearch.WordTrace]
  refine ⟨74875140715222947337098041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199667041907261192898928109 74875140715222947337098041)
  ·
    refine ⟨56156355536417210502823531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74875140715222947337098041 56156355536417210502823531)
    ·
      refine ⟨84234533304625815754235297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56156355536417210502823531 84234533304625815754235297)
      ·
        refine ⟨63175899978469361815676473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84234533304625815754235297 63175899978469361815676473)
        ·
          refine ⟨47381924983852021361757355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63175899978469361815676473 47381924983852021361757355)
          ·
            refine ⟨71072887475778032042636033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47381924983852021361757355 71072887475778032042636033)
            ·
              refine ⟨53304665606833524031977025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71072887475778032042636033 53304665606833524031977025)
              ·
                refine ⟨39978499205125143023982769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53304665606833524031977025 39978499205125143023982769)
                ·
                  refine ⟨29983874403843857267987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39978499205125143023982769 29983874403843857267987077)
                  ·
                    refine ⟨5621976450720723237747577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29983874403843857267987077 5621976450720723237747577)
                    ·
                      refine ⟨4216482338040542428310683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5621976450720723237747577 4216482338040542428310683)
                      ·
                        rfl

theorem cell23_8211570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_8211570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211570 prefixEnd_8211570 := by exact prefixLift 8211570
  have htrace : WordTrace (prefixWord ++ tailWord_8211570) baseStart_8211570 baseEnd_8211570 := by
    simpa [prefixWord, tailWord_8211570, baseEnd_8211570] using wordTrace_append hprefix tailTrace_8211570
  have hstable : (prefixWord ++ tailWord_8211570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211570).length < 2 ^ (prefixWord ++ tailWord_8211570).sum := by decide
  have hdescent : baseEnd_8211570 < baseStart_8211570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211576 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 8]
def baseStart_8211576 : Nat := 118140960795 + 8211576 * 2 ^ 59
def prefixEnd_8211576 : Nat := 4983230072969 + 3 ^ 40 * 8211576 * 2
def baseEnd_8211576 : Nat := 468498379880496600537295

theorem tailTrace_8211576 : CollatzResearch.WordTrace tailWord_8211576 prefixEnd_8211576 468498379880496600537295 := by
  unfold tailWord_8211576
  simp only [CollatzResearch.WordTrace]
  refine ⟨149750390849435026186555291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199667187799246701582073721 149750390849435026186555291)
  ·
    refine ⟨224625586274152539279832937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149750390849435026186555291 224625586274152539279832937)
    ·
      refine ⟨168469189705614404459874703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224625586274152539279832937 168469189705614404459874703)
      ·
        refine ⟨252703784558421606689812055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168469189705614404459874703 252703784558421606689812055)
        ·
          refine ⟨379055676837632410034718083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252703784558421606689812055 379055676837632410034718083)
          ·
            refine ⟨568583515256448615052077125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379055676837632410034718083 568583515256448615052077125)
            ·
              refine ⟨106609409110584115322264461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568583515256448615052077125 106609409110584115322264461)
              ·
                refine ⟨39978528416469043245849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106609409110584115322264461 39978528416469043245849173)
                ·
                  refine ⟨468498379880496600537295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39978528416469043245849173 468498379880496600537295)
                  ·
                    rfl

theorem cell23_8211576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_8211576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211576 prefixEnd_8211576 := by exact prefixLift 8211576
  have htrace : WordTrace (prefixWord ++ tailWord_8211576) baseStart_8211576 baseEnd_8211576 := by
    simpa [prefixWord, tailWord_8211576, baseEnd_8211576] using wordTrace_append hprefix tailTrace_8211576
  have hstable : (prefixWord ++ tailWord_8211576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211576).length < 2 ^ (prefixWord ++ tailWord_8211576).sum := by decide
  have hdescent : baseEnd_8211576 < baseStart_8211576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211593 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 6]
def baseStart_8211593 : Nat := 118140960795 + 8211593 * 2 ^ 59
def prefixEnd_8211593 : Nat := 4983230072969 + 3 ^ 40 * 8211593 * 2
def baseEnd_8211593 : Nat := 468499349788399537591453

theorem tailTrace_8211593 : CollatzResearch.WordTrace tailWord_8211593 prefixEnd_8211593 468499349788399537591453 := by
  unfold tailWord_8211593
  simp only [CollatzResearch.WordTrace]
  refine ⟨299501401739808464276479433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199667601159872309517652955 299501401739808464276479433)
  ·
    refine ⟨224626051304856348207359575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299501401739808464276479433 224626051304856348207359575)
    ·
      refine ⟨336939076957284522311039363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224626051304856348207359575 336939076957284522311039363)
      ·
        refine ⟨505408615435926783466559045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336939076957284522311039363 505408615435926783466559045)
        ·
          refine ⟨94764115394236271899979821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505408615435926783466559045 94764115394236271899979821)
          ·
            refine ⟨35536543272838601962492433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94764115394236271899979821 35536543272838601962492433)
            ·
              refine ⟨26652407454628951471869325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35536543272838601962492433 26652407454628951471869325)
              ·
                refine ⟨9994652795485856801950997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26652407454628951471869325 9994652795485856801950997)
                ·
                  refine ⟨468499349788399537591453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9994652795485856801950997 468499349788399537591453)
                  ·
                    rfl

theorem cell23_8211593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_8211593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211593 prefixEnd_8211593 := by exact prefixLift 8211593
  have htrace : WordTrace (prefixWord ++ tailWord_8211593) baseStart_8211593 baseEnd_8211593 := by
    simpa [prefixWord, tailWord_8211593, baseEnd_8211593] using wordTrace_append hprefix tailTrace_8211593
  have hstable : (prefixWord ++ tailWord_8211593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211593).length < 2 ^ (prefixWord ++ tailWord_8211593).sum := by decide
  have hdescent : baseEnd_8211593 < baseStart_8211593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211607 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_8211607 : Nat := 118140960795 + 8211607 * 2 ^ 59
def prefixEnd_8211607 : Nat := 4983230072969 + 3 ^ 40 * 8211607 * 2
def baseEnd_8211607 : Nat := 4216501336824758783548013

theorem tailTrace_8211607 : CollatzResearch.WordTrace tailWord_8211607 prefixEnd_8211607 4216501336824758783548013 := by
  unfold tailWord_8211607
  simp only [CollatzResearch.WordTrace]
  refine ⟨299501912361757744667489075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199667941574505163111659383 299501912361757744667489075)
  ·
    refine ⟨449252868542636617001233613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299501912361757744667489075 449252868542636617001233613)
    ·
      refine ⟨168469825703488731375462605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449252868542636617001233613 168469825703488731375462605)
      ·
        refine ⟨63176184638808274265798477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168469825703488731375462605 63176184638808274265798477)
        ·
          refine ⟨23691069239553102849674429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63176184638808274265798477 23691069239553102849674429)
          ·
            refine ⟨8884150964832413568627911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23691069239553102849674429 8884150964832413568627911)
            ·
              refine ⟨13326226447248620352941867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884150964832413568627911 13326226447248620352941867)
              ·
                refine ⟨19989339670872930529412801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326226447248620352941867 19989339670872930529412801)
                ·
                  refine ⟨14992004753154697897059601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19989339670872930529412801 14992004753154697897059601)
                  ·
                    refine ⟨11244003564866023422794701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992004753154697897059601 11244003564866023422794701)
                    ·
                      refine ⟨4216501336824758783548013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244003564866023422794701 4216501336824758783548013)
                      ·
                        rfl

theorem cell23_8211607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_8211607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211607 prefixEnd_8211607 := by exact prefixLift 8211607
  have htrace : WordTrace (prefixWord ++ tailWord_8211607) baseStart_8211607 baseEnd_8211607 := by
    simpa [prefixWord, tailWord_8211607, baseEnd_8211607] using wordTrace_append hprefix tailTrace_8211607
  have hstable : (prefixWord ++ tailWord_8211607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211607).length < 2 ^ (prefixWord ++ tailWord_8211607).sum := by decide
  have hdescent : baseEnd_8211607 < baseStart_8211607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211614 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_8211614 : Nat := 118140960795 + 8211614 * 2 ^ 59
def prefixEnd_8211614 : Nat := 4983230072969 + 3 ^ 40 * 8211614 * 2
def baseEnd_8211614 : Nat := 1405501643729780085386827

theorem tailTrace_8211614 : CollatzResearch.WordTrace tailWord_8211614 prefixEnd_8211614 1405501643729780085386827 := by
  unfold tailWord_8211614
  simp only [CollatzResearch.WordTrace]
  refine ⟨37437770959091548107874237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199668111781821589908662597 37437770959091548107874237)
  ·
    refine ⟨14039164109659330540452839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37437770959091548107874237 14039164109659330540452839)
    ·
      refine ⟨21058746164488995810679259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039164109659330540452839 21058746164488995810679259)
      ·
        refine ⟨31588119246733493716018889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21058746164488995810679259 31588119246733493716018889)
        ·
          refine ⟨23691089435050120287014167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31588119246733493716018889 23691089435050120287014167)
          ·
            refine ⟨35536634152575180430521251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23691089435050120287014167 35536634152575180430521251)
            ·
              refine ⟨53304951228862770645781877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35536634152575180430521251 53304951228862770645781877)
              ·
                refine ⟨4997339177705884748042051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53304951228862770645781877 4997339177705884748042051)
                ·
                  refine ⟨7496008766558827122063077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997339177705884748042051 7496008766558827122063077)
                  ·
                    refine ⟨1405501643729780085386827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496008766558827122063077 1405501643729780085386827)
                    ·
                      rfl

theorem cell23_8211614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_8211614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211614 prefixEnd_8211614 := by exact prefixLift 8211614
  have htrace : WordTrace (prefixWord ++ tailWord_8211614) baseStart_8211614 baseEnd_8211614 := by
    simpa [prefixWord, tailWord_8211614, baseEnd_8211614] using wordTrace_append hprefix tailTrace_8211614
  have hstable : (prefixWord ++ tailWord_8211614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211614).length < 2 ^ (prefixWord ++ tailWord_8211614).sum := by decide
  have hdescent : baseEnd_8211614 < baseStart_8211614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211643 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4]
def baseStart_8211643 : Nat := 118140960795 + 8211643 * 2 ^ 59
def prefixEnd_8211643 : Nat := 4983230072969 + 3 ^ 40 * 8211643 * 2
def baseEnd_8211643 : Nat := 4216519822128320642697847

theorem tailTrace_8211643 : CollatzResearch.WordTrace tailWord_8211643 prefixEnd_8211643 4216519822128320642697847 := by
  unfold tailWord_8211643
  simp only [CollatzResearch.WordTrace]
  refine ⟨299503225389627322815799583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199668816926418215210533055 299503225389627322815799583)
  ·
    refine ⟨449254838084440984223699375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299503225389627322815799583 449254838084440984223699375)
    ·
      refine ⟨673882257126661476335549063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449254838084440984223699375 673882257126661476335549063)
      ·
        refine ⟨1010823385689992214503323595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673882257126661476335549063 1010823385689992214503323595)
        ·
          refine ⟨1516235078534988321754985393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010823385689992214503323595 1516235078534988321754985393)
          ·
            refine ⟨1137176308901241241316239045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516235078534988321754985393 1137176308901241241316239045)
            ·
              refine ⟨213220557918982732746794821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1137176308901241241316239045 213220557918982732746794821)
              ·
                refine ⟨39978854609809262390024029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213220557918982732746794821 39978854609809262390024029)
                ·
                  refine ⟨14992070478678473396259011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39978854609809262390024029 14992070478678473396259011)
                  ·
                    refine ⟨22488105718017710094388517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14992070478678473396259011 22488105718017710094388517)
                    ·
                      refine ⟨4216519822128320642697847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22488105718017710094388517 4216519822128320642697847)
                      ·
                        rfl

theorem cell23_8211643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_8211643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211643 prefixEnd_8211643 := by exact prefixLift 8211643
  have htrace : WordTrace (prefixWord ++ tailWord_8211643) baseStart_8211643 baseEnd_8211643 := by
    simpa [prefixWord, tailWord_8211643, baseEnd_8211643] using wordTrace_append hprefix tailTrace_8211643
  have hstable : (prefixWord ++ tailWord_8211643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211643).length < 2 ^ (prefixWord ++ tailWord_8211643).sum := by decide
  have hdescent : baseEnd_8211643 < baseStart_8211643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211673 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_8211673 : Nat := 118140960795 + 8211673 * 2 ^ 59
def prefixEnd_8211673 : Nat := 4983230072969 + 3 ^ 40 * 8211673 * 2
def baseEnd_8211673 : Nat := 4216535226547955525322709

theorem tailTrace_8211673 : CollatzResearch.WordTrace tailWord_8211673 prefixEnd_8211673 4216535226547955525322709 := by
  unfold tailWord_8211673
  simp only [CollatzResearch.WordTrace]
  refine ⟨299504319579518637939391673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199669546386345758626261115 299504319579518637939391673)
  ·
    refine ⟨224628239684638978454543755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299504319579518637939391673 224628239684638978454543755)
    ·
      refine ⟨336942359526958467681815633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224628239684638978454543755 336942359526958467681815633)
      ·
        refine ⟨252706769645218850761361725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336942359526958467681815633 252706769645218850761361725)
        ·
          refine ⟨94765038616957069035510647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252706769645218850761361725 94765038616957069035510647)
          ·
            refine ⟨142147557925435603553265971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94765038616957069035510647 142147557925435603553265971)
            ·
              refine ⟨213221336888153405329898957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142147557925435603553265971 213221336888153405329898957)
              ·
                refine ⟨79958001333057526998712109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213221336888153405329898957 79958001333057526998712109)
                ·
                  refine ⟨29984250499896572624517041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79958001333057526998712109 29984250499896572624517041)
                  ·
                    refine ⟨22488187874922429468387781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29984250499896572624517041 22488187874922429468387781)
                    ·
                      refine ⟨4216535226547955525322709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22488187874922429468387781 4216535226547955525322709)
                      ·
                        rfl

theorem cell23_8211673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_8211673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211673 prefixEnd_8211673 := by exact prefixLift 8211673
  have htrace : WordTrace (prefixWord ++ tailWord_8211673) baseStart_8211673 baseEnd_8211673 := by
    simpa [prefixWord, tailWord_8211673, baseEnd_8211673] using wordTrace_append hprefix tailTrace_8211673
  have hstable : (prefixWord ++ tailWord_8211673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211673).length < 2 ^ (prefixWord ++ tailWord_8211673).sum := by decide
  have hdescent : baseEnd_8211673 < baseStart_8211673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211680 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_8211680 : Nat := 118140960795 + 8211680 * 2 ^ 59
def prefixEnd_8211680 : Nat := 4983230072969 + 3 ^ 40 * 8211680 * 2
def baseEnd_8211680 : Nat := 4216538820912536997935177

theorem tailTrace_8211680 : CollatzResearch.WordTrace tailWord_8211680 prefixEnd_8211680 4216538820912536997935177 := by
  unfold tailWord_8211680
  simp only [CollatzResearch.WordTrace]
  refine ⟨149752287445246639067448247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199669716593662185423264329 149752287445246639067448247)
  ·
    refine ⟨224628431167869958601172371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149752287445246639067448247 224628431167869958601172371)
    ·
      refine ⟨336942646751804937901758557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224628431167869958601172371 336942646751804937901758557)
      ·
        refine ⟨126353492531926851713159459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336942646751804937901758557 126353492531926851713159459)
        ·
          refine ⟨189530238797890277569739189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126353492531926851713159459 189530238797890277569739189)
          ·
            refine ⟨17768459887302213522163049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189530238797890277569739189 17768459887302213522163049)
            ·
              refine ⟨13326344915476660141622287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17768459887302213522163049 13326344915476660141622287)
              ·
                refine ⟨19989517373214990212433431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326344915476660141622287 19989517373214990212433431)
                ·
                  refine ⟨29984276059822485318650147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19989517373214990212433431 29984276059822485318650147)
                  ·
                    refine ⟨44976414089733727977975221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29984276059822485318650147 44976414089733727977975221)
                    ·
                      refine ⟨4216538820912536997935177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44976414089733727977975221 4216538820912536997935177)
                      ·
                        rfl

theorem cell23_8211680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_8211680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211680 prefixEnd_8211680 := by exact prefixLift 8211680
  have htrace : WordTrace (prefixWord ++ tailWord_8211680) baseStart_8211680 baseEnd_8211680 := by
    simpa [prefixWord, tailWord_8211680, baseEnd_8211680] using wordTrace_append hprefix tailTrace_8211680
  have hstable : (prefixWord ++ tailWord_8211680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211680).length < 2 ^ (prefixWord ++ tailWord_8211680).sum := by decide
  have hdescent : baseEnd_8211680 < baseStart_8211680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211694 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_8211694 : Nat := 118140960795 + 8211694 * 2 ^ 59
def prefixEnd_8211694 : Nat := 4983230072969 + 3 ^ 40 * 8211694 * 2
def baseEnd_8211694 : Nat := 4216546009641699943160113

theorem tailTrace_8211694 : CollatzResearch.WordTrace tailWord_8211694 prefixEnd_8211694 4216546009641699943160113 := by
  unfold tailWord_8211694
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438135689055319815738267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199670057008295039017270757 37438135689055319815738267)
  ·
    refine ⟨56157203533582979723607401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37438135689055319815738267 56157203533582979723607401)
    ·
      refine ⟨42117902650187234792705551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56157203533582979723607401 42117902650187234792705551)
      ·
        refine ⟨63176853975280852189058327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42117902650187234792705551 63176853975280852189058327)
        ·
          refine ⟨94765280962921278283587491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63176853975280852189058327 94765280962921278283587491)
          ·
            refine ⟨142147921444381917425381237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94765280962921278283587491 142147921444381917425381237)
            ·
              refine ⟨13326367635410804758629491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142147921444381917425381237 13326367635410804758629491)
              ·
                refine ⟨19989551453116207137944237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326367635410804758629491 19989551453116207137944237)
                ·
                  refine ⟨7496081794918577676729089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19989551453116207137944237 7496081794918577676729089)
                  ·
                    refine ⟨5622061346188933257546817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496081794918577676729089 5622061346188933257546817)
                    ·
                      refine ⟨4216546009641699943160113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622061346188933257546817 4216546009641699943160113)
                      ·
                        rfl

theorem cell23_8211694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_8211694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211694 prefixEnd_8211694 := by exact prefixLift 8211694
  have htrace : WordTrace (prefixWord ++ tailWord_8211694) baseStart_8211694 baseEnd_8211694 := by
    simpa [prefixWord, tailWord_8211694, baseEnd_8211694] using wordTrace_append hprefix tailTrace_8211694
  have hstable : (prefixWord ++ tailWord_8211694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211694).length < 2 ^ (prefixWord ++ tailWord_8211694).sum := by decide
  have hdescent : baseEnd_8211694 < baseStart_8211694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211714 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_8211714 : Nat := 118140960795 + 8211714 * 2 ^ 59
def prefixEnd_8211714 : Nat := 4983230072969 + 3 ^ 40 * 8211714 * 2
def baseEnd_8211714 : Nat := 4216556279254789864910021

theorem tailTrace_8211714 : CollatzResearch.WordTrace tailWord_8211714 prefixEnd_8211714 4216556279254789864910021 := by
  unfold tailWord_8211714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876453743092525485408549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199670543314913401294422797 74876453743092525485408549)
  ·
    refine ⟨14039335076829848528514103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74876453743092525485408549 14039335076829848528514103)
    ·
      refine ⟨21059002615244772792771155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039335076829848528514103 21059002615244772792771155)
      ·
        refine ⟨31588503922867159189156733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21059002615244772792771155 31588503922867159189156733)
        ·
          refine ⟨11845688971075184695933775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31588503922867159189156733 11845688971075184695933775)
          ·
            refine ⟨17768533456612777043900663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845688971075184695933775 17768533456612777043900663)
            ·
              refine ⟨26652800184919165565850995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17768533456612777043900663 26652800184919165565850995)
              ·
                refine ⟨39979200277378748348776493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26652800184919165565850995 39979200277378748348776493)
                ·
                  refine ⟨14992200104017030630791185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39979200277378748348776493 14992200104017030630791185)
                  ·
                    refine ⟨11244150078012772973093389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992200104017030630791185 11244150078012772973093389)
                    ·
                      refine ⟨4216556279254789864910021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244150078012772973093389 4216556279254789864910021)
                      ·
                        rfl

theorem cell23_8211714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_8211714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211714 prefixEnd_8211714 := by exact prefixLift 8211714
  have htrace : WordTrace (prefixWord ++ tailWord_8211714) baseStart_8211714 baseEnd_8211714 := by
    simpa [prefixWord, tailWord_8211714, baseEnd_8211714] using wordTrace_append hprefix tailTrace_8211714
  have hstable : (prefixWord ++ tailWord_8211714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211714).length < 2 ^ (prefixWord ++ tailWord_8211714).sum := by decide
  have hdescent : baseEnd_8211714 < baseStart_8211714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211754 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_8211754 : Nat := 118140960795 + 8211754 * 2 ^ 59
def prefixEnd_8211754 : Nat := 4983230072969 + 3 ^ 40 * 8211754 * 2
def baseEnd_8211754 : Nat := 4216576818480969708409837

theorem tailTrace_8211754 : CollatzResearch.WordTrace tailWord_8211754 prefixEnd_8211754 4216576818480969708409837 := by
  unfold tailWord_8211754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876818473056297193272579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199671515928150125848726877 74876818473056297193272579)
  ·
    refine ⟨112315227709584445789908869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74876818473056297193272579 112315227709584445789908869)
    ·
      refine ⟨21059105195547083585607913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112315227709584445789908869 21059105195547083585607913)
      ·
        refine ⟨15794328896660312689205935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21059105195547083585607913 15794328896660312689205935)
        ·
          refine ⟨23691493344990469033808903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794328896660312689205935 23691493344990469033808903)
          ·
            refine ⟨35537240017485703550713355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23691493344990469033808903 35537240017485703550713355)
            ·
              refine ⟨53305860026228555326070033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35537240017485703550713355 53305860026228555326070033)
              ·
                refine ⟨39979395019671416494552525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53305860026228555326070033 39979395019671416494552525)
                ·
                  refine ⟨14992273132376781185457197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39979395019671416494552525 14992273132376781185457197)
                  ·
                    refine ⟨5622102424641292944546449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14992273132376781185457197 5622102424641292944546449)
                    ·
                      refine ⟨4216576818480969708409837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622102424641292944546449 4216576818480969708409837)
                      ·
                        rfl

theorem cell23_8211754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_8211754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211754 prefixEnd_8211754 := by exact prefixLift 8211754
  have htrace : WordTrace (prefixWord ++ tailWord_8211754) baseStart_8211754 baseEnd_8211754 := by
    simpa [prefixWord, tailWord_8211754, baseEnd_8211754] using wordTrace_append hprefix tailTrace_8211754
  have hstable : (prefixWord ++ tailWord_8211754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211754).length < 2 ^ (prefixWord ++ tailWord_8211754).sum := by decide
  have hdescent : baseEnd_8211754 < baseStart_8211754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211767 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 8, 2, 2]
def baseStart_8211767 : Nat := 118140960795 + 8211767 * 2 ^ 59
def prefixEnd_8211767 : Nat := 4983230072969 + 3 ^ 40 * 8211767 * 2
def baseEnd_8211767 : Nat := 4216583493729478157547277

theorem tailTrace_8211767 : CollatzResearch.WordTrace tailWord_8211767 prefixEnd_8211767 4216583493729478157547277 := by
  unfold tailWord_8211767
  simp only [CollatzResearch.WordTrace]
  refine ⟨299507748041178091993313555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199671832027452061328875703 299507748041178091993313555)
  ·
    refine ⟨449261622061767137989970333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299507748041178091993313555 449261622061767137989970333)
    ·
      refine ⟨168473108273162676746238875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449261622061767137989970333 168473108273162676746238875)
      ·
        refine ⟨252709662409744015119358313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168473108273162676746238875 252709662409744015119358313)
        ·
          refine ⟨189532246807308011339518735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252709662409744015119358313 189532246807308011339518735)
          ·
            refine ⟨284298370210962017009278103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189532246807308011339518735 284298370210962017009278103)
            ·
              refine ⟨426447555316443025513917155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284298370210962017009278103 426447555316443025513917155)
              ·
                refine ⟨639671332974664538270875733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426447555316443025513917155 639671332974664538270875733)
                ·
                  refine ⟨7496148433296850057861825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 639671332974664538270875733 7496148433296850057861825)
                  ·
                    refine ⟨5622111324972637543396369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496148433296850057861825 5622111324972637543396369)
                    ·
                      refine ⟨4216583493729478157547277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622111324972637543396369 4216583493729478157547277)
                      ·
                        rfl

theorem cell23_8211767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_8211767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211767 prefixEnd_8211767 := by exact prefixLift 8211767
  have htrace : WordTrace (prefixWord ++ tailWord_8211767) baseStart_8211767 baseEnd_8211767 := by
    simpa [prefixWord, tailWord_8211767, baseEnd_8211767] using wordTrace_append hprefix tailTrace_8211767
  have hstable : (prefixWord ++ tailWord_8211767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211767).length < 2 ^ (prefixWord ++ tailWord_8211767).sum := by decide
  have hdescent : baseEnd_8211767 < baseStart_8211767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211770 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_8211770 : Nat := 118140960795 + 8211770 * 2 ^ 59
def prefixEnd_8211770 : Nat := 4983230072969 + 3 ^ 40 * 8211770 * 2
def baseEnd_8211770 : Nat := 4216585034171441645809763

theorem tailTrace_8211770 : CollatzResearch.WordTrace tailWord_8211770 prefixEnd_8211770 4216585034171441645809763 := by
  unfold tailWord_8211770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876964365041805876418191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199671904973444815670448509 74876964365041805876418191)
  ·
    refine ⟨112315446547562708814627287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74876964365041805876418191 112315446547562708814627287)
    ·
      refine ⟨168473169821344063221940931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112315446547562708814627287 168473169821344063221940931)
      ·
        refine ⟨252709754732016094832911397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168473169821344063221940931 252709754732016094832911397)
        ·
          refine ⟨47383079012253017781170887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252709754732016094832911397 47383079012253017781170887)
          ·
            refine ⟨71074618518379526671756331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47383079012253017781170887 71074618518379526671756331)
            ·
              refine ⟨106611927777569290007634497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71074618518379526671756331 106611927777569290007634497)
              ·
                refine ⟨79958945833176967505725873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106611927777569290007634497 79958945833176967505725873)
                ·
                  refine ⟨59969209374882725629294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79958945833176967505725873 59969209374882725629294405)
                  ·
                    refine ⟨11244226757790511055492701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59969209374882725629294405 11244226757790511055492701)
                    ·
                      refine ⟨4216585034171441645809763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244226757790511055492701 4216585034171441645809763)
                      ·
                        rfl

theorem cell23_8211770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_8211770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211770 prefixEnd_8211770 := by exact prefixLift 8211770
  have htrace : WordTrace (prefixWord ++ tailWord_8211770) baseStart_8211770 baseEnd_8211770 := by
    simpa [prefixWord, tailWord_8211770, baseEnd_8211770] using wordTrace_append hprefix tailTrace_8211770
  have hstable : (prefixWord ++ tailWord_8211770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211770).length < 2 ^ (prefixWord ++ tailWord_8211770).sum := by decide
  have hdescent : baseEnd_8211770 < baseStart_8211770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211782 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_8211782 : Nat := 118140960795 + 8211782 * 2 ^ 59
def prefixEnd_8211782 : Nat := 4983230072969 + 3 ^ 40 * 8211782 * 2
def baseEnd_8211782 : Nat := 4216591195939295598859709

theorem tailTrace_8211782 : CollatzResearch.WordTrace tailWord_8211782 prefixEnd_8211782 4216591195939295598859709 := by
  unfold tailWord_8211782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359634223003867173597175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199672196757415833036739733 9359634223003867173597175)
  ·
    refine ⟨14039451334505800760395763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9359634223003867173597175 14039451334505800760395763)
    ·
      refine ⟨21059177001758701140593645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039451334505800760395763 21059177001758701140593645)
      ·
        refine ⟨7897191375659512927722617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21059177001758701140593645 7897191375659512927722617)
        ·
          refine ⟨5922893531744634695791963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897191375659512927722617 5922893531744634695791963)
          ·
            refine ⟨8884340297616952043687945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922893531744634695791963 8884340297616952043687945)
            ·
              refine ⟨6663255223212714032765959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884340297616952043687945 6663255223212714032765959)
              ·
                refine ⟨9994882834819071049148939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663255223212714032765959 9994882834819071049148939)
                ·
                  refine ⟨14992324252228606573723409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994882834819071049148939 14992324252228606573723409)
                  ·
                    refine ⟨11244243189171454930292557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992324252228606573723409 11244243189171454930292557)
                    ·
                      refine ⟨4216591195939295598859709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244243189171454930292557 4216591195939295598859709)
                      ·
                        rfl

theorem cell23_8211782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_8211782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211782 prefixEnd_8211782 := by exact prefixLift 8211782
  have htrace : WordTrace (prefixWord ++ tailWord_8211782) baseStart_8211782 baseEnd_8211782 := by
    simpa [prefixWord, tailWord_8211782, baseEnd_8211782] using wordTrace_append hprefix tailTrace_8211782
  have hstable : (prefixWord ++ tailWord_8211782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211782).length < 2 ^ (prefixWord ++ tailWord_8211782).sum := by decide
  have hdescent : baseEnd_8211782 < baseStart_8211782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211800 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_8211800 : Nat := 118140960795 + 8211800 * 2 ^ 59
def prefixEnd_8211800 : Nat := 4983230072969 + 3 ^ 40 * 8211800 * 2
def baseEnd_8211800 : Nat := 4216600438591076528434625

theorem tailTrace_8211800 : CollatzResearch.WordTrace tailWord_8211800 prefixEnd_8211800 4216600438591076528434625 := by
  unfold tailWord_8211800
  simp only [CollatzResearch.WordTrace]
  refine ⟨149754475825029269314632427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199672634433372359086176569 149754475825029269314632427)
  ·
    refine ⟨224631713737543903971948641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149754475825029269314632427 224631713737543903971948641)
    ·
      refine ⟨168473785303157927978961481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224631713737543903971948641 168473785303157927978961481)
      ·
        refine ⟨126355338977368445984221111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168473785303157927978961481 126355338977368445984221111)
        ·
          refine ⟨189533008466052668976331667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126355338977368445984221111 189533008466052668976331667)
          ·
            refine ⟨284299512699079003464497501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189533008466052668976331667 284299512699079003464497501)
            ·
              refine ⟨106612317262154626299186563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284299512699079003464497501 106612317262154626299186563)
              ·
                refine ⟨159918475893231939448779845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106612317262154626299186563 159918475893231939448779845)
                ·
                  refine ⟨29984714229980988646646221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159918475893231939448779845 29984714229980988646646221)
                  ·
                    refine ⟨11244267836242870742492333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29984714229980988646646221 11244267836242870742492333)
                    ·
                      refine ⟨4216600438591076528434625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244267836242870742492333 4216600438591076528434625)
                      ·
                        rfl

theorem cell23_8211800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_8211800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211800 prefixEnd_8211800 := by exact prefixLift 8211800
  have htrace : WordTrace (prefixWord ++ tailWord_8211800) baseStart_8211800 baseEnd_8211800 := by
    simpa [prefixWord, tailWord_8211800, baseEnd_8211800] using wordTrace_append hprefix tailTrace_8211800
  have hstable : (prefixWord ++ tailWord_8211800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211800).length < 2 ^ (prefixWord ++ tailWord_8211800).sum := by decide
  have hdescent : baseEnd_8211800 < baseStart_8211800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211818 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_8211818 : Nat := 118140960795 + 8211818 * 2 ^ 59
def prefixEnd_8211818 : Nat := 4983230072969 + 3 ^ 40 * 8211818 * 2
def baseEnd_8211818 : Nat := 4216609681242857458009543

theorem tailTrace_8211818 : CollatzResearch.WordTrace tailWord_8211818 prefixEnd_8211818 4216609681242857458009543 := by
  unfold tailWord_8211818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74877402040998331925855027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199673072109328885135613405 74877402040998331925855027)
  ·
    refine ⟨112316103061497497888782541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74877402040998331925855027 112316103061497497888782541)
    ·
      refine ⟨42118538648061561708293453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112316103061497497888782541 42118538648061561708293453)
      ·
        refine ⟨15794451993023085640610045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42118538648061561708293453 15794451993023085640610045)
        ·
          refine ⟨5922919497383657115228767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15794451993023085640610045 5922919497383657115228767)
          ·
            refine ⟨8884379246075485672843151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922919497383657115228767 8884379246075485672843151)
            ·
              refine ⟨13326568869113228509264727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884379246075485672843151 13326568869113228509264727)
              ·
                refine ⟨19989853303669842763897091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326568869113228509264727 19989853303669842763897091)
                ·
                  refine ⟨29984779955504764145845637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19989853303669842763897091 29984779955504764145845637)
                  ·
                    refine ⟨5622146241657143277346057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29984779955504764145845637 5622146241657143277346057)
                    ·
                      refine ⟨4216609681242857458009543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622146241657143277346057 4216609681242857458009543)
                      ·
                        rfl

theorem cell23_8211818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_8211818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211818 prefixEnd_8211818 := by exact prefixLift 8211818
  have htrace : WordTrace (prefixWord ++ tailWord_8211818) baseStart_8211818 baseEnd_8211818 := by
    simpa [prefixWord, tailWord_8211818, baseEnd_8211818] using wordTrace_append hprefix tailTrace_8211818
  have hstable : (prefixWord ++ tailWord_8211818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211818).length < 2 ^ (prefixWord ++ tailWord_8211818).sum := by decide
  have hdescent : baseEnd_8211818 < baseStart_8211818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211820 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_8211820 : Nat := 118140960795 + 8211820 * 2 ^ 59
def prefixEnd_8211820 : Nat := 4983230072969 + 3 ^ 40 * 8211820 * 2
def baseEnd_8211820 : Nat := 1405536902734722150061511

theorem tailTrace_8211820 : CollatzResearch.WordTrace tailWord_8211820 prefixEnd_8211820 1405536902734722150061511 := by
  unfold tailWord_8211820
  simp only [CollatzResearch.WordTrace]
  refine ⟨149754840554993041022496457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199673120739990721363328609 149754840554993041022496457)
  ·
    refine ⟨112316130416244780766872343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149754840554993041022496457 112316130416244780766872343)
    ·
      refine ⟨168474195624367171150308515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112316130416244780766872343 168474195624367171150308515)
      ·
        refine ⟨252711293436550756725462773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168474195624367171150308515 252711293436550756725462773)
        ·
          refine ⟨23691683759676633443012135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252711293436550756725462773 23691683759676633443012135)
          ·
            refine ⟨35537525639514950164518203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23691683759676633443012135 35537525639514950164518203)
            ·
              refine ⟨53306288459272425246777305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35537525639514950164518203 53306288459272425246777305)
              ·
                refine ⟨39979716344454318935082979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53306288459272425246777305 39979716344454318935082979)
                ·
                  refine ⟨59969574516681478402624469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39979716344454318935082979 59969574516681478402624469)
                  ·
                    refine ⟨1405536902734722150061511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59969574516681478402624469 1405536902734722150061511)
                    ·
                      rfl

theorem cell23_8211820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_8211820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211820 prefixEnd_8211820 := by exact prefixLift 8211820
  have htrace : WordTrace (prefixWord ++ tailWord_8211820) baseStart_8211820 baseEnd_8211820 := by
    simpa [prefixWord, tailWord_8211820, baseEnd_8211820] using wordTrace_append hprefix tailTrace_8211820
  have hstable : (prefixWord ++ tailWord_8211820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211820).length < 2 ^ (prefixWord ++ tailWord_8211820).sum := by decide
  have hdescent : baseEnd_8211820 < baseStart_8211820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211840 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_8211840 : Nat := 118140960795 + 8211840 * 2 ^ 59
def prefixEnd_8211840 : Nat := 4983230072969 + 3 ^ 40 * 8211840 * 2
def baseEnd_8211840 : Nat := 4216620977817256371934441

theorem tailTrace_8211840 : CollatzResearch.WordTrace tailWord_8211840 prefixEnd_8211840 4216620977817256371934441 := by
  unfold tailWord_8211840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149755205284956812730360487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199673607046609083640480649 149755205284956812730360487)
  ·
    refine ⟨224632807927435219095540731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149755205284956812730360487 224632807927435219095540731)
    ·
      refine ⟨336949211891152828643311097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224632807927435219095540731 336949211891152828643311097)
      ·
        refine ⟨252711908918364621482483323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336949211891152828643311097 252711908918364621482483323)
        ·
          refine ⟨379067863377546932223724985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252711908918364621482483323 379067863377546932223724985)
          ·
            refine ⟨284300897533160199167793739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379067863377546932223724985 284300897533160199167793739)
            ·
              refine ⟨426451346299740298751690609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284300897533160199167793739 426451346299740298751690609)
              ·
                refine ⟨319838509724805224063767957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426451346299740298751690609 319838509724805224063767957)
                ·
                  refine ⟨14992430143350244877989123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319838509724805224063767957 14992430143350244877989123)
                  ·
                    refine ⟨22488645215025367316983685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14992430143350244877989123 22488645215025367316983685)
                    ·
                      refine ⟨4216620977817256371934441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22488645215025367316983685 4216620977817256371934441)
                      ·
                        rfl

theorem cell23_8211840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_8211840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211840 prefixEnd_8211840 := by exact prefixLift 8211840
  have htrace : WordTrace (prefixWord ++ tailWord_8211840) baseStart_8211840 baseEnd_8211840 := by
    simpa [prefixWord, tailWord_8211840, baseEnd_8211840] using wordTrace_append hprefix tailTrace_8211840
  have hstable : (prefixWord ++ tailWord_8211840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211840).length < 2 ^ (prefixWord ++ tailWord_8211840).sum := by decide
  have hdescent : baseEnd_8211840 < baseStart_8211840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211841 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 5]
def baseStart_8211841 : Nat := 118140960795 + 8211841 * 2 ^ 59
def prefixEnd_8211841 : Nat := 4983230072969 + 3 ^ 40 * 8211841 * 2
def baseEnd_8211841 : Nat := 468513499033101207557993

theorem tailTrace_8211841 : CollatzResearch.WordTrace tailWord_8211841 prefixEnd_8211841 468513499033101207557993 := by
  unfold tailWord_8211841
  simp only [CollatzResearch.WordTrace]
  refine ⟨299510447042910002631507377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199673631361940001754338251 299510447042910002631507377)
  ·
    refine ⟨224632835282182501973630533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299510447042910002631507377 224632835282182501973630533)
    ·
      refine ⟨42118656615409219120055725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224632835282182501973630533 42118656615409219120055725)
      ·
        refine ⟨15794496230778457170020897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42118656615409219120055725 15794496230778457170020897)
        ·
          refine ⟨11845872173083842877515673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15794496230778457170020897 11845872173083842877515673)
          ·
            refine ⟨8884404129812882158136755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11845872173083842877515673 8884404129812882158136755)
            ·
              refine ⟨13326606194719323237205133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884404129812882158136755 13326606194719323237205133)
              ·
                refine ⟨4997477323019746213951925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13326606194719323237205133 4997477323019746213951925)
                ·
                  refine ⟨468513499033101207557993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997477323019746213951925 468513499033101207557993)
                  ·
                    rfl

theorem cell23_8211841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 5].length) (baseStart_8211841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211841 prefixEnd_8211841 := by exact prefixLift 8211841
  have htrace : WordTrace (prefixWord ++ tailWord_8211841) baseStart_8211841 baseEnd_8211841 := by
    simpa [prefixWord, tailWord_8211841, baseEnd_8211841] using wordTrace_append hprefix tailTrace_8211841
  have hstable : (prefixWord ++ tailWord_8211841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211841).length < 2 ^ (prefixWord ++ tailWord_8211841).sum := by decide
  have hdescent : baseEnd_8211841 < baseStart_8211841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211854 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_8211854 : Nat := 118140960795 + 8211854 * 2 ^ 59
def prefixEnd_8211854 : Nat := 4983230072969 + 3 ^ 40 * 8211854 * 2
def baseEnd_8211854 : Nat := 1405542722182139772386459

theorem tailTrace_8211854 : CollatzResearch.WordTrace tailWord_8211854 prefixEnd_8211854 1405542722182139772386459 := by
  unfold tailWord_8211854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37438865148982863231466327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199673947461241937234487077 37438865148982863231466327)
  ·
    refine ⟨56158297723474294847199491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37438865148982863231466327 56158297723474294847199491)
    ·
      refine ⟨84237446585211442270799237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56158297723474294847199491 84237446585211442270799237)
      ·
        refine ⟨15794521234727145425774857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84237446585211442270799237 15794521234727145425774857)
        ·
          refine ⟨11845890926045359069331143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15794521234727145425774857 11845890926045359069331143)
          ·
            refine ⟨17768836389068038603996715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845890926045359069331143 17768836389068038603996715)
            ·
              refine ⟨26653254583602057905995073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17768836389068038603996715 26653254583602057905995073)
              ·
                refine ⟨19989940937701543429496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26653254583602057905995073 19989940937701543429496305)
                ·
                  refine ⟨14992455703276157572122229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19989940937701543429496305 14992455703276157572122229)
                  ·
                    refine ⟨1405542722182139772386459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14992455703276157572122229 1405542722182139772386459)
                    ·
                      rfl

theorem cell23_8211854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_8211854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211854 prefixEnd_8211854 := by exact prefixLift 8211854
  have htrace : WordTrace (prefixWord ++ tailWord_8211854) baseStart_8211854 baseEnd_8211854 := by
    simpa [prefixWord, tailWord_8211854, baseEnd_8211854] using wordTrace_append hprefix tailTrace_8211854
  have hstable : (prefixWord ++ tailWord_8211854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211854).length < 2 ^ (prefixWord ++ tailWord_8211854).sum := by decide
  have hdescent : baseEnd_8211854 < baseStart_8211854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211858 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_8211858 : Nat := 118140960795 + 8211858 * 2 ^ 59
def prefixEnd_8211858 : Nat := 4983230072969 + 3 ^ 40 * 8211858 * 2
def baseEnd_8211858 : Nat := 468514468941004144612151

theorem tailTrace_8211858 : CollatzResearch.WordTrace tailWord_8211858 prefixEnd_8211858 468514468941004144612151 := by
  unfold tailWord_8211858
  simp only [CollatzResearch.WordTrace]
  refine ⟨74877766770962103633719057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199674044722565609689917485 74877766770962103633719057)
  ·
    refine ⟨56158325078221577725289293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74877766770962103633719057 56158325078221577725289293)
    ·
      refine ⟨21059371904333091646983485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56158325078221577725289293 21059371904333091646983485)
      ·
        refine ⟨7897264464124909367618807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21059371904333091646983485 7897264464124909367618807)
        ·
          refine ⟨11845896696187364051428211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7897264464124909367618807 11845896696187364051428211)
          ·
            refine ⟨17768845044281046077142317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845896696187364051428211 17768845044281046077142317)
            ·
              refine ⟨6663316891605392278928369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17768845044281046077142317 6663316891605392278928369)
              ·
                refine ⟨4997487668704044209196277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663316891605392278928369 4997487668704044209196277)
                ·
                  refine ⟨468514468941004144612151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997487668704044209196277 468514468941004144612151)
                  ·
                    rfl

theorem cell23_8211858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_8211858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211858 prefixEnd_8211858 := by exact prefixLift 8211858
  have htrace : WordTrace (prefixWord ++ tailWord_8211858) baseStart_8211858 baseEnd_8211858 := by
    simpa [prefixWord, tailWord_8211858, baseEnd_8211858] using wordTrace_append hprefix tailTrace_8211858
  have hstable : (prefixWord ++ tailWord_8211858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211858).length < 2 ^ (prefixWord ++ tailWord_8211858).sum := by decide
  have hdescent : baseEnd_8211858 < baseStart_8211858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211941 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_8211941 : Nat := 118140960795 + 8211941 * 2 ^ 59
def prefixEnd_8211941 : Nat := 4983230072969 + 3 ^ 40 * 8211941 * 2
def baseEnd_8211941 : Nat := 4216672839363360476771477

theorem tailTrace_8211941 : CollatzResearch.WordTrace tailWord_8211941 prefixEnd_8211941 4216672839363360476771477 := by
  unfold tailWord_8211941
  simp only [CollatzResearch.WordTrace]
  refine ⟨299514094342547719710147677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199676062895031813140098451 299514094342547719710147677)
  ·
    refine ⟨112317785378455394891305379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299514094342547719710147677 112317785378455394891305379)
    ·
      refine ⟨168476678067683092336958069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112317785378455394891305379 168476678067683092336958069)
      ·
        refine ⟨15794688568845289906589819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168476678067683092336958069 15794688568845289906589819)
        ·
          refine ⟨23692032853267934859884729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794688568845289906589819 23692032853267934859884729)
          ·
            refine ⟨17769024639950951144913547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23692032853267934859884729 17769024639950951144913547)
            ·
              refine ⟨26653536959926426717370321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17769024639950951144913547 26653536959926426717370321)
              ·
                refine ⟨19990152719944820038027741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26653536959926426717370321 19990152719944820038027741)
                ·
                  refine ⟨7496307269979307514260403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19990152719944820038027741 7496307269979307514260403)
                  ·
                    refine ⟨11244460904968961271390605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496307269979307514260403 11244460904968961271390605)
                    ·
                      refine ⟨4216672839363360476771477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244460904968961271390605 4216672839363360476771477)
                      ·
                        rfl

theorem cell23_8211941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_8211941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211941 prefixEnd_8211941 := by exact prefixLift 8211941
  have htrace : WordTrace (prefixWord ++ tailWord_8211941) baseStart_8211941 baseEnd_8211941 := by
    simpa [prefixWord, tailWord_8211941, baseEnd_8211941] using wordTrace_append hprefix tailTrace_8211941
  have hstable : (prefixWord ++ tailWord_8211941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211941).length < 2 ^ (prefixWord ++ tailWord_8211941).sum := by decide
  have hdescent : baseEnd_8211941 < baseStart_8211941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211947 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 8, 2]
def baseStart_8211947 : Nat := 118140960795 + 8211947 * 2 ^ 59
def prefixEnd_8211947 : Nat := 4983230072969 + 3 ^ 40 * 8211947 * 2
def baseEnd_8211947 : Nat := 4216675920247287453296449

theorem tailTrace_8211947 : CollatzResearch.WordTrace tailWord_8211947 prefixEnd_8211947 4216675920247287453296449 := by
  unfold tailWord_8211947
  simp only [CollatzResearch.WordTrace]
  refine ⟨299514313180525982734866095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199676208787017321823244063 299514313180525982734866095)
  ·
    refine ⟨449271469770788974102299143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299514313180525982734866095 449271469770788974102299143)
    ·
      refine ⟨673907204656183461153448715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449271469770788974102299143 673907204656183461153448715)
      ·
        refine ⟨1010860806984275191730173073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673907204656183461153448715 1010860806984275191730173073)
        ·
          refine ⟨758145605238206393797629805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010860806984275191730173073 758145605238206393797629805)
          ·
            refine ⟨284304601964327397674111177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758145605238206393797629805 284304601964327397674111177)
            ·
              refine ⟨213228451473245548255583383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284304601964327397674111177 213228451473245548255583383)
              ·
                refine ⟨319842677209868322383375075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213228451473245548255583383 319842677209868322383375075)
                ·
                  refine ⟨479764015814802483575062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319842677209868322383375075 479764015814802483575062613)
                  ·
                    refine ⟨5622234560329716604395265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 479764015814802483575062613 5622234560329716604395265)
                    ·
                      refine ⟨4216675920247287453296449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622234560329716604395265 4216675920247287453296449)
                      ·
                        rfl

theorem cell23_8211947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8, 2].length) (baseStart_8211947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211947 prefixEnd_8211947 := by exact prefixLift 8211947
  have htrace : WordTrace (prefixWord ++ tailWord_8211947) baseStart_8211947 baseEnd_8211947 := by
    simpa [prefixWord, tailWord_8211947, baseEnd_8211947] using wordTrace_append hprefix tailTrace_8211947
  have hstable : (prefixWord ++ tailWord_8211947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211947).length < 2 ^ (prefixWord ++ tailWord_8211947).sum := by decide
  have hdescent : baseEnd_8211947 < baseStart_8211947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211958 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_8211958 : Nat := 118140960795 + 8211958 * 2 ^ 59
def prefixEnd_8211958 : Nat := 4983230072969 + 3 ^ 40 * 8211958 * 2
def baseEnd_8211958 : Nat := 4216681568534486910258899

theorem tailTrace_8211958 : CollatzResearch.WordTrace tailWord_8211958 prefixEnd_8211958 4216681568534486910258899 := by
  unfold tailWord_8211958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18719669648967883225844783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199676476255657421075677685 18719669648967883225844783)
  ·
    refine ⟨28079504473451824838767175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18719669648967883225844783 28079504473451824838767175)
    ·
      refine ⟨42119256710177737258150763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28079504473451824838767175 42119256710177737258150763)
      ·
        refine ⟨63178885065266605887226145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42119256710177737258150763 63178885065266605887226145)
        ·
          refine ⟨47384163798949954415419609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63178885065266605887226145 47384163798949954415419609)
          ·
            refine ⟨35538122849212465811564707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47384163798949954415419609 35538122849212465811564707)
            ·
              refine ⟨53307184273818698717347061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35538122849212465811564707 53307184273818698717347061)
              ·
                refine ⟨4997548525670503004751287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53307184273818698717347061 4997548525670503004751287)
                ·
                  refine ⟨7496322788505754507126931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997548525670503004751287 7496322788505754507126931)
                  ·
                    refine ⟨11244484182758631760690397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496322788505754507126931 11244484182758631760690397)
                    ·
                      refine ⟨4216681568534486910258899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244484182758631760690397 4216681568534486910258899)
                      ·
                        rfl

theorem cell23_8211958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_8211958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211958 prefixEnd_8211958 := by exact prefixLift 8211958
  have htrace : WordTrace (prefixWord ++ tailWord_8211958) baseStart_8211958 baseEnd_8211958 := by
    simpa [prefixWord, tailWord_8211958, baseEnd_8211958] using wordTrace_append hprefix tailTrace_8211958
  have hstable : (prefixWord ++ tailWord_8211958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211958).length < 2 ^ (prefixWord ++ tailWord_8211958).sum := by decide
  have hdescent : baseEnd_8211958 < baseStart_8211958 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8211967 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_8211967 : Nat := 118140960795 + 8211967 * 2 ^ 59
def prefixEnd_8211967 : Nat := 4983230072969 + 3 ^ 40 * 8211967 * 2
def baseEnd_8211967 : Nat := 4216686189860377375046357

theorem tailTrace_8211967 : CollatzResearch.WordTrace tailWord_8211967 prefixEnd_8211967 4216686189860377375046357 := by
  unfold tailWord_8211967
  simp only [CollatzResearch.WordTrace]
  refine ⟨299515042640453526150594155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199676695093635684100396103 299515042640453526150594155)
  ·
    refine ⟨449272563960680289225891233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299515042640453526150594155 449272563960680289225891233)
    ·
      refine ⟨336954422970510216919418425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449272563960680289225891233 336954422970510216919418425)
      ·
        refine ⟨252715817227882662689563819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336954422970510216919418425 252715817227882662689563819)
        ·
          refine ⟨379073725841823994034345729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252715817227882662689563819 379073725841823994034345729)
          ·
            refine ⟨284305294381367995525759297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379073725841823994034345729 284305294381367995525759297)
            ·
              refine ⟨213228970786025996644319473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284305294381367995525759297 213228970786025996644319473)
              ·
                refine ⟨159921728089519497483239605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213228970786025996644319473 159921728089519497483239605)
                ·
                  refine ⟨14992662008392452889053713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159921728089519497483239605 14992662008392452889053713)
                  ·
                    refine ⟨11244496506294339666790285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992662008392452889053713 11244496506294339666790285)
                    ·
                      refine ⟨4216686189860377375046357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244496506294339666790285 4216686189860377375046357)
                      ·
                        rfl

theorem cell23_8211967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_8211967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8211967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8211967 prefixEnd_8211967 := by exact prefixLift 8211967
  have htrace : WordTrace (prefixWord ++ tailWord_8211967) baseStart_8211967 baseEnd_8211967 := by
    simpa [prefixWord, tailWord_8211967, baseEnd_8211967] using wordTrace_append hprefix tailTrace_8211967
  have hstable : (prefixWord ++ tailWord_8211967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8211967).length < 2 ^ (prefixWord ++ tailWord_8211967).sum := by decide
  have hdescent : baseEnd_8211967 < baseStart_8211967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8211967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212001 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_8212001 : Nat := 118140960795 + 8212001 * 2 ^ 59
def prefixEnd_8212001 : Nat := 4983230072969 + 3 ^ 40 * 8212001 * 2
def baseEnd_8212001 : Nat := 4216703648202630242021201

theorem tailTrace_8212001 : CollatzResearch.WordTrace tailWord_8212001 prefixEnd_8212001 4216703648202630242021201 := by
  unfold tailWord_8212001
  simp only [CollatzResearch.WordTrace]
  refine ⟨299516282722330349957331857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199677521814886899971554571 299516282722330349957331857)
  ·
    refine ⟨224637212041747762467998893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299516282722330349957331857 224637212041747762467998893)
    ·
      refine ⟨84238954515655410925499585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224637212041747762467998893 84238954515655410925499585)
      ·
        refine ⟨63179215886741558194124689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84238954515655410925499585 63179215886741558194124689)
        ·
          refine ⟨47384411915056168645593517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63179215886741558194124689 47384411915056168645593517)
          ·
            refine ⟨17769154468146063242097569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47384411915056168645593517 17769154468146063242097569)
            ·
              refine ⟨13326865851109547431573177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17769154468146063242097569 13326865851109547431573177)
              ·
                refine ⟨9995149388332160573679883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13326865851109547431573177 9995149388332160573679883)
                ·
                  refine ⟨14992724082498240860519825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995149388332160573679883 14992724082498240860519825)
                  ·
                    refine ⟨11244543061873680645389869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14992724082498240860519825 11244543061873680645389869)
                    ·
                      refine ⟨4216703648202630242021201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244543061873680645389869 4216703648202630242021201)
                      ·
                        rfl

theorem cell23_8212001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_8212001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212001 prefixEnd_8212001 := by exact prefixLift 8212001
  have htrace : WordTrace (prefixWord ++ tailWord_8212001) baseStart_8212001 baseEnd_8212001 := by
    simpa [prefixWord, tailWord_8212001, baseEnd_8212001] using wordTrace_append hprefix tailTrace_8212001
  have hstable : (prefixWord ++ tailWord_8212001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212001).length < 2 ^ (prefixWord ++ tailWord_8212001).sum := by decide
  have hdescent : baseEnd_8212001 < baseStart_8212001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212037 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_8212037 : Nat := 118140960795 + 8212037 * 2 ^ 59
def prefixEnd_8212037 : Nat := 4983230072969 + 3 ^ 40 * 8212037 * 2
def baseEnd_8212037 : Nat := 4216722133506192101171035

theorem tailTrace_8212037 : CollatzResearch.WordTrace tailWord_8212037 prefixEnd_8212037 4216722133506192101171035 := by
  unfold tailWord_8212037
  simp only [CollatzResearch.WordTrace]
  refine ⟨299517595750199928105642365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199678397166799952070428243 299517595750199928105642365)
  ·
    refine ⟨112319098406324973039615887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299517595750199928105642365 112319098406324973039615887)
    ·
      refine ⟨168478647609487459559423831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112319098406324973039615887 168478647609487459559423831)
      ·
        refine ⟨252717971414231189339135747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168478647609487459559423831 252717971414231189339135747)
        ·
          refine ⟨379076957121346784008703621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252717971414231189339135747 379076957121346784008703621)
          ·
            refine ⟨71076929460252522001631929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379076957121346784008703621 71076929460252522001631929)
            ·
              refine ⟨53307697095189391501223947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71076929460252522001631929 53307697095189391501223947)
              ·
                refine ⟨79961545642784087251835921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53307697095189391501223947 79961545642784087251835921)
                ·
                  refine ⟨59971159232088065438876941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79961545642784087251835921 59971159232088065438876941)
                  ·
                    refine ⟨22489184712033024539578853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59971159232088065438876941 22489184712033024539578853)
                    ·
                      refine ⟨4216722133506192101171035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22489184712033024539578853 4216722133506192101171035)
                      ·
                        rfl

theorem cell23_8212037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_8212037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212037 prefixEnd_8212037 := by exact prefixLift 8212037
  have htrace : WordTrace (prefixWord ++ tailWord_8212037) baseStart_8212037 baseEnd_8212037 := by
    simpa [prefixWord, tailWord_8212037, baseEnd_8212037] using wordTrace_append hprefix tailTrace_8212037
  have hstable : (prefixWord ++ tailWord_8212037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212037).length < 2 ^ (prefixWord ++ tailWord_8212037).sum := by decide
  have hdescent : baseEnd_8212037 < baseStart_8212037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212071 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_8212071 : Nat := 118140960795 + 8212071 * 2 ^ 59
def prefixEnd_8212071 : Nat := 4983230072969 + 3 ^ 40 * 8212071 * 2
def baseEnd_8212071 : Nat := 4216739591848444968145879

theorem tailTrace_8212071 : CollatzResearch.WordTrace tailWord_8212071 prefixEnd_8212071 4216739591848444968145879 := by
  unfold tailWord_8212071
  simp only [CollatzResearch.WordTrace]
  refine ⟨299518835832076751912380067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199679223888051167941586711 299518835832076751912380067)
  ·
    refine ⟨449278253748115127868570101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299518835832076751912380067 449278253748115127868570101)
    ·
      refine ⟨42119836288885793237678447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449278253748115127868570101 42119836288885793237678447)
      ·
        refine ⟨63179754433328689856517671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42119836288885793237678447 63179754433328689856517671)
        ·
          refine ⟨94769631649993034784776507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63179754433328689856517671 94769631649993034784776507)
          ·
            refine ⟨142154447474989552177164761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94769631649993034784776507 142154447474989552177164761)
            ·
              refine ⟨106615835606242164132873571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142154447474989552177164761 106615835606242164132873571)
              ·
                refine ⟨159923753409363246199310357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106615835606242164132873571 159923753409363246199310357)
                ·
                  refine ⟨7496425941063902165592673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159923753409363246199310357 7496425941063902165592673)
                  ·
                    refine ⟨5622319455797926624194505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496425941063902165592673 5622319455797926624194505)
                    ·
                      refine ⟨4216739591848444968145879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622319455797926624194505 4216739591848444968145879)
                      ·
                        rfl

theorem cell23_8212071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_8212071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212071 prefixEnd_8212071 := by exact prefixLift 8212071
  have htrace : WordTrace (prefixWord ++ tailWord_8212071) baseStart_8212071 baseEnd_8212071 := by
    simpa [prefixWord, tailWord_8212071, baseEnd_8212071] using wordTrace_append hprefix tailTrace_8212071
  have hstable : (prefixWord ++ tailWord_8212071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212071).length < 2 ^ (prefixWord ++ tailWord_8212071).sum := by decide
  have hdescent : baseEnd_8212071 < baseStart_8212071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212074 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_8212074 : Nat := 118140960795 + 8212074 * 2 ^ 59
def prefixEnd_8212074 : Nat := 4983230072969 + 3 ^ 40 * 8212074 * 2
def baseEnd_8212074 : Nat := 4216741132290408456408365

theorem tailTrace_8212074 : CollatzResearch.WordTrace tailWord_8212074 prefixEnd_8212074 4216741132290408456408365 := by
  unfold tailWord_8212074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74879736312766470856184819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199679296834043922283159517 74879736312766470856184819)
  ·
    refine ⟨112319604469149706284277229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74879736312766470856184819 112319604469149706284277229)
    ·
      refine ⟨42119851675931139856603961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112319604469149706284277229 42119851675931139856603961)
      ·
        refine ⟨31589888756948354892452971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42119851675931139856603961 31589888756948354892452971)
        ·
          refine ⟨47384833135422532338679457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31589888756948354892452971 47384833135422532338679457)
          ·
            refine ⟨35538624851566899254009593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47384833135422532338679457 35538624851566899254009593)
            ·
              refine ⟨26653968638675174440507195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35538624851566899254009593 26653968638675174440507195)
              ·
                refine ⟨39980952958012761660760793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26653968638675174440507195 39980952958012761660760793)
                ·
                  refine ⟨29985714718509571245570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39980952958012761660760793 29985714718509571245570595)
                  ·
                    refine ⟨44978572077764356868355893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29985714718509571245570595 44978572077764356868355893)
                    ·
                      refine ⟨4216741132290408456408365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44978572077764356868355893 4216741132290408456408365)
                      ·
                        rfl

theorem cell23_8212074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_8212074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212074 prefixEnd_8212074 := by exact prefixLift 8212074
  have htrace : WordTrace (prefixWord ++ tailWord_8212074) baseStart_8212074 baseEnd_8212074 := by
    simpa [prefixWord, tailWord_8212074, baseEnd_8212074] using wordTrace_append hprefix tailTrace_8212074
  have hstable : (prefixWord ++ tailWord_8212074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212074).length < 2 ^ (prefixWord ++ tailWord_8212074).sum := by decide
  have hdescent : baseEnd_8212074 < baseStart_8212074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212107 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 7]
def baseStart_8212107 : Nat := 118140960795 + 8212107 * 2 ^ 59
def prefixEnd_8212107 : Nat := 4983230072969 + 3 ^ 40 * 8212107 * 2
def baseEnd_8212107 : Nat := 1405586025717335609098571

theorem tailTrace_8212107 : CollatzResearch.WordTrace tailWord_8212107 prefixEnd_8212107 1405586025717335609098571 := by
  unfold tailWord_8212107
  simp only [CollatzResearch.WordTrace]
  refine ⟨299520148859946330060690575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199680099239964220040460383 299520148859946330060690575)
  ·
    refine ⟨449280223289919495091035863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299520148859946330060690575 449280223289919495091035863)
    ·
      refine ⟨673920334934879242636553795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449280223289919495091035863 673920334934879242636553795)
      ·
        refine ⟨1010880502402318863954830693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673920334934879242636553795 1010880502402318863954830693)
        ·
          refine ⟨189540094200434786991530755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1010880502402318863954830693 189540094200434786991530755)
          ·
            refine ⟨284310141300652180487296133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189540094200434786991530755 284310141300652180487296133)
            ·
              refine ⟨53308151493872283841368025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284310141300652180487296133 53308151493872283841368025)
              ·
                refine ⟨39981113620404212881026019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53308151493872283841368025 39981113620404212881026019)
                ·
                  refine ⟨59971670430606319321539029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39981113620404212881026019 59971670430606319321539029)
                  ·
                    refine ⟨1405586025717335609098571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59971670430606319321539029 1405586025717335609098571)
                    ·
                      rfl

theorem cell23_8212107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_8212107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212107 prefixEnd_8212107 := by exact prefixLift 8212107
  have htrace : WordTrace (prefixWord ++ tailWord_8212107) baseStart_8212107 baseEnd_8212107 := by
    simpa [prefixWord, tailWord_8212107, baseEnd_8212107] using wordTrace_append hprefix tailTrace_8212107
  have hstable : (prefixWord ++ tailWord_8212107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212107).length < 2 ^ (prefixWord ++ tailWord_8212107).sum := by decide
  have hdescent : baseEnd_8212107 < baseStart_8212107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212117 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_8212117 : Nat := 118140960795 + 8212117 * 2 ^ 59
def prefixEnd_8212117 : Nat := 4983230072969 + 3 ^ 40 * 8212117 * 2
def baseEnd_8212117 : Nat := 4216763211958551788170667

theorem tailTrace_8212117 : CollatzResearch.WordTrace tailWord_8212117 prefixEnd_8212117 4216763211958551788170667 := by
  unfold tailWord_8212117
  simp only [CollatzResearch.WordTrace]
  refine ⟨299520513589910101768554605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199680342393273401179036403 299520513589910101768554605)
  ·
    refine ⟨112320192596216288163207977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299520513589910101768554605 112320192596216288163207977)
    ·
      refine ⟨84240144447162216122405983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112320192596216288163207977 84240144447162216122405983)
      ·
        refine ⟨126360216670743324183608975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84240144447162216122405983 126360216670743324183608975)
        ·
          refine ⟨189540325006114986275413463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126360216670743324183608975 189540325006114986275413463)
          ·
            refine ⟨284310487509172479413120195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189540325006114986275413463 284310487509172479413120195)
            ·
              refine ⟨426465731263758719119680293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284310487509172479413120195 426465731263758719119680293)
              ·
                refine ⟨79962324611954759834940055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426465731263758719119680293 79962324611954759834940055)
                ·
                  refine ⟨119943486917932139752410083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79962324611954759834940055 119943486917932139752410083)
                  ·
                    refine ⟨179915230376898209628615125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119943486917932139752410083 179915230376898209628615125)
                    ·
                      refine ⟨4216763211958551788170667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179915230376898209628615125 4216763211958551788170667)
                      ·
                        rfl

theorem cell23_8212117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_8212117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212117 prefixEnd_8212117 := by exact prefixLift 8212117
  have htrace : WordTrace (prefixWord ++ tailWord_8212117) baseStart_8212117 baseEnd_8212117 := by
    simpa [prefixWord, tailWord_8212117, baseEnd_8212117] using wordTrace_append hprefix tailTrace_8212117
  have hstable : (prefixWord ++ tailWord_8212117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212117).length < 2 ^ (prefixWord ++ tailWord_8212117).sum := by decide
  have hdescent : baseEnd_8212117 < baseStart_8212117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212144 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_8212144 : Nat := 118140960795 + 8212144 * 2 ^ 59
def prefixEnd_8212144 : Nat := 4983230072969 + 3 ^ 40 * 8212144 * 2
def baseEnd_8212144 : Nat := 4216777075936223182533043

theorem tailTrace_8212144 : CollatzResearch.WordTrace tailWord_8212144 prefixEnd_8212144 4216777075936223182533043 := by
  unfold tailWord_8212144
  simp only [CollatzResearch.WordTrace]
  refine ⟨149760749180406142689893743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199680998907208190253191657 149760749180406142689893743)
  ·
    refine ⟨224641123770609214034840615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149760749180406142689893743 224641123770609214034840615)
    ·
      refine ⟨336961685655913821052260923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224641123770609214034840615 336961685655913821052260923)
      ·
        refine ⟨505442528483870731578391385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336961685655913821052260923 505442528483870731578391385)
        ·
          refine ⟨379081896362903048683793539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505442528483870731578391385 379081896362903048683793539)
          ·
            refine ⟨568622844544354573025690309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379081896362903048683793539 568622844544354573025690309)
            ·
              refine ⟨106616783352066482442316933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568622844544354573025690309 106616783352066482442316933)
              ·
                refine ⟨19990646878512465457934425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106616783352066482442316933 19990646878512465457934425)
                ·
                  refine ⟨14992985158884349093450819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19990646878512465457934425 14992985158884349093450819)
                  ·
                    refine ⟨22489477738326523640176229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14992985158884349093450819 22489477738326523640176229)
                    ·
                      refine ⟨4216777075936223182533043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22489477738326523640176229 4216777075936223182533043)
                      ·
                        rfl

theorem cell23_8212144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_8212144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212144 prefixEnd_8212144 := by exact prefixLift 8212144
  have htrace : WordTrace (prefixWord ++ tailWord_8212144) baseStart_8212144 baseEnd_8212144 := by
    simpa [prefixWord, tailWord_8212144, baseEnd_8212144] using wordTrace_append hprefix tailTrace_8212144
  have hstable : (prefixWord ++ tailWord_8212144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212144).length < 2 ^ (prefixWord ++ tailWord_8212144).sum := by decide
  have hdescent : baseEnd_8212144 < baseStart_8212144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212174 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_8212174 : Nat := 118140960795 + 8212174 * 2 ^ 59
def prefixEnd_8212174 : Nat := 4983230072969 + 3 ^ 40 * 8212174 * 2
def baseEnd_8212174 : Nat := 4216792480355858065157905

theorem tailTrace_8212174 : CollatzResearch.WordTrace tailWord_8212174 prefixEnd_8212174 4216792480355858065157905 := by
  unfold tailWord_8212174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440324068837950062922447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199681728367135733668919717 37440324068837950062922447)
  ·
    refine ⟨56160486103256925094383671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440324068837950062922447 56160486103256925094383671)
    ·
      refine ⟨84240729154885387641575507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56160486103256925094383671 84240729154885387641575507)
      ·
        refine ⟨126361093732328081462363261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84240729154885387641575507 126361093732328081462363261)
        ·
          refine ⟨47385410149623030548386223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126361093732328081462363261 47385410149623030548386223)
          ·
            refine ⟨71078115224434545822579335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47385410149623030548386223 71078115224434545822579335)
            ·
              refine ⟨106617172836651818733869003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71078115224434545822579335 106617172836651818733869003)
              ·
                refine ⟨159925759254977728100803505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106617172836651818733869003 159925759254977728100803505)
                ·
                  refine ⟨119944319441233296075602629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159925759254977728100803505 119944319441233296075602629)
                  ·
                    refine ⟨22489559895231243014175493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119944319441233296075602629 22489559895231243014175493)
                    ·
                      refine ⟨4216792480355858065157905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22489559895231243014175493 4216792480355858065157905)
                      ·
                        rfl

theorem cell23_8212174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_8212174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212174 prefixEnd_8212174 := by exact prefixLift 8212174
  have htrace : WordTrace (prefixWord ++ tailWord_8212174) baseStart_8212174 baseEnd_8212174 := by
    simpa [prefixWord, tailWord_8212174, baseEnd_8212174] using wordTrace_append hprefix tailTrace_8212174
  have hstable : (prefixWord ++ tailWord_8212174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212174).length < 2 ^ (prefixWord ++ tailWord_8212174).sum := by decide
  have hdescent : baseEnd_8212174 < baseStart_8212174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212221 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_8212221 : Nat := 118140960795 + 8212221 * 2 ^ 59
def prefixEnd_8212221 : Nat := 4983230072969 + 3 ^ 40 * 8212221 * 2
def baseEnd_8212221 : Nat := 4216816613946619381270189

theorem tailTrace_8212221 : CollatzResearch.WordTrace tailWord_8212221 prefixEnd_8212221 4216816613946619381270189 := by
  unfold tailWord_8212221
  simp only [CollatzResearch.WordTrace]
  refine ⟨299524306781533327530340517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199682871187688885020227011 299524306781533327530340517)
  ·
    refine ⟨56160807521537498911938847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299524306781533327530340517 56160807521537498911938847)
    ·
      refine ⟨84241211282306248367908271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56160807521537498911938847 84241211282306248367908271)
      ·
        refine ⟨126361816923459372551862407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84241211282306248367908271 126361816923459372551862407)
        ·
          refine ⟨189542725385189058827793611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126361816923459372551862407 189542725385189058827793611)
          ·
            refine ⟨284314088077783588241690417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189542725385189058827793611 284314088077783588241690417)
            ·
              refine ⟨213235566058337691181267813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284314088077783588241690417 213235566058337691181267813)
              ·
                refine ⟨39981668635938317096487715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213235566058337691181267813 39981668635938317096487715)
                ·
                  refine ⟨59972502953907475644731573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39981668635938317096487715 59972502953907475644731573)
                  ·
                    refine ⟨5622422151928825841693585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59972502953907475644731573 5622422151928825841693585)
                    ·
                      refine ⟨4216816613946619381270189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622422151928825841693585 4216816613946619381270189)
                      ·
                        rfl

theorem cell23_8212221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_8212221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212221 prefixEnd_8212221 := by exact prefixLift 8212221
  have htrace : WordTrace (prefixWord ++ tailWord_8212221) baseStart_8212221 baseEnd_8212221 := by
    simpa [prefixWord, tailWord_8212221, baseEnd_8212221] using wordTrace_append hprefix tailTrace_8212221
  have hstable : (prefixWord ++ tailWord_8212221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212221).length < 2 ^ (prefixWord ++ tailWord_8212221).sum := by decide
  have hdescent : baseEnd_8212221 < baseStart_8212221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212238 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_8212238 : Nat := 118140960795 + 8212238 * 2 ^ 59
def prefixEnd_8212238 : Nat := 4983230072969 + 3 ^ 40 * 8212238 * 2
def baseEnd_8212238 : Nat := 4216825343117745814757611

theorem tailTrace_8212238 : CollatzResearch.WordTrace tailWord_8212238 prefixEnd_8212238 4216825343117745814757611 := by
  unfold tailWord_8212238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37440615852808967429213671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199683284548314492955806245 37440615852808967429213671)
  ·
    refine ⟨56160923779213451143820507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37440615852808967429213671 56160923779213451143820507)
    ·
      refine ⟨84241385668820176715730761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56160923779213451143820507 84241385668820176715730761)
      ·
        refine ⟨63181039251615132536798071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84241385668820176715730761 63181039251615132536798071)
        ·
          refine ⟨94771558877422698805197107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63181039251615132536798071 94771558877422698805197107)
          ·
            refine ⟨142157338316134048207795661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94771558877422698805197107 142157338316134048207795661)
            ·
              refine ⟨53309001868550268077923373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142157338316134048207795661 53309001868550268077923373)
              ·
                refine ⟨19990875700706350529221265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53309001868550268077923373 19990875700706350529221265)
                ·
                  refine ⟨14993156775529762896915949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19990875700706350529221265 14993156775529762896915949)
                  ·
                    refine ⟨5622433790823661086343481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14993156775529762896915949 5622433790823661086343481)
                    ·
                      refine ⟨4216825343117745814757611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622433790823661086343481 4216825343117745814757611)
                      ·
                        rfl

theorem cell23_8212238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_8212238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212238 prefixEnd_8212238 := by exact prefixLift 8212238
  have htrace : WordTrace (prefixWord ++ tailWord_8212238) baseStart_8212238 baseEnd_8212238 := by
    simpa [prefixWord, tailWord_8212238, baseEnd_8212238] using wordTrace_append hprefix tailTrace_8212238
  have hstable : (prefixWord ++ tailWord_8212238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212238).length < 2 ^ (prefixWord ++ tailWord_8212238).sum := by decide
  have hdescent : baseEnd_8212238 < baseStart_8212238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212278 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_8212278 : Nat := 118140960795 + 8212278 * 2 ^ 59
def prefixEnd_8212278 : Nat := 4983230072969 + 3 ^ 40 * 8212278 * 2
def baseEnd_8212278 : Nat := 1405615294114641886085809

theorem tailTrace_8212278 : CollatzResearch.WordTrace tailWord_8212278 prefixEnd_8212278 1405615294114641886085809 := by
  unfold tailWord_8212278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18720399108895426641572843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199684257161551217510110325 18720399108895426641572843)
  ·
    refine ⟨28080598663343139962359265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18720399108895426641572843 28080598663343139962359265)
    ·
      refine ⟨21060448997507354971769449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28080598663343139962359265 21060448997507354971769449)
      ·
        refine ⟨15795336748130516228827087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21060448997507354971769449 15795336748130516228827087)
        ·
          refine ⟨23693005122195774343240631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795336748130516228827087 23693005122195774343240631)
          ·
            refine ⟨35539507683293661514860947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693005122195774343240631 35539507683293661514860947)
            ·
              refine ⟨53309261524940492272291421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539507683293661514860947 53309261524940492272291421)
              ·
                refine ⟨19990973071852684602109283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53309261524940492272291421 19990973071852684602109283)
                ·
                  refine ⟨29986459607779026903163925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19990973071852684602109283 29986459607779026903163925)
                  ·
                    refine ⟨1405615294114641886085809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29986459607779026903163925 1405615294114641886085809)
                    ·
                      rfl

theorem cell23_8212278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_8212278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212278 prefixEnd_8212278 := by exact prefixLift 8212278
  have htrace : WordTrace (prefixWord ++ tailWord_8212278) baseStart_8212278 baseEnd_8212278 := by
    simpa [prefixWord, tailWord_8212278, baseEnd_8212278] using wordTrace_append hprefix tailTrace_8212278
  have hstable : (prefixWord ++ tailWord_8212278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212278).length < 2 ^ (prefixWord ++ tailWord_8212278).sum := by decide
  have hdescent : baseEnd_8212278 < baseStart_8212278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212285 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_8212285 : Nat := 118140960795 + 8212285 * 2 ^ 59
def prefixEnd_8212285 : Nat := 4983230072969 + 3 ^ 40 * 8212285 * 2
def baseEnd_8212285 : Nat := 4216849476708507130869895

theorem tailTrace_8212285 : CollatzResearch.WordTrace tailWord_8212285 prefixEnd_8212285 4216849476708507130869895 := by
  unfold tailWord_8212285
  simp only [CollatzResearch.WordTrace]
  refine ⟨299526641053301466460670309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199684427368867644307113539 299526641053301466460670309)
  ·
    refine ⟨56161245197494024961375683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299526641053301466460670309 56161245197494024961375683)
    ·
      refine ⟨84241867796241037442063525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56161245197494024961375683 84241867796241037442063525)
      ·
        refine ⟨15795350211795194520386911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84241867796241037442063525 15795350211795194520386911)
        ·
          refine ⟨23693025317692791780580367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795350211795194520386911 23693025317692791780580367)
          ·
            refine ⟨35539537976539187670870551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693025317692791780580367 35539537976539187670870551)
            ·
              refine ⟨53309306964808781506305827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539537976539187670870551 53309306964808781506305827)
              ·
                refine ⟨79963960447213172259458741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53309306964808781506305827 79963960447213172259458741)
                ·
                  refine ⟨7496621291926234899324257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79963960447213172259458741 7496621291926234899324257)
                  ·
                    refine ⟨5622465968944676174493193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496621291926234899324257 5622465968944676174493193)
                    ·
                      refine ⟨4216849476708507130869895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622465968944676174493193 4216849476708507130869895)
                      ·
                        rfl

theorem cell23_8212285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_8212285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212285 prefixEnd_8212285 := by exact prefixLift 8212285
  have htrace : WordTrace (prefixWord ++ tailWord_8212285) baseStart_8212285 baseEnd_8212285 := by
    simpa [prefixWord, tailWord_8212285, baseEnd_8212285] using wordTrace_append hprefix tailTrace_8212285
  have hstable : (prefixWord ++ tailWord_8212285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212285).length < 2 ^ (prefixWord ++ tailWord_8212285).sum := by decide
  have hdescent : baseEnd_8212285 < baseStart_8212285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212291 : List Nat := [1, 1, 1, 3, 1, 6, 3, 7]
def baseStart_8212291 : Nat := 118140960795 + 8212291 * 2 ^ 59
def prefixEnd_8212291 : Nat := 4983230072969 + 3 ^ 40 * 8212291 * 2
def baseEnd_8212291 : Nat := 156179724355275337310921

theorem tailTrace_8212291 : CollatzResearch.WordTrace tailWord_8212291 prefixEnd_8212291 156179724355275337310921 := by
  unfold tailWord_8212291
  simp only [CollatzResearch.WordTrace]
  refine ⟨299526859891279729485388727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199684573260853152990259151 299526859891279729485388727)
  ·
    refine ⟨449290289836919594228083091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299526859891279729485388727 449290289836919594228083091)
    ·
      refine ⟨673935434755379391342124637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449290289836919594228083091 673935434755379391342124637)
      ·
        refine ⟨252725788033267271753296739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673935434755379391342124637 252725788033267271753296739)
        ·
          refine ⟨379088682049900907629945109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252725788033267271753296739 379088682049900907629945109)
          ·
            refine ⟨17769781971089105045153677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 379088682049900907629945109 17769781971089105045153677)
            ·
              refine ⟨6663668239158414391932629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17769781971089105045153677 6663668239158414391932629)
              ·
                refine ⟨156179724355275337310921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6663668239158414391932629 156179724355275337310921)
                ·
                  rfl

theorem cell23_8212291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 7].length) (baseStart_8212291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212291 prefixEnd_8212291 := by exact prefixLift 8212291
  have htrace : WordTrace (prefixWord ++ tailWord_8212291) baseStart_8212291 baseEnd_8212291 := by
    simpa [prefixWord, tailWord_8212291, baseEnd_8212291] using wordTrace_append hprefix tailTrace_8212291
  have hstable : (prefixWord ++ tailWord_8212291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212291).length < 2 ^ (prefixWord ++ tailWord_8212291).sum := by decide
  have hdescent : baseEnd_8212291 < baseStart_8212291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212305 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_8212305 : Nat := 118140960795 + 8212305 * 2 ^ 59
def prefixEnd_8212305 : Nat := 4983230072969 + 3 ^ 40 * 8212305 * 2
def baseEnd_8212305 : Nat := 4216859746321597052619803

theorem tailTrace_8212305 : CollatzResearch.WordTrace tailWord_8212305 prefixEnd_8212305 4216859746321597052619803 := by
  unfold tailWord_8212305
  simp only [CollatzResearch.WordTrace]
  refine ⟨299527370513229009876398369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199684913675486006584265579 299527370513229009876398369)
  ·
    refine ⟨224645527884921757407298777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299527370513229009876398369 224645527884921757407298777)
    ·
      refine ⟨168484145913691318055474083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224645527884921757407298777 168484145913691318055474083)
      ·
        refine ⟨252726218870536977083211125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168484145913691318055474083 252726218870536977083211125)
        ·
          refine ⟨23693083019112841601551043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252726218870536977083211125 23693083019112841601551043)
          ·
            refine ⟨35539624528669262402326565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693083019112841601551043 35539624528669262402326565)
            ·
              refine ⟨6663679599125486700436231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35539624528669262402326565 6663679599125486700436231)
              ·
                refine ⟨9995519398688230050654347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663679599125486700436231 9995519398688230050654347)
                ·
                  refine ⟨14993279098032345075981521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995519398688230050654347 14993279098032345075981521)
                  ·
                    refine ⟨11244959323524258806986141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14993279098032345075981521 11244959323524258806986141)
                    ·
                      refine ⟨4216859746321597052619803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11244959323524258806986141 4216859746321597052619803)
                      ·
                        rfl

theorem cell23_8212305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_8212305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212305 prefixEnd_8212305 := by exact prefixLift 8212305
  have htrace : WordTrace (prefixWord ++ tailWord_8212305) baseStart_8212305 baseEnd_8212305 := by
    simpa [prefixWord, tailWord_8212305, baseEnd_8212305] using wordTrace_append hprefix tailTrace_8212305
  have hstable : (prefixWord ++ tailWord_8212305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212305).length < 2 ^ (prefixWord ++ tailWord_8212305).sum := by decide
  have hdescent : baseEnd_8212305 < baseStart_8212305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212342 : List Nat := [5, 1, 1, 3, 3, 1, 2, 7]
def baseStart_8212342 : Nat := 118140960795 + 8212342 * 2 ^ 59
def prefixEnd_8212342 : Nat := 4983230072969 + 3 ^ 40 * 8212342 * 2
def baseEnd_8212342 : Nat := 156180694263178274365079

theorem tailTrace_8212342 : CollatzResearch.WordTrace tailWord_8212342 prefixEnd_8212342 156180694263178274365079 := by
  unfold tailWord_8212342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18720545000880935324718455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199685813342729976796996853 18720545000880935324718455)
  ·
    refine ⟨28080817501321402987077683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18720545000880935324718455 28080817501321402987077683)
    ·
      refine ⟨42121226251982104480616525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28080817501321402987077683 42121226251982104480616525)
      ·
        refine ⟨15795459844493289180231197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42121226251982104480616525 15795459844493289180231197)
        ·
          refine ⟨5923297441684983442586699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15795459844493289180231197 5923297441684983442586699)
          ·
            refine ⟨8884946162527475163880049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923297441684983442586699 8884946162527475163880049)
            ·
              refine ⟨6663709621895606372910037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884946162527475163880049 6663709621895606372910037)
              ·
                refine ⟨156180694263178274365079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6663709621895606372910037 156180694263178274365079)
                ·
                  rfl

theorem cell23_8212342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_8212342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212342 prefixEnd_8212342 := by exact prefixLift 8212342
  have htrace : WordTrace (prefixWord ++ tailWord_8212342) baseStart_8212342 baseEnd_8212342 := by
    simpa [prefixWord, tailWord_8212342, baseEnd_8212342] using wordTrace_append hprefix tailTrace_8212342
  have hstable : (prefixWord ++ tailWord_8212342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212342).length < 2 ^ (prefixWord ++ tailWord_8212342).sum := by decide
  have hdescent : baseEnd_8212342 < baseStart_8212342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212345 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 1, 3, 2]
def baseStart_8212345 : Nat := 118140960795 + 8212345 * 2 ^ 59
def prefixEnd_8212345 : Nat := 4983230072969 + 3 ^ 40 * 8212345 * 2
def baseEnd_8212345 : Nat := 4216880285547776896119619

theorem tailTrace_8212345 : CollatzResearch.WordTrace tailWord_8212345 prefixEnd_8212345 4216880285547776896119619 := by
  unfold tailWord_8212345
  simp only [CollatzResearch.WordTrace]
  refine ⟨299528829433084096707854489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199685886288722731138569659 299528829433084096707854489)
  ·
    refine ⟨224646622074813072530890867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299528829433084096707854489 224646622074813072530890867)
    ·
      refine ⟨336969933112219608796336301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224646622074813072530890867 336969933112219608796336301)
      ·
        refine ⟨126363724917082353298626113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336969933112219608796336301 126363724917082353298626113)
        ·
          refine ⟨94772793687811764973969585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126363724917082353298626113 94772793687811764973969585)
          ·
            refine ⟨71079595265858823730477189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94772793687811764973969585 71079595265858823730477189)
            ·
              refine ⟨13327424112348529449464473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71079595265858823730477189 13327424112348529449464473)
              ·
                refine ⟨9995568084261397087098355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13327424112348529449464473 9995568084261397087098355)
                ·
                  refine ⟨14993352126392095630647533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995568084261397087098355 14993352126392095630647533)
                  ·
                    refine ⟨5622507047397035861492825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14993352126392095630647533 5622507047397035861492825)
                    ·
                      refine ⟨4216880285547776896119619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622507047397035861492825 4216880285547776896119619)
                      ·
                        rfl

theorem cell23_8212345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_8212345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212345 prefixEnd_8212345 := by exact prefixLift 8212345
  have htrace : WordTrace (prefixWord ++ tailWord_8212345) baseStart_8212345 baseEnd_8212345 := by
    simpa [prefixWord, tailWord_8212345, baseEnd_8212345] using wordTrace_append hprefix tailTrace_8212345
  have hstable : (prefixWord ++ tailWord_8212345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212345).length < 2 ^ (prefixWord ++ tailWord_8212345).sum := by decide
  have hdescent : baseEnd_8212345 < baseStart_8212345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212353 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_8212353 : Nat := 118140960795 + 8212353 * 2 ^ 59
def prefixEnd_8212353 : Nat := 4983230072969 + 3 ^ 40 * 8212353 * 2
def baseEnd_8212353 : Nat := 4216884393393012864819583

theorem tailTrace_8212353 : CollatzResearch.WordTrace tailWord_8212353 prefixEnd_8212353 4216884393393012864819583 := by
  unfold tailWord_8212353
  simp only [CollatzResearch.WordTrace]
  refine ⟨299529121217055114074145713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199686080811370076049430475 299529121217055114074145713)
  ·
    refine ⟨224646840912791335555609285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299529121217055114074145713 224646840912791335555609285)
    ·
      refine ⟨42121282671148375416676741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224646840912791335555609285 42121282671148375416676741)
      ·
        refine ⟨7897740500840320390626889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42121282671148375416676741 7897740500840320390626889)
        ·
          refine ⟨5923305375630240292970167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7897740500840320390626889 5923305375630240292970167)
          ·
            refine ⟨8884958063445360439455251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923305375630240292970167 8884958063445360439455251)
            ·
              refine ⟨13327437095168040659182877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884958063445360439455251 13327437095168040659182877)
              ·
                refine ⟨4997788910688015247193579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13327437095168040659182877 4997788910688015247193579)
                ·
                  refine ⟨7496683366032022870790369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997788910688015247193579 7496683366032022870790369)
                  ·
                    refine ⟨5622512524524017153092777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496683366032022870790369 5622512524524017153092777)
                    ·
                      refine ⟨4216884393393012864819583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622512524524017153092777 4216884393393012864819583)
                      ·
                        rfl

theorem cell23_8212353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_8212353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212353 prefixEnd_8212353 := by exact prefixLift 8212353
  have htrace : WordTrace (prefixWord ++ tailWord_8212353) baseStart_8212353 baseEnd_8212353 := by
    simpa [prefixWord, tailWord_8212353, baseEnd_8212353] using wordTrace_append hprefix tailTrace_8212353
  have hstable : (prefixWord ++ tailWord_8212353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212353).length < 2 ^ (prefixWord ++ tailWord_8212353).sum := by decide
  have hdescent : baseEnd_8212353 < baseStart_8212353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212361 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_8212361 : Nat := 118140960795 + 8212361 * 2 ^ 59
def prefixEnd_8212361 : Nat := 4983230072969 + 3 ^ 40 * 8212361 * 2
def baseEnd_8212361 : Nat := 4216888501238248833519545

theorem tailTrace_8212361 : CollatzResearch.WordTrace tailWord_8212361 prefixEnd_8212361 4216888501238248833519545 := by
  unfold tailWord_8212361
  simp only [CollatzResearch.WordTrace]
  refine ⟨299529413001026131440436937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199686275334017420960291291 299529413001026131440436937)
  ·
    refine ⟨224647059750769598580327703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299529413001026131440436937 224647059750769598580327703)
    ·
      refine ⟨336970589626154397870491555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224647059750769598580327703 336970589626154397870491555)
      ·
        refine ⟨505455884439231596805737333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336970589626154397870491555 505455884439231596805737333)
        ·
          refine ⟨47386489166177962200537875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 505455884439231596805737333 47386489166177962200537875)
          ·
            refine ⟨71079733749266943300806813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47386489166177962200537875 71079733749266943300806813)
            ·
              refine ⟨26654900155975103737802555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71079733749266943300806813 26654900155975103737802555)
              ·
                refine ⟨39982350233962655606703833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26654900155975103737802555 39982350233962655606703833)
                ·
                  refine ⟨29986762675471991705027875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39982350233962655606703833 29986762675471991705027875)
                  ·
                    refine ⟨44980144013207987557541813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29986762675471991705027875 44980144013207987557541813)
                    ·
                      refine ⟨4216888501238248833519545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44980144013207987557541813 4216888501238248833519545)
                      ·
                        rfl

theorem cell23_8212361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_8212361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212361 prefixEnd_8212361 := by exact prefixLift 8212361
  have htrace : WordTrace (prefixWord ++ tailWord_8212361) baseStart_8212361 baseEnd_8212361 := by
    simpa [prefixWord, tailWord_8212361, baseEnd_8212361] using wordTrace_append hprefix tailTrace_8212361
  have hstable : (prefixWord ++ tailWord_8212361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212361).length < 2 ^ (prefixWord ++ tailWord_8212361).sum := by decide
  have hdescent : baseEnd_8212361 < baseStart_8212361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212375 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_8212375 : Nat := 118140960795 + 8212375 * 2 ^ 59
def prefixEnd_8212375 : Nat := 4983230072969 + 3 ^ 40 * 8212375 * 2
def baseEnd_8212375 : Nat := 4216895689967411778744481

theorem tailTrace_8212375 : CollatzResearch.WordTrace tailWord_8212375 prefixEnd_8212375 4216895689967411778744481 := by
  unfold tailWord_8212375
  simp only [CollatzResearch.WordTrace]
  refine ⟨299529923622975411831446579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199686615748650274554297719 299529923622975411831446579)
  ·
    refine ⟨449294885434463117747169869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299529923622975411831446579 449294885434463117747169869)
    ·
      refine ⟨168485582037923669155188701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449294885434463117747169869 168485582037923669155188701)
      ·
        refine ⟨63182093264221375933195763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168485582037923669155188701 63182093264221375933195763)
        ·
          refine ⟨94773139896332063899793645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63182093264221375933195763 94773139896332063899793645)
          ·
            refine ⟨35539927461124523962422617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94773139896332063899793645 35539927461124523962422617)
            ·
              refine ⟨26654945595843392971816963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35539927461124523962422617 26654945595843392971816963)
              ·
                refine ⟨39982418393765089457725445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26654945595843392971816963 39982418393765089457725445)
                ·
                  refine ⟨7496703448830954273323521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39982418393765089457725445 7496703448830954273323521)
                  ·
                    refine ⟨5622527586623215704992641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7496703448830954273323521 5622527586623215704992641)
                    ·
                      refine ⟨4216895689967411778744481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622527586623215704992641 4216895689967411778744481)
                      ·
                        rfl

theorem cell23_8212375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_8212375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212375 prefixEnd_8212375 := by exact prefixLift 8212375
  have htrace : WordTrace (prefixWord ++ tailWord_8212375) baseStart_8212375 baseEnd_8212375 := by
    simpa [prefixWord, tailWord_8212375, baseEnd_8212375] using wordTrace_append hprefix tailTrace_8212375
  have hstable : (prefixWord ++ tailWord_8212375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212375).length < 2 ^ (prefixWord ++ tailWord_8212375).sum := by decide
  have hdescent : baseEnd_8212375 < baseStart_8212375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212386 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_8212386 : Nat := 118140960795 + 8212386 * 2 ^ 59
def prefixEnd_8212386 : Nat := 4983230072969 + 3 ^ 40 * 8212386 * 2
def baseEnd_8212386 : Nat := 4216901338254611235706931

theorem tailTrace_8212386 : CollatzResearch.WordTrace tailWord_8212386 prefixEnd_8212386 4216901338254611235706931 := by
  unfold tailWord_8212386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882581206483890177524253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199686883217290373806731341 74882581206483890177524253)
  ·
    refine ⟨28080967952431458816571595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74882581206483890177524253 28080967952431458816571595)
    ·
      refine ⟨42121451928647188224857393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28080967952431458816571595 42121451928647188224857393)
      ·
        refine ⟨31591088946485391168643045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42121451928647188224857393 31591088946485391168643045)
        ·
          refine ⟨5923329177466010844120571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31591088946485391168643045 5923329177466010844120571)
          ·
            refine ⟨8884993766199016266180857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923329177466010844120571 8884993766199016266180857)
            ·
              refine ⟨6663745324649262199635643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884993766199016266180857 6663745324649262199635643)
              ·
                refine ⟨9995617986973893299453465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663745324649262199635643 9995617986973893299453465)
                ·
                  refine ⟨7496713490230419974590099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995617986973893299453465 7496713490230419974590099)
                  ·
                    refine ⟨11245070235345629961885149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496713490230419974590099 11245070235345629961885149)
                    ·
                      refine ⟨4216901338254611235706931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245070235345629961885149 4216901338254611235706931)
                      ·
                        rfl

theorem cell23_8212386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_8212386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212386 prefixEnd_8212386 := by exact prefixLift 8212386
  have htrace : WordTrace (prefixWord ++ tailWord_8212386) baseStart_8212386 baseEnd_8212386 := by
    simpa [prefixWord, tailWord_8212386, baseEnd_8212386] using wordTrace_append hprefix tailTrace_8212386
  have hstable : (prefixWord ++ tailWord_8212386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212386).length < 2 ^ (prefixWord ++ tailWord_8212386).sum := by decide
  have hdescent : baseEnd_8212386 < baseStart_8212386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212411 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 2, 5]
def baseStart_8212411 : Nat := 118140960795 + 8212411 * 2 ^ 59
def prefixEnd_8212411 : Nat := 4983230072969 + 3 ^ 40 * 8212411 * 2
def baseEnd_8212411 : Nat := 1405638058423657879298105

theorem tailTrace_8212411 : CollatzResearch.WordTrace tailWord_8212411 prefixEnd_8212411 1405638058423657879298105 := by
  unfold tailWord_8212411
  simp only [CollatzResearch.WordTrace]
  refine ⟨299531236650844989979757087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199687491100563326653171391 299531236650844989979757087)
  ·
    refine ⟨449296854976267484969635631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299531236650844989979757087 449296854976267484969635631)
    ·
      refine ⟨673945282464401227454453447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449296854976267484969635631 673945282464401227454453447)
      ·
        refine ⟨1010917923696601841181680171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673945282464401227454453447 1010917923696601841181680171)
        ·
          refine ⟨1516376885544902761772520257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010917923696601841181680171 1516376885544902761772520257)
          ·
            refine ⟨1137282664158677071329390193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516376885544902761772520257 1137282664158677071329390193)
            ·
              refine ⟨852961998119007803497042645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137282664158677071329390193 852961998119007803497042645)
              ·
                refine ⟨19991296830914245394461937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 852961998119007803497042645 19991296830914245394461937)
                ·
                  refine ⟨14993472623185684045846453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19991296830914245394461937 14993472623185684045846453)
                  ·
                    refine ⟨1405638058423657879298105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14993472623185684045846453 1405638058423657879298105)
                    ·
                      rfl

theorem cell23_8212411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].length) (baseStart_8212411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212411 prefixEnd_8212411 := by exact prefixLift 8212411
  have htrace : WordTrace (prefixWord ++ tailWord_8212411) baseStart_8212411 baseEnd_8212411 := by
    simpa [prefixWord, tailWord_8212411, baseEnd_8212411] using wordTrace_append hprefix tailTrace_8212411
  have hstable : (prefixWord ++ tailWord_8212411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212411).length < 2 ^ (prefixWord ++ tailWord_8212411).sum := by decide
  have hdescent : baseEnd_8212411 < baseStart_8212411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212428 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_8212428 : Nat := 118140960795 + 8212428 * 2 ^ 59
def prefixEnd_8212428 : Nat := 4983230072969 + 3 ^ 40 * 8212428 * 2
def baseEnd_8212428 : Nat := 1405640968147366690460579

theorem tailTrace_8212428 : CollatzResearch.WordTrace tailWord_8212428 prefixEnd_8212428 1405640968147366690460579 := by
  unfold tailWord_8212428
  simp only [CollatzResearch.WordTrace]
  refine ⟨149765928345891700941562969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199687904461188934588750625 149765928345891700941562969)
  ·
    refine ⟨112324446259418775706172227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149765928345891700941562969 112324446259418775706172227)
    ·
      refine ⟨168486669389128163559258341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112324446259418775706172227 168486669389128163559258341)
      ·
        refine ⟨31591250510461530667360939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168486669389128163559258341 31591250510461530667360939)
        ·
          refine ⟨47386875765692296001041409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31591250510461530667360939 47386875765692296001041409)
          ·
            refine ⟨35540156824269222000781057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47386875765692296001041409 35540156824269222000781057)
            ·
              refine ⟨26655117618201916500585793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35540156824269222000781057 26655117618201916500585793)
              ·
                refine ⟨19991338213651437375439345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26655117618201916500585793 19991338213651437375439345)
                ·
                  refine ⟨14993503660238578031579509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19991338213651437375439345 14993503660238578031579509)
                  ·
                    refine ⟨1405640968147366690460579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14993503660238578031579509 1405640968147366690460579)
                    ·
                      rfl

theorem cell23_8212428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_8212428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212428 prefixEnd_8212428 := by exact prefixLift 8212428
  have htrace : WordTrace (prefixWord ++ tailWord_8212428) baseStart_8212428 baseEnd_8212428 := by
    simpa [prefixWord, tailWord_8212428, baseEnd_8212428] using wordTrace_append hprefix tailTrace_8212428
  have hstable : (prefixWord ++ tailWord_8212428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212428).length < 2 ^ (prefixWord ++ tailWord_8212428).sum := by decide
  have hdescent : baseEnd_8212428 < baseStart_8212428 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212475 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 1, 4]
def baseStart_8212475 : Nat := 118140960795 + 8212475 * 2 ^ 59
def prefixEnd_8212475 : Nat := 4983230072969 + 3 ^ 40 * 8212475 * 2
def baseEnd_8212475 : Nat := 1405649012677620462498007

theorem tailTrace_8212475 : CollatzResearch.WordTrace tailWord_8212475 prefixEnd_8212475 1405649012677620462498007 := by
  unfold tailWord_8212475
  simp only [CollatzResearch.WordTrace]
  refine ⟨299533570922613128910086879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199689047281742085940057919 299533570922613128910086879)
  ·
    refine ⟨449300356383919693365130319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299533570922613128910086879 449300356383919693365130319)
    ·
      refine ⟨673950534575879540047695479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449300356383919693365130319 673950534575879540047695479)
      ·
        refine ⟨1010925801863819310071543219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673950534575879540047695479 1010925801863819310071543219)
        ·
          refine ⟨1516388702795728965107314829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010925801863819310071543219 1516388702795728965107314829)
          ·
            refine ⟨568645763548398361915243061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516388702795728965107314829 568645763548398361915243061)
            ·
              refine ⟨53310540332662346429554037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 568645763548398361915243061 53310540332662346429554037)
              ·
                refine ⟨4997863156187094977770691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53310540332662346429554037 4997863156187094977770691)
                ·
                  refine ⟨7496794734280642466656037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997863156187094977770691 7496794734280642466656037)
                  ·
                    refine ⟨1405649012677620462498007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496794734280642466656037 1405649012677620462498007)
                    ·
                      rfl

theorem cell23_8212475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 1, 4].length) (baseStart_8212475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212475 prefixEnd_8212475 := by exact prefixLift 8212475
  have htrace : WordTrace (prefixWord ++ tailWord_8212475) baseStart_8212475 baseEnd_8212475 := by
    simpa [prefixWord, tailWord_8212475, baseEnd_8212475] using wordTrace_append hprefix tailTrace_8212475
  have hstable : (prefixWord ++ tailWord_8212475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212475).length < 2 ^ (prefixWord ++ tailWord_8212475).sum := by decide
  have hdescent : baseEnd_8212475 < baseStart_8212475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212491 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_8212491 : Nat := 118140960795 + 8212491 * 2 ^ 59
def prefixEnd_8212491 : Nat := 4983230072969 + 3 ^ 40 * 8212491 * 2
def baseEnd_8212491 : Nat := 4216955253723333324893947

theorem tailTrace_8212491 : CollatzResearch.WordTrace tailWord_8212491 prefixEnd_8212491 4216955253723333324893947 := by
  unfold tailWord_8212491
  simp only [CollatzResearch.WordTrace]
  refine ⟨299534154490555163642669327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199689436327036775761779551 299534154490555163642669327)
  ·
    refine ⟨449301231735832745464003991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299534154490555163642669327 449301231735832745464003991)
    ·
      refine ⟨673951847603749118196005987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449301231735832745464003991 673951847603749118196005987)
      ·
        refine ⟨1010927771405623677294008981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673951847603749118196005987 1010927771405623677294008981)
        ·
          refine ⟨47387239284638609873156671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1010927771405623677294008981 47387239284638609873156671)
          ·
            refine ⟨71080858926957914809735007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47387239284638609873156671 71080858926957914809735007)
            ·
              refine ⟨106621288390436872214602511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71080858926957914809735007 106621288390436872214602511)
              ·
                refine ⟨159931932585655308321903767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106621288390436872214602511 159931932585655308321903767)
                ·
                  refine ⟨239897898878482962482855651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159931932585655308321903767 239897898878482962482855651)
                  ·
                    refine ⟨359846848317724443724283477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239897898878482962482855651 359846848317724443724283477)
                    ·
                      refine ⟨4216955253723333324893947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 359846848317724443724283477 4216955253723333324893947)
                      ·
                        rfl

theorem cell23_8212491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_8212491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212491 prefixEnd_8212491 := by exact prefixLift 8212491
  have htrace : WordTrace (prefixWord ++ tailWord_8212491) baseStart_8212491 baseEnd_8212491 := by
    simpa [prefixWord, tailWord_8212491, baseEnd_8212491] using wordTrace_append hprefix tailTrace_8212491
  have hstable : (prefixWord ++ tailWord_8212491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212491).length < 2 ^ (prefixWord ++ tailWord_8212491).sum := by decide
  have hdescent : baseEnd_8212491 < baseStart_8212491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212515 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 3]
def baseStart_8212515 : Nat := 118140960795 + 8212515 * 2 ^ 59
def prefixEnd_8212515 : Nat := 4983230072969 + 3 ^ 40 * 8212515 * 2
def baseEnd_8212515 : Nat := 4216967577259041230993837

theorem tailTrace_8212515 : CollatzResearch.WordTrace tailWord_8212515 prefixEnd_8212515 4216967577259041230993837 := by
  unfold tailWord_8212515
  simp only [CollatzResearch.WordTrace]
  refine ⟨299535029842468215741542999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199690019894978810494361999 299535029842468215741542999)
  ·
    refine ⟨449302544763702323612314499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299535029842468215741542999 449302544763702323612314499)
    ·
      refine ⟨673953817145553485418471749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449302544763702323612314499 673953817145553485418471749)
      ·
        refine ⟨126366340714791278515963453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 673953817145553485418471749 126366340714791278515963453)
        ·
          refine ⟨47387377768046729443486295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126366340714791278515963453 47387377768046729443486295)
          ·
            refine ⟨71081066652070094165229443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47387377768046729443486295 71081066652070094165229443)
            ·
              refine ⟨106621599978105141247844165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71081066652070094165229443 106621599978105141247844165)
              ·
                refine ⟨19991549995894713983970781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106621599978105141247844165 19991549995894713983970781)
                ·
                  refine ⟨7496831248460517743989043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19991549995894713983970781 7496831248460517743989043)
                  ·
                    refine ⟨11245246872690776615983565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496831248460517743989043 11245246872690776615983565)
                    ·
                      refine ⟨4216967577259041230993837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245246872690776615983565 4216967577259041230993837)
                      ·
                        rfl

theorem cell23_8212515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_8212515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212515 prefixEnd_8212515 := by exact prefixLift 8212515
  have htrace : WordTrace (prefixWord ++ tailWord_8212515) baseStart_8212515 baseEnd_8212515 := by
    simpa [prefixWord, tailWord_8212515, baseEnd_8212515] using wordTrace_append hprefix tailTrace_8212515
  have hstable : (prefixWord ++ tailWord_8212515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212515).length < 2 ^ (prefixWord ++ tailWord_8212515).sum := by decide
  have hdescent : baseEnd_8212515 < baseStart_8212515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212538 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_8212538 : Nat := 118140960795 + 8212538 * 2 ^ 59
def prefixEnd_8212538 : Nat := 4983230072969 + 3 ^ 40 * 8212538 * 2
def baseEnd_8212538 : Nat := 4216979387314094641006231

theorem tailTrace_8212538 : CollatzResearch.WordTrace tailWord_8212538 prefixEnd_8212538 4216979387314094641006231 := by
  unfold tailWord_8212538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74883967180346222667407567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199690579147589927113086845 74883967180346222667407567)
  ·
    refine ⟨112325950770519334001111351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74883967180346222667407567 112325950770519334001111351)
    ·
      refine ⟨168488926155779001001667027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112325950770519334001111351 168488926155779001001667027)
      ·
        refine ⟨252733389233668501502500541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168488926155779001001667027 252733389233668501502500541)
        ·
          refine ⟨94775020962625688063437703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252733389233668501502500541 94775020962625688063437703)
          ·
            refine ⟨142162531443938532095156555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94775020962625688063437703 142162531443938532095156555)
            ·
              refine ⟨213243797165907798142734833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142162531443938532095156555 213243797165907798142734833)
              ·
                refine ⟨159932847874430848607051125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213243797165907798142734833 159932847874430848607051125)
                ·
                  refine ⟨14993704488227892056911043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159932847874430848607051125 14993704488227892056911043)
                  ·
                    refine ⟨22490556732341838085366565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14993704488227892056911043 22490556732341838085366565)
                    ·
                      refine ⟨4216979387314094641006231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22490556732341838085366565 4216979387314094641006231)
                      ·
                        rfl

theorem cell23_8212538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_8212538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212538 prefixEnd_8212538 := by exact prefixLift 8212538
  have htrace : WordTrace (prefixWord ++ tailWord_8212538) baseStart_8212538 baseEnd_8212538 := by
    simpa [prefixWord, tailWord_8212538, baseEnd_8212538] using wordTrace_append hprefix tailTrace_8212538
  have hstable : (prefixWord ++ tailWord_8212538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212538).length < 2 ^ (prefixWord ++ tailWord_8212538).sum := by decide
  have hdescent : baseEnd_8212538 < baseStart_8212538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212568 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_8212568 : Nat := 118140960795 + 8212568 * 2 ^ 59
def prefixEnd_8212568 : Nat := 4983230072969 + 3 ^ 40 * 8212568 * 2
def baseEnd_8212568 : Nat := 4216994791733729523631093

theorem tailTrace_8212568 : CollatzResearch.WordTrace tailWord_8212568 prefixEnd_8212568 4216994791733729523631093 := by
  unfold tailWord_8212568
  simp only [CollatzResearch.WordTrace]
  refine ⟨149768481455638102896611179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199691308607517470528814905 149768481455638102896611179)
  ·
    refine ⟨224652722183457154344916769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149768481455638102896611179 224652722183457154344916769)
    ·
      refine ⟨168489541637592865758687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224652722183457154344916769 168489541637592865758687577)
      ·
        refine ⟨126367156228194649319015683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168489541637592865758687577 126367156228194649319015683)
        ·
          refine ⟨189550734342291973978523525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126367156228194649319015683 189550734342291973978523525)
          ·
            refine ⟨35540762689179745120973161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189550734342291973978523525 35540762689179745120973161)
            ·
              refine ⟨26655572016884808840729871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35540762689179745120973161 26655572016884808840729871)
              ·
                refine ⟨39983358025327213261094807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26655572016884808840729871 39983358025327213261094807)
                ·
                  refine ⟨59975037037990819891642211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39983358025327213261094807 59975037037990819891642211)
                  ·
                    refine ⟨89962555556986229837463317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59975037037990819891642211 89962555556986229837463317)
                    ·
                      refine ⟨4216994791733729523631093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89962555556986229837463317 4216994791733729523631093)
                      ·
                        rfl

theorem cell23_8212568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_8212568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212568 prefixEnd_8212568 := by exact prefixLift 8212568
  have htrace : WordTrace (prefixWord ++ tailWord_8212568) baseStart_8212568 baseEnd_8212568 := by
    simpa [prefixWord, tailWord_8212568, baseEnd_8212568] using wordTrace_append hprefix tailTrace_8212568
  have hstable : (prefixWord ++ tailWord_8212568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212568).length < 2 ^ (prefixWord ++ tailWord_8212568).sum := by decide
  have hdescent : baseEnd_8212568 < baseStart_8212568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212572 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_8212572 : Nat := 118140960795 + 8212572 * 2 ^ 59
def prefixEnd_8212572 : Nat := 4983230072969 + 3 ^ 40 * 8212572 * 2
def baseEnd_8212572 : Nat := 4216996845656347507981075

theorem tailTrace_8212572 : CollatzResearch.WordTrace tailWord_8212572 prefixEnd_8212572 4216996845656347507981075 := by
  unfold tailWord_8212572
  simp only [CollatzResearch.WordTrace]
  refine ⟨149768554401630857238183985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199691405868841142984245313 149768554401630857238183985)
  ·
    refine ⟨112326415801223142928637989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149768554401630857238183985 112326415801223142928637989)
    ·
      refine ⟨21061202962729339299119623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112326415801223142928637989 21061202962729339299119623)
      ·
        refine ⟨31591804444094008948679435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21061202962729339299119623 31591804444094008948679435)
        ·
          refine ⟨47387706666141013423019153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31591804444094008948679435 47387706666141013423019153)
          ·
            refine ⟨35540779999605760067264365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47387706666141013423019153 35540779999605760067264365)
            ·
              refine ⟨13327792499852160025224137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35540779999605760067264365 13327792499852160025224137)
              ·
                refine ⟨9995844374889120018918103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13327792499852160025224137 9995844374889120018918103)
                ·
                  refine ⟨14993766562333680028377155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995844374889120018918103 14993766562333680028377155)
                  ·
                    refine ⟨22490649843500520042565733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14993766562333680028377155 22490649843500520042565733)
                    ·
                      refine ⟨4216996845656347507981075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22490649843500520042565733 4216996845656347507981075)
                      ·
                        rfl

theorem cell23_8212572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_8212572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212572 prefixEnd_8212572 := by exact prefixLift 8212572
  have htrace : WordTrace (prefixWord ++ tailWord_8212572) baseStart_8212572 baseEnd_8212572 := by
    simpa [prefixWord, tailWord_8212572, baseEnd_8212572] using wordTrace_append hprefix tailTrace_8212572
  have hstable : (prefixWord ++ tailWord_8212572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212572).length < 2 ^ (prefixWord ++ tailWord_8212572).sum := by decide
  have hdescent : baseEnd_8212572 < baseStart_8212572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212575 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_8212575 : Nat := 118140960795 + 8212575 * 2 ^ 59
def prefixEnd_8212575 : Nat := 4983230072969 + 3 ^ 40 * 8212575 * 2
def baseEnd_8212575 : Nat := 4216998386098310996243561

theorem tailTrace_8212575 : CollatzResearch.WordTrace tailWord_8212575 prefixEnd_8212575 4216998386098310996243561 := by
  unfold tailWord_8212575
  simp only [CollatzResearch.WordTrace]
  refine ⟨299537218222250845988727179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199691478814833897325818119 299537218222250845988727179)
  ·
    refine ⟨449305827333376268983090769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299537218222250845988727179 449305827333376268983090769)
    ·
      refine ⟨336979370500032201737318077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449305827333376268983090769 336979370500032201737318077)
      ·
        refine ⟨126367263937512075651494279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336979370500032201737318077 126367263937512075651494279)
        ·
          refine ⟨189550895906268113477241419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126367263937512075651494279 189550895906268113477241419)
          ·
            refine ⟨284326343859402170215862129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189550895906268113477241419 284326343859402170215862129)
            ·
              refine ⟨213244757894551627661896597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284326343859402170215862129 213244757894551627661896597)
              ·
                refine ⟨9995848026307107546651403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213244757894551627661896597 9995848026307107546651403)
                ·
                  refine ⟨14993772039460661319977105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9995848026307107546651403 14993772039460661319977105)
                  ·
                    refine ⟨11245329029595495989982829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14993772039460661319977105 11245329029595495989982829)
                    ·
                      refine ⟨4216998386098310996243561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245329029595495989982829 4216998386098310996243561)
                      ·
                        rfl

theorem cell23_8212575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_8212575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212575 prefixEnd_8212575 := by exact prefixLift 8212575
  have htrace : WordTrace (prefixWord ++ tailWord_8212575) baseStart_8212575 baseEnd_8212575 := by
    simpa [prefixWord, tailWord_8212575, baseEnd_8212575] using wordTrace_append hprefix tailTrace_8212575
  have hstable : (prefixWord ++ tailWord_8212575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212575).length < 2 ^ (prefixWord ++ tailWord_8212575).sum := by decide
  have hdescent : baseEnd_8212575 < baseStart_8212575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212673 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_8212673 : Nat := 118140960795 + 8212673 * 2 ^ 59
def prefixEnd_8212673 : Nat := 4983230072969 + 3 ^ 40 * 8212673 * 2
def baseEnd_8212673 : Nat := 4217048707202451612818111

theorem tailTrace_8212673 : CollatzResearch.WordTrace tailWord_8212673 prefixEnd_8212673 4217048707202451612818111 := by
  unfold tailWord_8212673
  simp only [CollatzResearch.WordTrace]
  refine ⟨299540792575895808725794673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199693861717263872483863115 299540792575895808725794673)
  ·
    refine ⟨224655594431921856544346005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299540792575895808725794673 224655594431921856544346005)
    ·
      refine ⟨10530730988996337025516219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224655594431921856544346005 10530730988996337025516219)
      ·
        refine ⟨15796096483494505538274329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530730988996337025516219 15796096483494505538274329)
        ·
          refine ⟨11847072362620879153705747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15796096483494505538274329 11847072362620879153705747)
          ·
            refine ⟨17770608543931318730558621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847072362620879153705747 17770608543931318730558621)
            ·
              refine ⟨6663978203974244523959483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17770608543931318730558621 6663978203974244523959483)
              ·
                refine ⟨9995967305961366785939225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663978203974244523959483 9995967305961366785939225)
                ·
                  refine ⟨7496975479471025089454419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995967305961366785939225 7496975479471025089454419)
                  ·
                    refine ⟨11245463219206537634181629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7496975479471025089454419 11245463219206537634181629)
                    ·
                      refine ⟨4217048707202451612818111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245463219206537634181629 4217048707202451612818111)
                      ·
                        rfl

theorem cell23_8212673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_8212673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212673 prefixEnd_8212673 := by exact prefixLift 8212673
  have htrace : WordTrace (prefixWord ++ tailWord_8212673) baseStart_8212673 baseEnd_8212673 := by
    simpa [prefixWord, tailWord_8212673, baseEnd_8212673] using wordTrace_append hprefix tailTrace_8212673
  have hstable : (prefixWord ++ tailWord_8212673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212673).length < 2 ^ (prefixWord ++ tailWord_8212673).sum := by decide
  have hdescent : baseEnd_8212673 < baseStart_8212673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212715 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 2, 5]
def baseStart_8212715 : Nat := 118140960795 + 8212715 * 2 ^ 59
def prefixEnd_8212715 : Nat := 4983230072969 + 3 ^ 40 * 8212715 * 2
def baseEnd_8212715 : Nat := 1405690091129980149497639

theorem tailTrace_8212715 : CollatzResearch.WordTrace tailWord_8212715 prefixEnd_8212715 1405690091129980149497639 := by
  unfold tailWord_8212715
  simp only [CollatzResearch.WordTrace]
  refine ⟨299542324441743649898823599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199694882961162433265882399 299542324441743649898823599)
  ·
    refine ⟨449313486662615474848235399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299542324441743649898823599 449313486662615474848235399)
    ·
      refine ⟨673970229993923212272353099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449313486662615474848235399 673970229993923212272353099)
      ·
        refine ⟨1010955344990884818408529649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673970229993923212272353099 1010955344990884818408529649)
        ·
          refine ⟨758216508743163613806397237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010955344990884818408529649 758216508743163613806397237)
          ·
            refine ⟨71082797694671588794349741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 758216508743163613806397237 71082797694671588794349741)
            ·
              refine ⟨26656049135501845797881153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71082797694671588794349741 26656049135501845797881153)
              ·
                refine ⟨19992036851626384348410865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26656049135501845797881153 19992036851626384348410865)
                ·
                  refine ⟨14994027638719788261308149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19992036851626384348410865 14994027638719788261308149)
                  ·
                    refine ⟨1405690091129980149497639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14994027638719788261308149 1405690091129980149497639)
                    ·
                      rfl

theorem cell23_8212715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].length) (baseStart_8212715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212715 prefixEnd_8212715 := by exact prefixLift 8212715
  have htrace : WordTrace (prefixWord ++ tailWord_8212715) baseStart_8212715 baseEnd_8212715 := by
    simpa [prefixWord, tailWord_8212715, baseEnd_8212715] using wordTrace_append hprefix tailTrace_8212715
  have hstable : (prefixWord ++ tailWord_8212715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212715).length < 2 ^ (prefixWord ++ tailWord_8212715).sum := by decide
  have hdescent : baseEnd_8212715 < baseStart_8212715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212719 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 5]
def baseStart_8212719 : Nat := 118140960795 + 8212719 * 2 ^ 59
def prefixEnd_8212719 : Nat := 4983230072969 + 3 ^ 40 * 8212719 * 2
def baseEnd_8212719 : Nat := 468563591923617603649211

theorem tailTrace_8212719 : CollatzResearch.WordTrace tailWord_8212719 prefixEnd_8212719 468563591923617603649211 := by
  unfold tailWord_8212719
  simp only [CollatzResearch.WordTrace]
  refine ⟨299542470333729158581969211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199694980222486105721312807 299542470333729158581969211)
  ·
    refine ⟨449313705500593737872953817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299542470333729158581969211 449313705500593737872953817)
    ·
      refine ⟨336985279125445303404715363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449313705500593737872953817 336985279125445303404715363)
      ·
        refine ⟨505477918688167955107073045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336985279125445303404715363 505477918688167955107073045)
        ·
          refine ⟨23694277438507872895644049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 505477918688167955107073045 23694277438507872895644049)
          ·
            refine ⟨17770708078880904671733037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23694277438507872895644049 17770708078880904671733037)
            ·
              refine ⟨6664015529580339251899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17770708078880904671733037 6664015529580339251899889)
              ·
                refine ⟨4998011647185254438924917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6664015529580339251899889 4998011647185254438924917)
                ·
                  refine ⟨468563591923617603649211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4998011647185254438924917 468563591923617603649211)
                  ·
                    rfl

theorem cell23_8212719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 5].length) (baseStart_8212719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212719 prefixEnd_8212719 := by exact prefixLift 8212719
  have htrace : WordTrace (prefixWord ++ tailWord_8212719) baseStart_8212719 baseEnd_8212719 := by
    simpa [prefixWord, tailWord_8212719, baseEnd_8212719] using wordTrace_append hprefix tailTrace_8212719
  have hstable : (prefixWord ++ tailWord_8212719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212719).length < 2 ^ (prefixWord ++ tailWord_8212719).sum := by decide
  have hdescent : baseEnd_8212719 < baseStart_8212719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212735 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_8212735 : Nat := 118140960795 + 8212735 * 2 ^ 59
def prefixEnd_8212735 : Nat := 4983230072969 + 3 ^ 40 * 8212735 * 2
def baseEnd_8212735 : Nat := 4217080543003030370242825

theorem tailTrace_8212735 : CollatzResearch.WordTrace tailWord_8212735 prefixEnd_8212735 4217080543003030370242825 := by
  unfold tailWord_8212735
  simp only [CollatzResearch.WordTrace]
  refine ⟨299543053901671193314551659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199695369267780795543034439 299543053901671193314551659)
  ·
    refine ⟨449314580852506789971827489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299543053901671193314551659 449314580852506789971827489)
    ·
      refine ⟨336985935639380092478870617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449314580852506789971827489 336985935639380092478870617)
      ·
        refine ⟨252739451729535069359152963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336985935639380092478870617 252739451729535069359152963)
        ·
          refine ⟨379109177594302604038729445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252739451729535069359152963 379109177594302604038729445)
          ·
            refine ⟨71082970798931738257261771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379109177594302604038729445 71082970798931738257261771)
            ·
              refine ⟨106624456198397607385892657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71082970798931738257261771 106624456198397607385892657)
              ·
                refine ⟨79968342148798205539419493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106624456198397607385892657 79968342148798205539419493)
                ·
                  refine ⟨14994064152899663538641155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79968342148798205539419493 14994064152899663538641155)
                  ·
                    refine ⟨22491096229349495307961733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14994064152899663538641155 22491096229349495307961733)
                    ·
                      refine ⟨4217080543003030370242825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22491096229349495307961733 4217080543003030370242825)
                      ·
                        rfl

theorem cell23_8212735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_8212735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212735 prefixEnd_8212735 := by exact prefixLift 8212735
  have htrace : WordTrace (prefixWord ++ tailWord_8212735) baseStart_8212735 baseEnd_8212735 := by
    simpa [prefixWord, tailWord_8212735, baseEnd_8212735] using wordTrace_append hprefix tailTrace_8212735
  have hstable : (prefixWord ++ tailWord_8212735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212735).length < 2 ^ (prefixWord ++ tailWord_8212735).sum := by decide
  have hdescent : baseEnd_8212735 < baseStart_8212735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212755 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3]
def baseStart_8212755 : Nat := 118140960795 + 8212755 * 2 ^ 59
def prefixEnd_8212755 : Nat := 4983230072969 + 3 ^ 40 * 8212755 * 2
def baseEnd_8212755 : Nat := 4217090812616120291992733

theorem tailTrace_8212755 : CollatzResearch.WordTrace tailWord_8212755 prefixEnd_8212755 4217090812616120291992733 := by
  unfold tailWord_8212755
  simp only [CollatzResearch.WordTrace]
  refine ⟨299543783361598736730279719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199695855574399157820186479 299543783361598736730279719)
  ·
    refine ⟨449315675042398105095419579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299543783361598736730279719 449315675042398105095419579)
    ·
      refine ⟨673973512563597157643129369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449315675042398105095419579 673973512563597157643129369)
      ·
        refine ⟨505480134422697868232347027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673973512563597157643129369 505480134422697868232347027)
        ·
          refine ⟨758220201634046802348520541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505480134422697868232347027 758220201634046802348520541)
          ·
            refine ⟨284332575612767550880695203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758220201634046802348520541 284332575612767550880695203)
            ·
              refine ⟨426498863419151326321042805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284332575612767550880695203 426498863419151326321042805)
              ·
                refine ⟨39984268445545436842597763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426498863419151326321042805 39984268445545436842597763)
                ·
                  refine ⟨59976402668318155263896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39984268445545436842597763 59976402668318155263896645)
                  ·
                    refine ⟨11245575500309654111980621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59976402668318155263896645 11245575500309654111980621)
                    ·
                      refine ⟨4217090812616120291992733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245575500309654111980621 4217090812616120291992733)
                      ·
                        rfl

theorem cell23_8212755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_8212755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212755 prefixEnd_8212755 := by exact prefixLift 8212755
  have htrace : WordTrace (prefixWord ++ tailWord_8212755) baseStart_8212755 baseEnd_8212755 := by
    simpa [prefixWord, tailWord_8212755, baseEnd_8212755] using wordTrace_append hprefix tailTrace_8212755
  have hstable : (prefixWord ++ tailWord_8212755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212755).length < 2 ^ (prefixWord ++ tailWord_8212755).sum := by decide
  have hdescent : baseEnd_8212755 < baseStart_8212755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212836 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_8212836 : Nat := 118140960795 + 8212836 * 2 ^ 59
def prefixEnd_8212836 : Nat := 4983230072969 + 3 ^ 40 * 8212836 * 2
def baseEnd_8212836 : Nat := 4217132404549134475079861

theorem tailTrace_8212836 : CollatzResearch.WordTrace tailWord_8212836 prefixEnd_8212836 4217132404549134475079861 := by
  unfold tailWord_8212836
  simp only [CollatzResearch.WordTrace]
  refine ⟨149773368837152643781989181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199697825116203525042652241 149773368837152643781989181)
  ·
    refine ⟨56165013313932241418245943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149773368837152643781989181 56165013313932241418245943)
    ·
      refine ⟨84247519970898362127368915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56165013313932241418245943 84247519970898362127368915)
      ·
        refine ⟨126371279956347543191053373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84247519970898362127368915 126371279956347543191053373)
        ·
          refine ⟨47389229983630328696645015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126371279956347543191053373 47389229983630328696645015)
          ·
            refine ⟨71083844975445493044967523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47389229983630328696645015 71083844975445493044967523)
            ·
              refine ⟨106625767463168239567451285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71083844975445493044967523 106625767463168239567451285)
              ·
                refine ⟨4998082849836011229724279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106625767463168239567451285 4998082849836011229724279)
                ·
                  refine ⟨7497124274754016844586419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998082849836011229724279 7497124274754016844586419)
                  ·
                    refine ⟨11245686412131025266879629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497124274754016844586419 11245686412131025266879629)
                    ·
                      refine ⟨4217132404549134475079861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11245686412131025266879629 4217132404549134475079861)
                      ·
                        rfl

theorem cell23_8212836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_8212836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212836 prefixEnd_8212836 := by exact prefixLift 8212836
  have htrace : WordTrace (prefixWord ++ tailWord_8212836) baseStart_8212836 baseEnd_8212836 := by
    simpa [prefixWord, tailWord_8212836, baseEnd_8212836] using wordTrace_append hprefix tailTrace_8212836
  have hstable : (prefixWord ++ tailWord_8212836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212836).length < 2 ^ (prefixWord ++ tailWord_8212836).sum := by decide
  have hdescent : baseEnd_8212836 < baseStart_8212836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212859 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 4]
def baseStart_8212859 : Nat := 118140960795 + 8212859 * 2 ^ 59
def prefixEnd_8212859 : Nat := 4983230072969 + 3 ^ 40 * 8212859 * 2
def baseEnd_8212859 : Nat := 4217144214604187885092255

theorem tailTrace_8212859 : CollatzResearch.WordTrace tailWord_8212859 prefixEnd_8212859 4217144214604187885092255 := by
  unfold tailWord_8212859
  simp only [CollatzResearch.WordTrace]
  refine ⟨299547576553221962492065631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199698384368814641661377087 299547576553221962492065631)
  ·
    refine ⟨449321364829832943738098447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299547576553221962492065631 449321364829832943738098447)
    ·
      refine ⟨673982047244749415607147671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449321364829832943738098447 673982047244749415607147671)
      ·
        refine ⟨1010973070867124123410721507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673982047244749415607147671 1010973070867124123410721507)
        ·
          refine ⟨1516459606300686185116082261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010973070867124123410721507 1516459606300686185116082261)
          ·
            refine ⟨17771011011336166231829089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1516459606300686185116082261 17771011011336166231829089)
            ·
              refine ⟨13328258258502124673871817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771011011336166231829089 13328258258502124673871817)
              ·
                refine ⟨9996193693876593505403863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13328258258502124673871817 9996193693876593505403863)
                ·
                  refine ⟨14994290540814890258105795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9996193693876593505403863 14994290540814890258105795)
                  ·
                    refine ⟨22491435811222335387158693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14994290540814890258105795 22491435811222335387158693)
                    ·
                      refine ⟨4217144214604187885092255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22491435811222335387158693 4217144214604187885092255)
                      ·
                        rfl

theorem cell23_8212859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 4].length) (baseStart_8212859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212859 prefixEnd_8212859 := by exact prefixLift 8212859
  have htrace : WordTrace (prefixWord ++ tailWord_8212859) baseStart_8212859 baseEnd_8212859 := by
    simpa [prefixWord, tailWord_8212859, baseEnd_8212859] using wordTrace_append hprefix tailTrace_8212859
  have hstable : (prefixWord ++ tailWord_8212859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212859).length < 2 ^ (prefixWord ++ tailWord_8212859).sum := by decide
  have hdescent : baseEnd_8212859 < baseStart_8212859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212872 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_8212872 : Nat := 118140960795 + 8212872 * 2 ^ 59
def prefixEnd_8212872 : Nat := 4983230072969 + 3 ^ 40 * 8212872 * 2
def baseEnd_8212872 : Nat := 4217150889852696334229695

theorem tailTrace_8212872 : CollatzResearch.WordTrace tailWord_8212872 prefixEnd_8212872 4217150889852696334229695 := by
  unfold tailWord_8212872
  simp only [CollatzResearch.WordTrace]
  refine ⟨149774025351087432856144435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199698700468116577141525913 149774025351087432856144435)
  ·
    refine ⟨224661038026631149284216653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149774025351087432856144435 224661038026631149284216653)
    ·
      refine ⟨84247889259986680981581245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224661038026631149284216653 84247889259986680981581245)
      ·
        refine ⟨31592958472495005368092967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84247889259986680981581245 31592958472495005368092967)
        ·
          refine ⟨47389437708742508052139451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31592958472495005368092967 47389437708742508052139451)
          ·
            refine ⟨71084156563113762078209177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47389437708742508052139451 71084156563113762078209177)
            ·
              refine ⟨53313117422335321558656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71084156563113762078209177 53313117422335321558656883)
              ·
                refine ⟨79969676133502982337985325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53313117422335321558656883 79969676133502982337985325)
                ·
                  refine ⟨29988628550063618376744497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79969676133502982337985325 29988628550063618376744497)
                  ·
                    refine ⟨22491471412547713782558373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29988628550063618376744497 22491471412547713782558373)
                    ·
                      refine ⟨4217150889852696334229695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22491471412547713782558373 4217150889852696334229695)
                      ·
                        rfl

theorem cell23_8212872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_8212872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212872 prefixEnd_8212872 := by exact prefixLift 8212872
  have htrace : WordTrace (prefixWord ++ tailWord_8212872) baseStart_8212872 baseEnd_8212872 := by
    simpa [prefixWord, tailWord_8212872, baseEnd_8212872] using wordTrace_append hprefix tailTrace_8212872
  have hstable : (prefixWord ++ tailWord_8212872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212872).length < 2 ^ (prefixWord ++ tailWord_8212872).sum := by decide
  have hdescent : baseEnd_8212872 < baseStart_8212872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212903 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 2, 4]
def baseStart_8212903 : Nat := 118140960795 + 8212903 * 2 ^ 59
def prefixEnd_8212903 : Nat := 4983230072969 + 3 ^ 40 * 8212903 * 2
def baseEnd_8212903 : Nat := 1405722269250995237647351

theorem tailTrace_8212903 : CollatzResearch.WordTrace tailWord_8212903 prefixEnd_8212903 1405722269250995237647351 := by
  unfold tailWord_8212903
  simp only [CollatzResearch.WordTrace]
  refine ⟨299549181365062558006667363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199699454243375038671111575 299549181365062558006667363)
  ·
    refine ⟨449323772047593837010001045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299549181365062558006667363 449323772047593837010001045)
    ·
      refine ⟨21062051814730961109843799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 449323772047593837010001045 21062051814730961109843799)
      ·
        refine ⟨31593077722096441664765699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062051814730961109843799 31593077722096441664765699)
        ·
          refine ⟨47389616583144662497148549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31593077722096441664765699 47389616583144662497148549)
          ·
            refine ⟨8885553109339624218215353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47389616583144662497148549 8885553109339624218215353)
            ·
              refine ⟨6664164832004718163661515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885553109339624218215353 6664164832004718163661515)
              ·
                refine ⟨9996247248007077245492273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664164832004718163661515 9996247248007077245492273)
                ·
                  refine ⟨7497185436005307934119205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9996247248007077245492273 7497185436005307934119205)
                  ·
                    refine ⟨1405722269250995237647351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497185436005307934119205 1405722269250995237647351)
                    ·
                      rfl

theorem cell23_8212903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_8212903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212903 prefixEnd_8212903 := by exact prefixLift 8212903
  have htrace : WordTrace (prefixWord ++ tailWord_8212903) baseStart_8212903 baseEnd_8212903 := by
    simpa [prefixWord, tailWord_8212903, baseEnd_8212903] using wordTrace_append hprefix tailTrace_8212903
  have hstable : (prefixWord ++ tailWord_8212903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212903).length < 2 ^ (prefixWord ++ tailWord_8212903).sum := by decide
  have hdescent : baseEnd_8212903 < baseStart_8212903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_8212915 : Nat := 118140960795 + 8212915 * 2 ^ 59
def prefixEnd_8212915 : Nat := 4983230072969 + 3 ^ 40 * 8212915 * 2
def baseEnd_8212915 : Nat := 4217172969520839665991997

theorem tailTrace_8212915 : CollatzResearch.WordTrace tailWord_8212915 prefixEnd_8212915 4217172969520839665991997 := by
  unfold tailWord_8212915
  simp only [CollatzResearch.WordTrace]
  refine ⟨299549619041019084056104199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199699746027346056037402799 299549619041019084056104199)
  ·
    refine ⟨449324428561528626084156299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299549619041019084056104199 449324428561528626084156299)
    ·
      refine ⟨673986642842292939126234449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449324428561528626084156299 673986642842292939126234449)
      ·
        refine ⟨505489982131719704344675837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673986642842292939126234449 505489982131719704344675837)
        ·
          refine ⟨189558743299394889129253439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505489982131719704344675837 189558743299394889129253439)
          ·
            refine ⟨284338114949092333693880159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189558743299394889129253439 284338114949092333693880159)
            ·
              refine ⟨426507172423638500540820239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284338114949092333693880159 426507172423638500540820239)
              ·
                refine ⟨639760758635457750811230359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426507172423638500540820239 639760758635457750811230359)
                ·
                  refine ⟨959641137953186626216845539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639760758635457750811230359 959641137953186626216845539)
                  ·
                    refine ⟨1439461706929779939325268309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959641137953186626216845539 1439461706929779939325268309)
                    ·
                      refine ⟨4217172969520839665991997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1439461706929779939325268309 4217172969520839665991997)
                      ·
                        rfl

theorem cell23_8212915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_8212915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212915 prefixEnd_8212915 := by exact prefixLift 8212915
  have htrace : WordTrace (prefixWord ++ tailWord_8212915) baseStart_8212915 baseEnd_8212915 := by
    simpa [prefixWord, tailWord_8212915, baseEnd_8212915] using wordTrace_append hprefix tailTrace_8212915
  have hstable : (prefixWord ++ tailWord_8212915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212915).length < 2 ^ (prefixWord ++ tailWord_8212915).sum := by decide
  have hdescent : baseEnd_8212915 < baseStart_8212915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212942 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_8212942 : Nat := 118140960795 + 8212942 * 2 ^ 59
def prefixEnd_8212942 : Nat := 4983230072969 + 3 ^ 40 * 8212942 * 2
def baseEnd_8212942 : Nat := 1405728944499503686784791

theorem tailTrace_8212942 : CollatzResearch.WordTrace tailWord_8212942 prefixEnd_8212942 1405728944499503686784791 := by
  unfold tailWord_8212942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37443825476490158458417135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199700402541280845111558053 37443825476490158458417135)
  ·
    refine ⟨56165738214735237687625703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37443825476490158458417135 56165738214735237687625703)
    ·
      refine ⟨84248607322102856531438555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56165738214735237687625703 84248607322102856531438555)
      ·
        refine ⟨126372910983154284797157833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84248607322102856531438555 126372910983154284797157833)
        ·
          refine ⟨94779683237365713597868375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126372910983154284797157833 94779683237365713597868375)
          ·
            refine ⟨142169524856048570396802563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94779683237365713597868375 142169524856048570396802563)
            ·
              refine ⟨213254287284072855595203845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142169524856048570396802563 213254287284072855595203845)
              ·
                refine ⟨39985178865763660424100721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213254287284072855595203845 39985178865763660424100721)
                ·
                  refine ⟨29988884149322745318075541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39985178865763660424100721 29988884149322745318075541)
                  ·
                    refine ⟨1405728944499503686784791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29988884149322745318075541 1405728944499503686784791)
                    ·
                      rfl

theorem cell23_8212942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_8212942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212942 prefixEnd_8212942 := by exact prefixLift 8212942
  have htrace : WordTrace (prefixWord ++ tailWord_8212942) baseStart_8212942 baseEnd_8212942 := by
    simpa [prefixWord, tailWord_8212942, baseEnd_8212942] using wordTrace_append hprefix tailTrace_8212942
  have hstable : (prefixWord ++ tailWord_8212942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212942).length < 2 ^ (prefixWord ++ tailWord_8212942).sum := by decide
  have hdescent : baseEnd_8212942 < baseStart_8212942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212972 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 7]
def baseStart_8212972 : Nat := 118140960795 + 8212972 * 2 ^ 59
def prefixEnd_8212972 : Nat := 4983230072969 + 3 ^ 40 * 8212972 * 2
def baseEnd_8212972 : Nat := 468578026435349549219915

theorem tailTrace_8212972 : CollatzResearch.WordTrace tailWord_8212972 prefixEnd_8212972 468578026435349549219915 := by
  unfold tailWord_8212972
  simp only [CollatzResearch.WordTrace]
  refine ⟨149775849000906291395464585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199701132001208388527286113 149775849000906291395464585)
  ·
    refine ⟨112331886750679718546598439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149775849000906291395464585 112331886750679718546598439)
    ·
      refine ⟨168497830126019577819897659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112331886750679718546598439 168497830126019577819897659)
      ·
        refine ⟨252746745189029366729846489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168497830126019577819897659 252746745189029366729846489)
        ·
          refine ⟨189560058891772025047384867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252746745189029366729846489 189560058891772025047384867)
          ·
            refine ⟨284340088337658037571077301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189560058891772025047384867 284340088337658037571077301)
            ·
              refine ⟨26656883281655441022288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284340088337658037571077301 26656883281655441022288497)
              ·
                refine ⟨19992662461241580766716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26656883281655441022288497 19992662461241580766716373)
                ·
                  refine ⟨468578026435349549219915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19992662461241580766716373 468578026435349549219915)
                  ·
                    rfl

theorem cell23_8212972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_8212972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8212972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8212972 prefixEnd_8212972 := by exact prefixLift 8212972
  have htrace : WordTrace (prefixWord ++ tailWord_8212972) baseStart_8212972 baseEnd_8212972 := by
    simpa [prefixWord, tailWord_8212972, baseEnd_8212972] using wordTrace_append hprefix tailTrace_8212972
  have hstable : (prefixWord ++ tailWord_8212972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212972).length < 2 ^ (prefixWord ++ tailWord_8212972).sum := by decide
  have hdescent : baseEnd_8212972 < baseStart_8212972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213006 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_8213006 : Nat := 118140960795 + 8213006 * 2 ^ 59
def prefixEnd_8213006 : Nat := 4983230072969 + 3 ^ 40 * 8213006 * 2
def baseEnd_8213006 : Nat := 468579966251155423328231

theorem tailTrace_8213006 : CollatzResearch.WordTrace tailWord_8213006 prefixEnd_8213006 468579966251155423328231 := by
  unfold tailWord_8213006
  simp only [CollatzResearch.WordTrace]
  refine ⟨37444117260461175824708359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199701958722459604398444581 37444117260461175824708359)
  ·
    refine ⟨56166175890691763737062539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37444117260461175824708359 56166175890691763737062539)
    ·
      refine ⟨84249263836037645605593809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56166175890691763737062539 84249263836037645605593809)
      ·
        refine ⟨63186947877028234204195357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84249263836037645605593809 63186947877028234204195357)
        ·
          refine ⟨23695105453885587826573259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63186947877028234204195357 23695105453885587826573259)
          ·
            refine ⟨35542658180828381739859889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23695105453885587826573259 35542658180828381739859889)
            ·
              refine ⟨26656993635621286304894917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35542658180828381739859889 26656993635621286304894917)
              ·
                refine ⟨4998186306678991182167797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26656993635621286304894917 4998186306678991182167797)
                ·
                  refine ⟨468579966251155423328231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4998186306678991182167797 468579966251155423328231)
                  ·
                    rfl

theorem cell23_8213006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_8213006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213006 prefixEnd_8213006 := by exact prefixLift 8213006
  have htrace : WordTrace (prefixWord ++ tailWord_8213006) baseStart_8213006 baseEnd_8213006 := by
    simpa [prefixWord, tailWord_8213006, baseEnd_8213006] using wordTrace_append hprefix tailTrace_8213006
  have hstable : (prefixWord ++ tailWord_8213006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213006).length < 2 ^ (prefixWord ++ tailWord_8213006).sum := by decide
  have hdescent : baseEnd_8213006 < baseStart_8213006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213009 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_8213009 : Nat := 118140960795 + 8213009 * 2 ^ 59
def prefixEnd_8213009 : Nat := 4983230072969 + 3 ^ 40 * 8213009 * 2
def baseEnd_8213009 : Nat := 4217221236702362298216565

theorem tailTrace_8213009 : CollatzResearch.WordTrace tailWord_8213009 prefixEnd_8213009 4217221236702362298216565 := by
  unfold tailWord_8213009
  simp only [CollatzResearch.WordTrace]
  refine ⟨299553047502678538110026081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199702031668452358740017387 299553047502678538110026081)
  ·
    refine ⟨224664785627008903582519561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299553047502678538110026081 224664785627008903582519561)
    ·
      refine ⟨168498589220256677686889671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224664785627008903582519561 168498589220256677686889671)
      ·
        refine ⟨252747883830385016530334507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168498589220256677686889671 252747883830385016530334507)
        ·
          refine ⟨379121825745577524795501761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252747883830385016530334507 379121825745577524795501761)
          ·
            refine ⟨284341369309183143596626321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379121825745577524795501761 284341369309183143596626321)
            ·
              refine ⟨213256026981887357697469741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284341369309183143596626321 213256026981887357697469741)
              ·
                refine ⟨79971010118207759136551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213256026981887357697469741 79971010118207759136551153)
                ·
                  refine ⟨59978257588655819352413365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79971010118207759136551153 59978257588655819352413365)
                  ·
                    refine ⟨5622961648936483064288753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59978257588655819352413365 5622961648936483064288753)
                    ·
                      refine ⟨4217221236702362298216565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5622961648936483064288753 4217221236702362298216565)
                      ·
                        rfl

theorem cell23_8213009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_8213009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213009 prefixEnd_8213009 := by exact prefixLift 8213009
  have htrace : WordTrace (prefixWord ++ tailWord_8213009) baseStart_8213009 baseEnd_8213009 := by
    simpa [prefixWord, tailWord_8213009, baseEnd_8213009] using wordTrace_append hprefix tailTrace_8213009
  have hstable : (prefixWord ++ tailWord_8213009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213009).length < 2 ^ (prefixWord ++ tailWord_8213009).sum := by decide
  have hdescent : baseEnd_8213009 < baseStart_8213009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213066 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_8213066 : Nat := 118140960795 + 8213066 * 2 ^ 59
def prefixEnd_8213066 : Nat := 4983230072969 + 3 ^ 40 * 8213066 * 2
def baseEnd_8213066 : Nat := 1405750168366556191734601

theorem tailTrace_8213066 : CollatzResearch.WordTrace tailWord_8213066 prefixEnd_8213066 1405750168366556191734601 := by
  unfold tailWord_8213066
  simp only [CollatzResearch.WordTrace]
  refine ⟨74888781615868009211212763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199703417642314691229900701 74888781615868009211212763)
  ·
    refine ⟨112333172423802013816819145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74888781615868009211212763 112333172423802013816819145)
    ·
      refine ⟨84249879317851510362614359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112333172423802013816819145 84249879317851510362614359)
      ·
        refine ⟨126374818976777265543921539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84249879317851510362614359 126374818976777265543921539)
        ·
          refine ⟨189562228465165898315882309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126374818976777265543921539 189562228465165898315882309)
          ·
            refine ⟨35542917837218605934227933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189562228465165898315882309 35542917837218605934227933)
            ·
              refine ⟨13328594188956977225335475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35542917837218605934227933 13328594188956977225335475)
              ·
                refine ⟨19992891283435465838003213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328594188956977225335475 19992891283435465838003213)
                ·
                  refine ⟨7497334231288299689251205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19992891283435465838003213 7497334231288299689251205)
                  ·
                    refine ⟨1405750168366556191734601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497334231288299689251205 1405750168366556191734601)
                    ·
                      rfl

theorem cell23_8213066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_8213066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213066 prefixEnd_8213066 := by exact prefixLift 8213066
  have htrace : WordTrace (prefixWord ++ tailWord_8213066) baseStart_8213066 baseEnd_8213066 := by
    simpa [prefixWord, tailWord_8213066, baseEnd_8213066] using wordTrace_append hprefix tailTrace_8213066
  have hstable : (prefixWord ++ tailWord_8213066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213066).length < 2 ^ (prefixWord ++ tailWord_8213066).sum := by decide
  have hdescent : baseEnd_8213066 < baseStart_8213066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213079 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 6]
def baseStart_8213079 : Nat := 118140960795 + 8213079 * 2 ^ 59
def prefixEnd_8213079 : Nat := 4983230072969 + 3 ^ 40 * 8213079 * 2
def baseEnd_8213079 : Nat := 468584131149797447149027

theorem tailTrace_8213079 : CollatzResearch.WordTrace tailWord_8213079 prefixEnd_8213079 468584131149797447149027 := by
  unfold tailWord_8213079
  simp only [CollatzResearch.WordTrace]
  refine ⟨299555600612424940065074291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199703733741616626710049527 299555600612424940065074291)
  ·
    refine ⟨449333400918637410097611437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299555600612424940065074291 449333400918637410097611437)
    ·
      refine ⟨168500025344489028786604289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449333400918637410097611437 168500025344489028786604289)
      ·
        refine ⟨126375019008366771589953217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168500025344489028786604289 126375019008366771589953217)
        ·
          refine ⟨94781264256275078692464913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126375019008366771589953217 94781264256275078692464913)
          ·
            refine ⟨71085948192206309019348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94781264256275078692464913 71085948192206309019348685)
            ·
              refine ⟨26657230572077365882255757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71085948192206309019348685 26657230572077365882255757)
              ·
                refine ⟨9996461464529012205845909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26657230572077365882255757 9996461464529012205845909)
                ·
                  refine ⟨468584131149797447149027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9996461464529012205845909 468584131149797447149027)
                  ·
                    rfl

theorem cell23_8213079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 6].length) (baseStart_8213079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213079 prefixEnd_8213079 := by exact prefixLift 8213079
  have htrace : WordTrace (prefixWord ++ tailWord_8213079) baseStart_8213079 baseEnd_8213079 := by
    simpa [prefixWord, tailWord_8213079, baseEnd_8213079] using wordTrace_append hprefix tailTrace_8213079
  have hstable : (prefixWord ++ tailWord_8213079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213079).length < 2 ^ (prefixWord ++ tailWord_8213079).sum := by decide
  have hdescent : baseEnd_8213079 < baseStart_8213079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213090 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8213090 : Nat := 118140960795 + 8213090 * 2 ^ 59
def prefixEnd_8213090 : Nat := 4983230072969 + 3 ^ 40 * 8213090 * 2
def baseEnd_8213090 : Nat := 4217262828635376481303693

theorem tailTrace_8213090 : CollatzResearch.WordTrace tailWord_8213090 prefixEnd_8213090 4217262828635376481303693 := by
  unfold tailWord_8213090
  simp only [CollatzResearch.WordTrace]
  refine ⟨74889000453846272235931181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199704001210256725962483149 74889000453846272235931181)
  ·
    refine ⟨28083375170192352088474193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74889000453846272235931181 28083375170192352088474193)
    ·
      refine ⟨21062531377644264066355645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28083375170192352088474193 21062531377644264066355645)
      ·
        refine ⟨7898449266616599024883367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21062531377644264066355645 7898449266616599024883367)
        ·
          refine ⟨11847673899924898537325051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898449266616599024883367 11847673899924898537325051)
          ·
            refine ⟨17771510849887347805987577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847673899924898537325051 17771510849887347805987577)
            ·
              refine ⟨13328633137415510854490683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771510849887347805987577 13328633137415510854490683)
              ·
                refine ⟨19992949706123266281736025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328633137415510854490683 19992949706123266281736025)
                ·
                  refine ⟨14994712279592449711302019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19992949706123266281736025 14994712279592449711302019)
                  ·
                    refine ⟨22492068419388674566953029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14994712279592449711302019 22492068419388674566953029)
                    ·
                      refine ⟨4217262828635376481303693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22492068419388674566953029 4217262828635376481303693)
                      ·
                        rfl

theorem cell23_8213090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8213090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213090 prefixEnd_8213090 := by exact prefixLift 8213090
  have htrace : WordTrace (prefixWord ++ tailWord_8213090) baseStart_8213090 baseEnd_8213090 := by
    simpa [prefixWord, tailWord_8213090, baseEnd_8213090] using wordTrace_append hprefix tailTrace_8213090
  have hstable : (prefixWord ++ tailWord_8213090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213090).length < 2 ^ (prefixWord ++ tailWord_8213090).sum := by decide
  have hdescent : baseEnd_8213090 < baseStart_8213090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213093 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_8213093 : Nat := 118140960795 + 8213093 * 2 ^ 59
def prefixEnd_8213093 : Nat := 4983230072969 + 3 ^ 40 * 8213093 * 2
def baseEnd_8213093 : Nat := 4217264369077339969566179

theorem tailTrace_8213093 : CollatzResearch.WordTrace tailWord_8213093 prefixEnd_8213093 4217264369077339969566179 := by
  unfold tailWord_8213093
  simp only [CollatzResearch.WordTrace]
  refine ⟨299556111234374220456083933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199704074156249480304055955 299556111234374220456083933)
  ·
    refine ⟨112333541712890332671031475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299556111234374220456083933 112333541712890332671031475)
    ·
      refine ⟨168500312569335499006547213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112333541712890332671031475 168500312569335499006547213)
      ·
        refine ⟨63187617213500812127455205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168500312569335499006547213 63187617213500812127455205)
        ·
          refine ⟨11847678227531402273897851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63187617213500812127455205 11847678227531402273897851)
          ·
            refine ⟨17771517341297103410846777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847678227531402273897851 17771517341297103410846777)
            ·
              refine ⟨13328638005972827558135083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771517341297103410846777 13328638005972827558135083)
              ·
                refine ⟨19992957008959241337202625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328638005972827558135083 19992957008959241337202625)
                ·
                  refine ⟨14994717756719431002901969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19992957008959241337202625 14994717756719431002901969)
                  ·
                    refine ⟨11246038317539573252176477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14994717756719431002901969 11246038317539573252176477)
                    ·
                      refine ⟨4217264369077339969566179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246038317539573252176477 4217264369077339969566179)
                      ·
                        rfl

theorem cell23_8213093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_8213093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213093 prefixEnd_8213093 := by exact prefixLift 8213093
  have htrace : WordTrace (prefixWord ++ tailWord_8213093) baseStart_8213093 baseEnd_8213093 := by
    simpa [prefixWord, tailWord_8213093, baseEnd_8213093] using wordTrace_append hprefix tailTrace_8213093
  have hstable : (prefixWord ++ tailWord_8213093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213093).length < 2 ^ (prefixWord ++ tailWord_8213093).sum := by decide
  have hdescent : baseEnd_8213093 < baseStart_8213093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213117 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_8213117 : Nat := 118140960795 + 8213117 * 2 ^ 59
def prefixEnd_8213117 : Nat := 4983230072969 + 3 ^ 40 * 8213117 * 2
def baseEnd_8213117 : Nat := 1405758897537682625222023

theorem tailTrace_8213117 : CollatzResearch.WordTrace tailWord_8213117 prefixEnd_8213117 1405758897537682625222023 := by
  unfold tailWord_8213117
  simp only [CollatzResearch.WordTrace]
  refine ⟨299556986586287272554957605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199704657724191515036638403 299556986586287272554957605)
  ·
    refine ⟨56166934984928863604054551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299556986586287272554957605 56166934984928863604054551)
    ·
      refine ⟨84250402477393295406081827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56166934984928863604054551 84250402477393295406081827)
      ·
        refine ⟨126375603716089943109122741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84250402477393295406081827 126375603716089943109122741)
        ·
          refine ⟨11847712848383432166480257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126375603716089943109122741 11847712848383432166480257)
          ·
            refine ⟨8885784636287574124860193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11847712848383432166480257 8885784636287574124860193)
            ·
              refine ⟨6664338477215680593645145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885784636287574124860193 6664338477215680593645145)
              ·
                refine ⟨4998253857911760445233859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6664338477215680593645145 4998253857911760445233859)
                ·
                  refine ⟨7497380786867640667850789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998253857911760445233859 7497380786867640667850789)
                  ·
                    refine ⟨1405758897537682625222023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497380786867640667850789 1405758897537682625222023)
                    ·
                      rfl

theorem cell23_8213117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_8213117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213117 prefixEnd_8213117 := by exact prefixLift 8213117
  have htrace : WordTrace (prefixWord ++ tailWord_8213117) baseStart_8213117 baseEnd_8213117 := by
    simpa [prefixWord, tailWord_8213117, baseEnd_8213117] using wordTrace_append hprefix tailTrace_8213117
  have hstable : (prefixWord ++ tailWord_8213117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213117).length < 2 ^ (prefixWord ++ tailWord_8213117).sum := by decide
  have hdescent : baseEnd_8213117 < baseStart_8213117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213140 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_8213140 : Nat := 118140960795 + 8213140 * 2 ^ 59
def prefixEnd_8213140 : Nat := 4983230072969 + 3 ^ 40 * 8213140 * 2
def baseEnd_8213140 : Nat := 4217288502668101285678463

theorem tailTrace_8213140 : CollatzResearch.WordTrace tailWord_8213140 prefixEnd_8213140 4217288502668101285678463 := by
  unfold tailWord_8213140
  simp only [CollatzResearch.WordTrace]
  refine ⟨149778912732601973741522437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199705216976802631655363249 149778912732601973741522437)
  ·
    refine ⟨28083546137362870076535457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149778912732601973741522437 28083546137362870076535457)
    ·
      refine ⟨21062659603022152557401593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28083546137362870076535457 21062659603022152557401593)
      ·
        refine ⟨15796994702266614418051195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21062659603022152557401593 15796994702266614418051195)
        ·
          refine ⟨23695492053399921627076793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796994702266614418051195 23695492053399921627076793)
          ·
            refine ⟨17771619040049941220307595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23695492053399921627076793 17771619040049941220307595)
            ·
              refine ⟨26657428560074911830461393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771619040049941220307595 26657428560074911830461393)
              ·
                refine ⟨19993071420056183872846045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26657428560074911830461393 19993071420056183872846045)
                ·
                  refine ⟨7497401782521068952317267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19993071420056183872846045 7497401782521068952317267)
                  ·
                    refine ⟨11246102673781603428475901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497401782521068952317267 11246102673781603428475901)
                    ·
                      refine ⟨4217288502668101285678463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246102673781603428475901 4217288502668101285678463)
                      ·
                        rfl

theorem cell23_8213140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_8213140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213140 prefixEnd_8213140 := by exact prefixLift 8213140
  have htrace : WordTrace (prefixWord ++ tailWord_8213140) baseStart_8213140 baseEnd_8213140 := by
    simpa [prefixWord, tailWord_8213140, baseEnd_8213140] using wordTrace_append hprefix tailTrace_8213140
  have hstable : (prefixWord ++ tailWord_8213140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213140).length < 2 ^ (prefixWord ++ tailWord_8213140).sum := by decide
  have hdescent : baseEnd_8213140 < baseStart_8213140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213156 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_8213156 : Nat := 118140960795 + 8213156 * 2 ^ 59
def prefixEnd_8213156 : Nat := 4983230072969 + 3 ^ 40 * 8213156 * 2
def baseEnd_8213156 : Nat := 1405765572786191074359463

theorem tailTrace_8213156 : CollatzResearch.WordTrace tailWord_8213156 prefixEnd_8213156 1405765572786191074359463 := by
  unfold tailWord_8213156
  simp only [CollatzResearch.WordTrace]
  refine ⟨149779204516572991107813661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199705606022097321477084881 149779204516572991107813661)
  ·
    refine ⟨56167201693714871665430123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149779204516572991107813661 56167201693714871665430123)
    ·
      refine ⟨84250802540572307498145185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56167201693714871665430123 84250802540572307498145185)
      ·
        refine ⟨63188101905429230623608889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84250802540572307498145185 63188101905429230623608889)
        ·
          refine ⟨47391076429071922967706667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63188101905429230623608889 47391076429071922967706667)
          ·
            refine ⟨71086614643607884451560001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47391076429071922967706667 71086614643607884451560001)
            ·
              refine ⟨53314960982705913338670001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71086614643607884451560001 53314960982705913338670001)
              ·
                refine ⟨39986220737029435004002501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53314960982705913338670001 39986220737029435004002501)
                ·
                  refine ⟨7497416388193019063250469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39986220737029435004002501 7497416388193019063250469)
                  ·
                    refine ⟨1405765572786191074359463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497416388193019063250469 1405765572786191074359463)
                    ·
                      rfl

theorem cell23_8213156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_8213156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213156 prefixEnd_8213156 := by exact prefixLift 8213156
  have htrace : WordTrace (prefixWord ++ tailWord_8213156) baseStart_8213156 baseEnd_8213156 := by
    simpa [prefixWord, tailWord_8213156, baseEnd_8213156] using wordTrace_append hprefix tailTrace_8213156
  have hstable : (prefixWord ++ tailWord_8213156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213156).length < 2 ^ (prefixWord ++ tailWord_8213156).sum := by decide
  have hdescent : baseEnd_8213156 < baseStart_8213156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213173 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_8213173 : Nat := 118140960795 + 8213173 * 2 ^ 59
def prefixEnd_8213173 : Nat := 4983230072969 + 3 ^ 40 * 8213173 * 2
def baseEnd_8213173 : Nat := 1405768482509899885521937

theorem tailTrace_8213173 : CollatzResearch.WordTrace tailWord_8213173 prefixEnd_8213173 1405768482509899885521937 := by
  unfold tailWord_8213173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299559029074084394118996173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199706019382722929412664115 299559029074084394118996173)
  ·
    refine ⟨112334635902781647794623565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299559029074084394118996173 112334635902781647794623565)
    ·
      refine ⟨42125488463543117922983837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112334635902781647794623565 42125488463543117922983837)
      ·
        refine ⟨15797058173828669221118939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42125488463543117922983837 15797058173828669221118939)
        ·
          refine ⟨23695587260743003831678409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15797058173828669221118939 23695587260743003831678409)
          ·
            refine ⟨17771690445557252873758807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23695587260743003831678409 17771690445557252873758807)
            ·
              refine ⟨26657535668335879310638211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771690445557252873758807 26657535668335879310638211)
              ·
                refine ⟨39986303502503818965957317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26657535668335879310638211 39986303502503818965957317)
                ·
                  refine ⟨7497431906719466056116997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39986303502503818965957317 7497431906719466056116997)
                  ·
                    refine ⟨1405768482509899885521937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497431906719466056116997 1405768482509899885521937)
                    ·
                      rfl

theorem cell23_8213173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_8213173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213173 prefixEnd_8213173 := by exact prefixLift 8213173
  have htrace : WordTrace (prefixWord ++ tailWord_8213173) baseStart_8213173 baseEnd_8213173 := by
    simpa [prefixWord, tailWord_8213173, baseEnd_8213173] using wordTrace_append hprefix tailTrace_8213173
  have hstable : (prefixWord ++ tailWord_8213173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213173).length < 2 ^ (prefixWord ++ tailWord_8213173).sum := by decide
  have hdescent : baseEnd_8213173 < baseStart_8213173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213179 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3]
def baseStart_8213179 : Nat := 118140960795 + 8213179 * 2 ^ 59
def prefixEnd_8213179 : Nat := 4983230072969 + 3 ^ 40 * 8213179 * 2
def baseEnd_8213179 : Nat := 4217308528413626633090783

theorem tailTrace_8213179 : CollatzResearch.WordTrace tailWord_8213179 prefixEnd_8213179 4217308528413626633090783 := by
  unfold tailWord_8213179
  simp only [CollatzResearch.WordTrace]
  refine ⟨299559247912062657143714591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199706165274708438095809727 299559247912062657143714591)
  ·
    refine ⟨449338871868093985715571887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299559247912062657143714591 449338871868093985715571887)
    ·
      refine ⟨674008307802140978573357831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449338871868093985715571887 674008307802140978573357831)
      ·
        refine ⟨1011012461703211467860036747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674008307802140978573357831 1011012461703211467860036747)
        ·
          refine ⟨1516518692554817201790055121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011012461703211467860036747 1516518692554817201790055121)
          ·
            refine ⟨1137389019416112901342541341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516518692554817201790055121 1137389019416112901342541341)
            ·
              refine ⟨426520882281042338003453003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1137389019416112901342541341 426520882281042338003453003)
              ·
                refine ⟨639781323421563507005179505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426520882281042338003453003 639781323421563507005179505)
                ·
                  refine ⟨479835992566172630253884629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639781323421563507005179505 479835992566172630253884629)
                  ·
                    refine ⟨11246156075769671021575421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 479835992566172630253884629 11246156075769671021575421)
                    ·
                      refine ⟨4217308528413626633090783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246156075769671021575421 4217308528413626633090783)
                      ·
                        rfl

theorem cell23_8213179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].length) (baseStart_8213179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213179 prefixEnd_8213179 := by exact prefixLift 8213179
  have htrace : WordTrace (prefixWord ++ tailWord_8213179) baseStart_8213179 baseEnd_8213179 := by
    simpa [prefixWord, tailWord_8213179, baseEnd_8213179] using wordTrace_append hprefix tailTrace_8213179
  have hstable : (prefixWord ++ tailWord_8213179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213179).length < 2 ^ (prefixWord ++ tailWord_8213179).sum := by decide
  have hdescent : baseEnd_8213179 < baseStart_8213179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213180 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_8213180 : Nat := 118140960795 + 8213180 * 2 ^ 59
def prefixEnd_8213180 : Nat := 4983230072969 + 3 ^ 40 * 8213180 * 2
def baseEnd_8213180 : Nat := 4217309041894281129178279

theorem tailTrace_8213180 : CollatzResearch.WordTrace tailWord_8213180 prefixEnd_8213180 4217309041894281129178279 := by
  unfold tailWord_8213180
  simp only [CollatzResearch.WordTrace]
  refine ⟨149779642192529517157250497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199706189590039356209667329 149779642192529517157250497)
  ·
    refine ⟨112334731644397137867937873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149779642192529517157250497 112334731644397137867937873)
    ·
      refine ⟨84251048733297853400953405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112334731644397137867937873 84251048733297853400953405)
      ·
        refine ⟨31594143274986695025357527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84251048733297853400953405 31594143274986695025357527)
        ·
          refine ⟨47391214912480042538036291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31594143274986695025357527 47391214912480042538036291)
          ·
            refine ⟨71086822368720063807054437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47391214912480042538036291 71086822368720063807054437)
            ·
              refine ⟨13328779194135011963822707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71086822368720063807054437 13328779194135011963822707)
              ·
                refine ⟨19993168791202517945734061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13328779194135011963822707 19993168791202517945734061)
                ·
                  refine ⟨7497438296700944229650273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19993168791202517945734061 7497438296700944229650273)
                  ·
                    refine ⟨5623078722525708172237705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7497438296700944229650273 5623078722525708172237705)
                    ·
                      refine ⟨4217309041894281129178279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623078722525708172237705 4217309041894281129178279)
                      ·
                        rfl

theorem cell23_8213180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_8213180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213180 prefixEnd_8213180 := by exact prefixLift 8213180
  have htrace : WordTrace (prefixWord ++ tailWord_8213180) baseStart_8213180 baseEnd_8213180 := by
    simpa [prefixWord, tailWord_8213180, baseEnd_8213180] using wordTrace_append hprefix tailTrace_8213180
  have hstable : (prefixWord ++ tailWord_8213180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213180).length < 2 ^ (prefixWord ++ tailWord_8213180).sum := by decide
  have hdescent : baseEnd_8213180 < baseStart_8213180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213197 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_8213197 : Nat := 118140960795 + 8213197 * 2 ^ 59
def prefixEnd_8213197 : Nat := 4983230072969 + 3 ^ 40 * 8213197 * 2
def baseEnd_8213197 : Nat := 4217317771065407562665701

theorem tailTrace_8213197 : CollatzResearch.WordTrace tailWord_8213197 prefixEnd_8213197 4217317771065407562665701 := by
  unfold tailWord_8213197
  simp only [CollatzResearch.WordTrace]
  refine ⟨299559904425997446217869845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199706602950664964145246563 299559904425997446217869845)
  ·
    refine ⟨14041870519968630291462649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299559904425997446217869845 14041870519968630291462649)
    ·
      refine ⟨10531402889976472718596987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14041870519968630291462649 10531402889976472718596987)
      ·
        refine ⟨15797104334964709077895481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10531402889976472718596987 15797104334964709077895481)
        ·
          refine ⟨11847828251223531808421611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15797104334964709077895481 11847828251223531808421611)
          ·
            refine ⟨17771742376835297712632417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847828251223531808421611 17771742376835297712632417)
            ·
              refine ⟨13328806782626473284474313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17771742376835297712632417 13328806782626473284474313)
              ·
                refine ⟨9996605086969854963355735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13328806782626473284474313 9996605086969854963355735)
                ·
                  refine ⟨14994907630454782445033603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9996605086969854963355735 14994907630454782445033603)
                  ·
                    refine ⟨22492361445682173667550405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14994907630454782445033603 22492361445682173667550405)
                    ·
                      refine ⟨4217317771065407562665701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22492361445682173667550405 4217317771065407562665701)
                      ·
                        rfl

theorem cell23_8213197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_8213197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213197 prefixEnd_8213197 := by exact prefixLift 8213197
  have htrace : WordTrace (prefixWord ++ tailWord_8213197) baseStart_8213197 baseEnd_8213197 := by
    simpa [prefixWord, tailWord_8213197, baseEnd_8213197] using wordTrace_append hprefix tailTrace_8213197
  have hstable : (prefixWord ++ tailWord_8213197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213197).length < 2 ^ (prefixWord ++ tailWord_8213197).sum := by decide
  have hdescent : baseEnd_8213197 < baseStart_8213197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213209 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_8213209 : Nat := 118140960795 + 8213209 * 2 ^ 59
def prefixEnd_8213209 : Nat := 4983230072969 + 3 ^ 40 * 8213209 * 2
def baseEnd_8213209 : Nat := 4217323932833261515715645

theorem tailTrace_8213209 : CollatzResearch.WordTrace tailWord_8213209 prefixEnd_8213209 4217323932833261515715645 := by
  unfold tailWord_8213209
  simp only [CollatzResearch.WordTrace]
  refine ⟨299560342101953972267306681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199706894734635981511537787 299560342101953972267306681)
  ·
    refine ⟨224670256576465479200480011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299560342101953972267306681 224670256576465479200480011)
    ·
      refine ⟨337005384864698218800720017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224670256576465479200480011 337005384864698218800720017)
      ·
        refine ⟨252754038648523664100540013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337005384864698218800720017 252754038648523664100540013)
        ·
          refine ⟨94782764493196374037702505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252754038648523664100540013 94782764493196374037702505)
          ·
            refine ⟨71087073369897280528276879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94782764493196374037702505 71087073369897280528276879)
            ·
              refine ⟨106630610054845920792415319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71087073369897280528276879 106630610054845920792415319)
              ·
                refine ⟨159945915082268881188622979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106630610054845920792415319 159945915082268881188622979)
                ·
                  refine ⟨239918872623403321782934469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159945915082268881188622979 239918872623403321782934469)
                  ·
                    refine ⟨44984788616888122834300213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239918872623403321782934469 44984788616888122834300213)
                    ·
                      refine ⟨4217323932833261515715645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44984788616888122834300213 4217323932833261515715645)
                      ·
                        rfl

theorem cell23_8213209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_8213209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213209 prefixEnd_8213209 := by exact prefixLift 8213209
  have htrace : WordTrace (prefixWord ++ tailWord_8213209) baseStart_8213209 baseEnd_8213209 := by
    simpa [prefixWord, tailWord_8213209, baseEnd_8213209] using wordTrace_append hprefix tailTrace_8213209
  have hstable : (prefixWord ++ tailWord_8213209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213209).length < 2 ^ (prefixWord ++ tailWord_8213209).sum := by decide
  have hdescent : baseEnd_8213209 < baseStart_8213209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213239 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_8213239 : Nat := 118140960795 + 8213239 * 2 ^ 59
def prefixEnd_8213239 : Nat := 4983230072969 + 3 ^ 40 * 8213239 * 2
def baseEnd_8213239 : Nat := 4217339337252896398340507

theorem tailTrace_8213239 : CollatzResearch.WordTrace tailWord_8213239 prefixEnd_8213239 4217339337252896398340507 := by
  unfold tailWord_8213239
  simp only [CollatzResearch.WordTrace]
  refine ⟨299561436291845287390898771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199707624194563524927265847 299561436291845287390898771)
  ·
    refine ⟨449342154437767931086348157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299561436291845287390898771 449342154437767931086348157)
    ·
      refine ⟨168503307914162974157380559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449342154437767931086348157 168503307914162974157380559)
      ·
        refine ⟨252754961871244461236070839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168503307914162974157380559 252754961871244461236070839)
        ·
          refine ⟨379132442806866691854106259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252754961871244461236070839 379132442806866691854106259)
          ·
            refine ⟨568698664210300037781159389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379132442806866691854106259 568698664210300037781159389)
            ·
              refine ⟨213261999078862514167934771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568698664210300037781159389 213261999078862514167934771)
              ·
                refine ⟨319892998618293771251902157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213261999078862514167934771 319892998618293771251902157)
                ·
                  refine ⟨119959874481860164219463309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319892998618293771251902157 119959874481860164219463309)
                  ·
                    refine ⟨44984952930697561582298741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119959874481860164219463309 44984952930697561582298741)
                    ·
                      refine ⟨4217339337252896398340507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44984952930697561582298741 4217339337252896398340507)
                      ·
                        rfl

theorem cell23_8213239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_8213239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213239 prefixEnd_8213239 := by exact prefixLift 8213239
  have htrace : WordTrace (prefixWord ++ tailWord_8213239) baseStart_8213239 baseEnd_8213239 := by
    simpa [prefixWord, tailWord_8213239, baseEnd_8213239] using wordTrace_append hprefix tailTrace_8213239
  have hstable : (prefixWord ++ tailWord_8213239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213239).length < 2 ^ (prefixWord ++ tailWord_8213239).sum := by decide
  have hdescent : baseEnd_8213239 < baseStart_8213239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213256 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_8213256 : Nat := 118140960795 + 8213256 * 2 ^ 59
def prefixEnd_8213256 : Nat := 4983230072969 + 3 ^ 40 * 8213256 * 2
def baseEnd_8213256 : Nat := 4217348066424022831827929

theorem tailTrace_8213256 : CollatzResearch.WordTrace tailWord_8213256 prefixEnd_8213256 4217348066424022831827929 := by
  unfold tailWord_8213256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149781028166391849647133811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199708037555189132862845081 149781028166391849647133811)
  ·
    refine ⟨224671542249587774470700717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149781028166391849647133811 224671542249587774470700717)
    ·
      refine ⟨84251828343595415426512769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224671542249587774470700717 84251828343595415426512769)
      ·
        refine ⟨63188871257696561569884577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84251828343595415426512769 63188871257696561569884577)
        ·
          refine ⟨47391653443272421177413433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63188871257696561569884577 47391653443272421177413433)
          ·
            refine ⟨35543740082454315883060075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47391653443272421177413433 35543740082454315883060075)
            ·
              refine ⟨53315610123681473824590113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35543740082454315883060075 53315610123681473824590113)
              ·
                refine ⟨39986707592761105368442585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53315610123681473824590113 39986707592761105368442585)
                ·
                  refine ⟨29990030694570829026331939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39986707592761105368442585 29990030694570829026331939)
                  ·
                    refine ⟨44985046041856243539497909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29990030694570829026331939 44985046041856243539497909)
                    ·
                      refine ⟨4217348066424022831827929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44985046041856243539497909 4217348066424022831827929)
                      ·
                        rfl

theorem cell23_8213256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_8213256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213256 prefixEnd_8213256 := by exact prefixLift 8213256
  have htrace : WordTrace (prefixWord ++ tailWord_8213256) baseStart_8213256 baseEnd_8213256 := by
    simpa [prefixWord, tailWord_8213256, baseEnd_8213256] using wordTrace_append hprefix tailTrace_8213256
  have hstable : (prefixWord ++ tailWord_8213256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213256).length < 2 ^ (prefixWord ++ tailWord_8213256).sum := by decide
  have hdescent : baseEnd_8213256 < baseStart_8213256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213259 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 9]
def baseStart_8213259 : Nat := 118140960795 + 8213259 * 2 ^ 59
def prefixEnd_8213259 : Nat := 4983230072969 + 3 ^ 40 * 8213259 * 2
def baseEnd_8213259 : Nat := 468594400762887368898935

theorem tailTrace_8213259 : CollatzResearch.WordTrace tailWord_8213259 prefixEnd_8213259 468594400762887368898935 := by
  unfold tailWord_8213259
  simp only [CollatzResearch.WordTrace]
  refine ⟨299562165751772830806626831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199708110501181887204417887 299562165751772830806626831)
  ·
    refine ⟨449343248627659246209940247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299562165751772830806626831 449343248627659246209940247)
    ·
      refine ⟨674014872941488869314910371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449343248627659246209940247 674014872941488869314910371)
      ·
        refine ⟨1011022309412233303972365557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674014872941488869314910371 1011022309412233303972365557)
        ·
          refine ⟨94783341507396872247409271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1011022309412233303972365557 94783341507396872247409271)
          ·
            refine ⟨142175012261095308371113907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94783341507396872247409271 142175012261095308371113907)
            ·
              refine ⟨213262518391642962556670861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142175012261095308371113907 213262518391642962556670861)
              ·
                refine ⟨79973444396866110958751573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213262518391642962556670861 79973444396866110958751573)
                ·
                  refine ⟨468594400762887368898935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79973444396866110958751573 468594400762887368898935)
                  ·
                    rfl

theorem cell23_8213259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_8213259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213259 prefixEnd_8213259 := by exact prefixLift 8213259
  have htrace : WordTrace (prefixWord ++ tailWord_8213259) baseStart_8213259 baseEnd_8213259 := by
    simpa [prefixWord, tailWord_8213259, baseEnd_8213259] using wordTrace_append hprefix tailTrace_8213259
  have hstable : (prefixWord ++ tailWord_8213259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213259).length < 2 ^ (prefixWord ++ tailWord_8213259).sum := by decide
  have hdescent : baseEnd_8213259 < baseStart_8213259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213300 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_8213300 : Nat := 118140960795 + 8213300 * 2 ^ 59
def prefixEnd_8213300 : Nat := 4983230072969 + 3 ^ 40 * 8213300 * 2
def baseEnd_8213300 : Nat := 4217370659572820659677727

theorem tailTrace_8213300 : CollatzResearch.WordTrace tailWord_8213300 prefixEnd_8213300 4217370659572820659677727 := by
  unfold tailWord_8213300
  simp only [CollatzResearch.WordTrace]
  refine ⟨149781830572312147404434677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199709107429749529872579569 149781830572312147404434677)
  ·
    refine ⟨14042046616154263819165751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149781830572312147404434677 14042046616154263819165751)
    ·
      refine ⟨21063069924231395728748627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14042046616154263819165751 21063069924231395728748627)
      ·
        refine ⟨31594604886347093593122941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063069924231395728748627 31594604886347093593122941)
        ·
          refine ⟨11847976832380160097421103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31594604886347093593122941 11847976832380160097421103)
          ·
            refine ⟨17771965248570240146131655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11847976832380160097421103 17771965248570240146131655)
            ·
              refine ⟨26657947872855360219197483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771965248570240146131655 26657947872855360219197483)
              ·
                refine ⟨39986921809283040328796225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26657947872855360219197483 39986921809283040328796225)
                ·
                  refine ⟨29990191356962280246597169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39986921809283040328796225 29990191356962280246597169)
                  ·
                    refine ⟨22492643517721710184947877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29990191356962280246597169 22492643517721710184947877)
                    ·
                      refine ⟨4217370659572820659677727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22492643517721710184947877 4217370659572820659677727)
                      ·
                        rfl

theorem cell23_8213300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_8213300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213300 prefixEnd_8213300 := by exact prefixLift 8213300
  have htrace : WordTrace (prefixWord ++ tailWord_8213300) baseStart_8213300 baseEnd_8213300 := by
    simpa [prefixWord, tailWord_8213300, baseEnd_8213300] using wordTrace_append hprefix tailTrace_8213300
  have hstable : (prefixWord ++ tailWord_8213300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213300).length < 2 ^ (prefixWord ++ tailWord_8213300).sum := by decide
  have hdescent : baseEnd_8213300 < baseStart_8213300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213343 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 4, 2]
def baseStart_8213343 : Nat := 118140960795 + 8213343 * 2 ^ 59
def prefixEnd_8213343 : Nat := 4983230072969 + 3 ^ 40 * 8213343 * 2
def baseEnd_8213343 : Nat := 4217392739240963991440029

theorem tailTrace_8213343 : CollatzResearch.WordTrace tailWord_8213343 prefixEnd_8213343 4217392739240963991440029 := by
  unfold tailWord_8213343
  simp only [CollatzResearch.WordTrace]
  refine ⟨299565229483468513152684683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199710152988979008768456455 299565229483468513152684683)
  ·
    refine ⟨449347844225202769729027025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299565229483468513152684683 449347844225202769729027025)
    ·
      refine ⟨337010883168902077296770269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449347844225202769729027025 337010883168902077296770269)
      ·
        refine ⟨126379081188338278986288851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337010883168902077296770269 126379081188338278986288851)
        ·
          refine ⟨189568621782507418479433277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126379081188338278986288851 189568621782507418479433277)
          ·
            refine ⟨71088233168440281929787479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189568621782507418479433277 71088233168440281929787479)
            ·
              refine ⟨106632349752660422894681219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71088233168440281929787479 106632349752660422894681219)
              ·
                refine ⟨159948524628990634342021829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106632349752660422894681219 159948524628990634342021829)
                ·
                  refine ⟨29990348367935743939129093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159948524628990634342021829 29990348367935743939129093)
                  ·
                    refine ⟨5623190318987951988586705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29990348367935743939129093 5623190318987951988586705)
                    ·
                      refine ⟨4217392739240963991440029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623190318987951988586705 4217392739240963991440029)
                      ·
                        rfl

theorem cell23_8213343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_8213343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213343 prefixEnd_8213343 := by exact prefixLift 8213343
  have htrace : WordTrace (prefixWord ++ tailWord_8213343) baseStart_8213343 baseEnd_8213343 := by
    simpa [prefixWord, tailWord_8213343, baseEnd_8213343] using wordTrace_append hprefix tailTrace_8213343
  have hstable : (prefixWord ++ tailWord_8213343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213343).length < 2 ^ (prefixWord ++ tailWord_8213343).sum := by decide
  have hdescent : baseEnd_8213343 < baseStart_8213343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213356 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_8213356 : Nat := 118140960795 + 8213356 * 2 ^ 59
def prefixEnd_8213356 : Nat := 4983230072969 + 3 ^ 40 * 8213356 * 2
def baseEnd_8213356 : Nat := 4217399414489472440577469

theorem tailTrace_8213356 : CollatzResearch.WordTrace tailWord_8213356 prefixEnd_8213356 4217399414489472440577469 := by
  unfold tailWord_8213356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149782851816210708186453961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199710469088280944248605281 149782851816210708186453961)
  ·
    refine ⟨112337138862158031139840471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149782851816210708186453961 112337138862158031139840471)
    ·
      refine ⟨168505708293237046709760707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112337138862158031139840471 168505708293237046709760707)
      ·
        refine ⟨252758562439855570064641061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168505708293237046709760707 252758562439855570064641061)
        ·
          refine ⟨47392230457472919387120199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252758562439855570064641061 47392230457472919387120199)
          ·
            refine ⟨71088345686209379080680299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47392230457472919387120199 71088345686209379080680299)
            ·
              refine ⟨106632518529314068621020449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71088345686209379080680299 106632518529314068621020449)
              ·
                refine ⟨79974388896985551465765337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106632518529314068621020449 79974388896985551465765337)
                ·
                  refine ⟨59980791672739163599324003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79974388896985551465765337 59980791672739163599324003)
                  ·
                    refine ⟨89971187509108745398986005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59980791672739163599324003 89971187509108745398986005)
                    ·
                      refine ⟨4217399414489472440577469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89971187509108745398986005 4217399414489472440577469)
                      ·
                        rfl

theorem cell23_8213356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_8213356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213356 prefixEnd_8213356 := by exact prefixLift 8213356
  have htrace : WordTrace (prefixWord ++ tailWord_8213356) baseStart_8213356 baseEnd_8213356 := by
    simpa [prefixWord, tailWord_8213356, baseEnd_8213356] using wordTrace_append hprefix tailTrace_8213356
  have hstable : (prefixWord ++ tailWord_8213356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213356).length < 2 ^ (prefixWord ++ tailWord_8213356).sum := by decide
  have hdescent : baseEnd_8213356 < baseStart_8213356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213404 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_8213404 : Nat := 118140960795 + 8213404 * 2 ^ 59
def prefixEnd_8213404 : Nat := 4983230072969 + 3 ^ 40 * 8213404 * 2
def baseEnd_8213404 : Nat := 1405808020520296084259083

theorem tailTrace_8213404 : CollatzResearch.WordTrace tailWord_8213404 prefixEnd_8213404 1405808020520296084259083 := by
  unfold tailWord_8213404
  simp only [CollatzResearch.WordTrace]
  refine ⟨149783727168123760285327633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199711636224165013713770177 149783727168123760285327633)
  ·
    refine ⟨112337795376092820213995725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149783727168123760285327633 112337795376092820213995725)
    ·
      refine ⟨42126673266034807580248397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112337795376092820213995725 42126673266034807580248397)
      ·
        refine ⟨15797502474763052842593149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42126673266034807580248397 15797502474763052842593149)
        ·
          refine ⟨5924063428036144815972431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15797502474763052842593149 5924063428036144815972431)
          ·
            refine ⟨8886095142054217223958647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924063428036144815972431 8886095142054217223958647)
            ·
              refine ⟨13329142713081325835937971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886095142054217223958647 13329142713081325835937971)
              ·
                refine ⟨19993714069621988753906957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329142713081325835937971 19993714069621988753906957)
                ·
                  refine ⟨7497642776108245782715109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19993714069621988753906957 7497642776108245782715109)
                  ·
                    refine ⟨1405808020520296084259083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497642776108245782715109 1405808020520296084259083)
                    ·
                      rfl

theorem cell23_8213404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_8213404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213404 prefixEnd_8213404 := by exact prefixLift 8213404
  have htrace : WordTrace (prefixWord ++ tailWord_8213404) baseStart_8213404 baseEnd_8213404 := by
    simpa [prefixWord, tailWord_8213404, baseEnd_8213404] using wordTrace_append hprefix tailTrace_8213404
  have hstable : (prefixWord ++ tailWord_8213404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213404).length < 2 ^ (prefixWord ++ tailWord_8213404).sum := by decide
  have hdescent : baseEnd_8213404 < baseStart_8213404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213477 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_8213477 : Nat := 118140960795 + 8213477 * 2 ^ 59
def prefixEnd_8213477 : Nat := 4983230072969 + 3 ^ 40 * 8213477 * 2
def baseEnd_8213477 : Nat := 1405820515216222155721471

theorem tailTrace_8213477 : CollatzResearch.WordTrace tailWord_8213477 prefixEnd_8213477 1405820515216222155721471 := by
  unfold tailWord_8213477
  simp only [CollatzResearch.WordTrace]
  refine ⟨299570116864983054038062685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199713411243322036025375123 299570116864983054038062685)
  ·
    refine ⟨112338793824368645264273507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299570116864983054038062685 112338793824368645264273507)
    ·
      refine ⟨168508190736552967896410261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112338793824368645264273507 168508190736552967896410261)
      ·
        refine ⟨7898821440775920370144231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168508190736552967896410261 7898821440775920370144231)
        ·
          refine ⟨11848232161163880555216347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7898821440775920370144231 11848232161163880555216347)
          ·
            refine ⟨17772348241745820832824521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11848232161163880555216347 17772348241745820832824521)
            ·
              refine ⟨13329261181309365624618391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17772348241745820832824521 13329261181309365624618391)
              ·
                refine ⟨19993891771964048436927587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329261181309365624618391 19993891771964048436927587)
                ·
                  refine ⟨29990837657946072655391381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19993891771964048436927587 29990837657946072655391381)
                  ·
                    refine ⟨1405820515216222155721471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29990837657946072655391381 1405820515216222155721471)
                    ·
                      rfl

theorem cell23_8213477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_8213477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213477 prefixEnd_8213477 := by exact prefixLift 8213477
  have htrace : WordTrace (prefixWord ++ tailWord_8213477) baseStart_8213477 baseEnd_8213477 := by
    simpa [prefixWord, tailWord_8213477, baseEnd_8213477] using wordTrace_append hprefix tailTrace_8213477
  have hstable : (prefixWord ++ tailWord_8213477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213477).length < 2 ^ (prefixWord ++ tailWord_8213477).sum := by decide
  have hdescent : baseEnd_8213477 < baseStart_8213477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213500 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_8213500 : Nat := 118140960795 + 8213500 * 2 ^ 59
def prefixEnd_8213500 : Nat := 4983230072969 + 3 ^ 40 * 8213500 * 2
def baseEnd_8213500 : Nat := 4217473355703719877176807

theorem tailTrace_8213500 : CollatzResearch.WordTrace tailWord_8213500 prefixEnd_8213500 4217473355703719877176807 := by
  unfold tailWord_8213500
  simp only [CollatzResearch.WordTrace]
  refine ⟨149785477871949864483074977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199713970495933152644099969 149785477871949864483074977)
  ·
    refine ⟨112339108403962398362306233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149785477871949864483074977 112339108403962398362306233)
    ·
      refine ⟨84254331302971798771729675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112339108403962398362306233 84254331302971798771729675)
      ·
        refine ⟨126381496954457698157594513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84254331302971798771729675 126381496954457698157594513)
        ·
          refine ⟨94786122715843273618195885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126381496954457698157594513 94786122715843273618195885)
          ·
            refine ⟨35544796018441227606823457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94786122715843273618195885 35544796018441227606823457)
            ·
              refine ⟨26658597013830920705117593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35544796018441227606823457 26658597013830920705117593)
              ·
                refine ⟨19993947760373190528838195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26658597013830920705117593 19993947760373190528838195)
                ·
                  refine ⟨29990921640559785793257293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19993947760373190528838195 29990921640559785793257293)
                  ·
                    refine ⟨11246595615209919672471485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29990921640559785793257293 11246595615209919672471485)
                    ·
                      refine ⟨4217473355703719877176807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246595615209919672471485 4217473355703719877176807)
                      ·
                        rfl

theorem cell23_8213500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_8213500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213500 prefixEnd_8213500 := by exact prefixLift 8213500
  have htrace : WordTrace (prefixWord ++ tailWord_8213500) baseStart_8213500 baseEnd_8213500 := by
    simpa [prefixWord, tailWord_8213500, baseEnd_8213500] using wordTrace_append hprefix tailTrace_8213500
  have hstable : (prefixWord ++ tailWord_8213500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213500).length < 2 ^ (prefixWord ++ tailWord_8213500).sum := by decide
  have hdescent : baseEnd_8213500 < baseStart_8213500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213560 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_8213560 : Nat := 118140960795 + 8213560 * 2 ^ 59
def prefixEnd_8213560 : Nat := 4983230072969 + 3 ^ 40 * 8213560 * 2
def baseEnd_8213560 : Nat := 4217504164542989642426531

theorem tailTrace_8213560 : CollatzResearch.WordTrace tailWord_8213560 prefixEnd_8213560 4217504164542989642426531 := by
  unfold tailWord_8213560
  simp only [CollatzResearch.WordTrace]
  refine ⟨149786572061841179606667067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199715429415788239475556089 149786572061841179606667067)
  ·
    refine ⟨224679858092761769410000601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149786572061841179606667067 224679858092761769410000601)
    ·
      refine ⟨168509893569571327057500451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224679858092761769410000601 168509893569571327057500451)
      ·
        refine ⟨252764840354356990586250677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168509893569571327057500451 252764840354356990586250677)
        ·
          refine ⟨23696703783220967867461001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252764840354356990586250677 23696703783220967867461001)
          ·
            refine ⟨17772527837415725900595751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23696703783220967867461001 17772527837415725900595751)
            ·
              refine ⟨26658791756123588850893627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17772527837415725900595751 26658791756123588850893627)
              ·
                refine ⟨39988187634185383276340441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26658791756123588850893627 39988187634185383276340441)
                ·
                  refine ⟨29991140725639037457255331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39988187634185383276340441 29991140725639037457255331)
                  ·
                    refine ⟨44986711088458556185882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29991140725639037457255331 44986711088458556185882997)
                    ·
                      refine ⟨4217504164542989642426531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44986711088458556185882997 4217504164542989642426531)
                      ·
                        rfl

theorem cell23_8213560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_8213560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213560 prefixEnd_8213560 := by exact prefixLift 8213560
  have htrace : WordTrace (prefixWord ++ tailWord_8213560) baseStart_8213560 baseEnd_8213560 := by
    simpa [prefixWord, tailWord_8213560, baseEnd_8213560] using wordTrace_append hprefix tailTrace_8213560
  have hstable : (prefixWord ++ tailWord_8213560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213560).length < 2 ^ (prefixWord ++ tailWord_8213560).sum := by decide
  have hdescent : baseEnd_8213560 < baseStart_8213560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213593 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_8213593 : Nat := 118140960795 + 8213593 * 2 ^ 59
def prefixEnd_8213593 : Nat := 4983230072969 + 3 ^ 40 * 8213593 * 2
def baseEnd_8213593 : Nat := 1405840369801529337771293

theorem tailTrace_8213593 : CollatzResearch.WordTrace tailWord_8213593 prefixEnd_8213593 1405840369801529337771293 := by
  unfold tailWord_8213593
  simp only [CollatzResearch.WordTrace]
  refine ⟨299574347732562805849285433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199716231821708537232856955 299574347732562805849285433)
  ·
    refine ⟨224680760799422104386964075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299574347732562805849285433 224680760799422104386964075)
    ·
      refine ⟨337021141199133156580446113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224680760799422104386964075 337021141199133156580446113)
      ·
        refine ⟨252765855899349867435334585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337021141199133156580446113 252765855899349867435334585)
        ·
          refine ⟨189574391924512400576500939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252765855899349867435334585 189574391924512400576500939)
          ·
            refine ⟨284361587886768600864751409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189574391924512400576500939 284361587886768600864751409)
            ·
              refine ⟨213271190915076450648563557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284361587886768600864751409 213271190915076450648563557)
              ·
                refine ⟨39988348296576834496605667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213271190915076450648563557 39988348296576834496605667)
                ·
                  refine ⟨59982522444865251744908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39988348296576834496605667 59982522444865251744908501)
                  ·
                    refine ⟨1405840369801529337771293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59982522444865251744908501 1405840369801529337771293)
                    ·
                      rfl

theorem cell23_8213593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_8213593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213593 prefixEnd_8213593 := by exact prefixLift 8213593
  have htrace : WordTrace (prefixWord ++ tailWord_8213593) baseStart_8213593 baseEnd_8213593 := by
    simpa [prefixWord, tailWord_8213593, baseEnd_8213593] using wordTrace_append hprefix tailTrace_8213593
  have hstable : (prefixWord ++ tailWord_8213593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213593).length < 2 ^ (prefixWord ++ tailWord_8213593).sum := by decide
  have hdescent : baseEnd_8213593 < baseStart_8213593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213603 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8213603 : Nat := 118140960795 + 8213603 * 2 ^ 59
def prefixEnd_8213603 : Nat := 4983230072969 + 3 ^ 40 * 8213603 * 2
def baseEnd_8213603 : Nat := 4217526244211132974188833

theorem tailTrace_8213603 : CollatzResearch.WordTrace tailWord_8213603 prefixEnd_8213603 4217526244211132974188833 := by
  unfold tailWord_8213603
  simp only [CollatzResearch.WordTrace]
  refine ⟨299574712462526577557149463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199716474975017718371432975 299574712462526577557149463)
  ·
    refine ⟨449362068693789866335724195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299574712462526577557149463 449362068693789866335724195)
    ·
      refine ⟨674043103040684799503586293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449362068693789866335724195 674043103040684799503586293)
      ·
        refine ⟨63191540910064199953461215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 674043103040684799503586293 63191540910064199953461215)
        ·
          refine ⟨94787311365096299930191823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63191540910064199953461215 94787311365096299930191823)
          ·
            refine ⟨142180967047644449895287735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94787311365096299930191823 142180967047644449895287735)
            ·
              refine ⟨213271450571466674842931603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142180967047644449895287735 213271450571466674842931603)
              ·
                refine ⟨319907175857200012264397405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213271450571466674842931603 319907175857200012264397405)
                ·
                  refine ⟨119965190946450004599149027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319907175857200012264397405 119965190946450004599149027)
                  ·
                    refine ⟨179947786419675006898723541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119965190946450004599149027 179947786419675006898723541)
                    ·
                      refine ⟨4217526244211132974188833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179947786419675006898723541 4217526244211132974188833)
                      ·
                        rfl

theorem cell23_8213603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8213603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213603 prefixEnd_8213603 := by exact prefixLift 8213603
  have htrace : WordTrace (prefixWord ++ tailWord_8213603) baseStart_8213603 baseEnd_8213603 := by
    simpa [prefixWord, tailWord_8213603, baseEnd_8213603] using wordTrace_append hprefix tailTrace_8213603
  have hstable : (prefixWord ++ tailWord_8213603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213603).length < 2 ^ (prefixWord ++ tailWord_8213603).sum := by decide
  have hdescent : baseEnd_8213603 < baseStart_8213603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213707 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 6, 3, 2]
def baseStart_8213707 : Nat := 118140960795 + 8213707 * 2 ^ 59
def prefixEnd_8213707 : Nat := 4983230072969 + 3 ^ 40 * 8213707 * 2
def baseEnd_8213707 : Nat := 4217579646199200567288355

theorem tailTrace_8213707 : CollatzResearch.WordTrace tailWord_8213707 prefixEnd_8213707 4217579646199200567288355 := by
  unfold tailWord_8213707
  simp only [CollatzResearch.WordTrace]
  refine ⟨299578505654149803318935375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199719003769433202212623583 299578505654149803318935375)
  ·
    refine ⟨449367758481224704978403063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299578505654149803318935375 449367758481224704978403063)
    ·
      refine ⟨674051637721837057467604595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449367758481224704978403063 674051637721837057467604595)
      ·
        refine ⟨1011077456582755586201406893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674051637721837057467604595 1011077456582755586201406893)
        ·
          refine ⟨379154046218533344825527585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011077456582755586201406893 379154046218533344825527585)
          ·
            refine ⟨284365534663900008619145689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379154046218533344825527585 284365534663900008619145689)
            ·
              refine ⟨213274150997925006464359267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284365534663900008619145689 213274150997925006464359267)
              ·
                refine ⟨319911226496887509696538901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213274150997925006464359267 319911226496887509696538901)
                ·
                  refine ⟨14995838742041602017025261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319911226496887509696538901 14995838742041602017025261)
                  ·
                    refine ⟨5623439528265600756384473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14995838742041602017025261 5623439528265600756384473)
                    ·
                      refine ⟨4217579646199200567288355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623439528265600756384473 4217579646199200567288355)
                      ·
                        rfl

theorem cell23_8213707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3, 2].length) (baseStart_8213707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213707 prefixEnd_8213707 := by exact prefixLift 8213707
  have htrace : WordTrace (prefixWord ++ tailWord_8213707) baseStart_8213707 baseEnd_8213707 := by
    simpa [prefixWord, tailWord_8213707, baseEnd_8213707] using wordTrace_append hprefix tailTrace_8213707
  have hstable : (prefixWord ++ tailWord_8213707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213707).length < 2 ^ (prefixWord ++ tailWord_8213707).sum := by decide
  have hdescent : baseEnd_8213707 < baseStart_8213707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213714 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_8213714 : Nat := 118140960795 + 8213714 * 2 ^ 59
def prefixEnd_8213714 : Nat := 4983230072969 + 3 ^ 40 * 8213714 * 2
def baseEnd_8213714 : Nat := 4217583240563782039900823

theorem tailTrace_8213714 : CollatzResearch.WordTrace tailWord_8213714 prefixEnd_8213714 4217583240563782039900823 := by
  unfold tailWord_8213714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74894690241281110878610049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199719173976749629009626797 74894690241281110878610049)
  ·
    refine ⟨56171017680960833158957537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74894690241281110878610049 56171017680960833158957537)
    ·
      refine ⟨42128263260720624869218153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56171017680960833158957537 42128263260720624869218153)
      ·
        refine ⟨31596197445540468651913615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42128263260720624869218153 31596197445540468651913615)
        ·
          refine ⟨47394296168310702977870423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31596197445540468651913615 47394296168310702977870423)
          ·
            refine ⟨71091444252466054466805635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47394296168310702977870423 71091444252466054466805635)
            ·
              refine ⟨106637166378699081700208453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71091444252466054466805635 106637166378699081700208453)
              ·
                refine ⟨19994468696006077818789085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106637166378699081700208453 19994468696006077818789085)
                ·
                  refine ⟨7497925761002279182045907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19994468696006077818789085 7497925761002279182045907)
                  ·
                    refine ⟨11246888641503418773068861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7497925761002279182045907 11246888641503418773068861)
                    ·
                      refine ⟨4217583240563782039900823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246888641503418773068861 4217583240563782039900823)
                      ·
                        rfl

theorem cell23_8213714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_8213714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213714 prefixEnd_8213714 := by exact prefixLift 8213714
  have htrace : WordTrace (prefixWord ++ tailWord_8213714) baseStart_8213714 baseEnd_8213714 := by
    simpa [prefixWord, tailWord_8213714, baseEnd_8213714] using wordTrace_append hprefix tailTrace_8213714
  have hstable : (prefixWord ++ tailWord_8213714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213714).length < 2 ^ (prefixWord ++ tailWord_8213714).sum := by decide
  have hdescent : baseEnd_8213714 < baseStart_8213714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213725 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_8213725 : Nat := 118140960795 + 8213725 * 2 ^ 59
def prefixEnd_8213725 : Nat := 4983230072969 + 3 ^ 40 * 8213725 * 2
def baseEnd_8213725 : Nat := 1405862962950327165621091

theorem tailTrace_8213725 : CollatzResearch.WordTrace tailWord_8213725 prefixEnd_8213725 1405862962950327165621091 := by
  unfold tailWord_8213725
  simp only [CollatzResearch.WordTrace]
  refine ⟨299579162168084592393090629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199719441445389728262060419 299579162168084592393090629)
  ·
    refine ⟨56171092906515861073704493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299579162168084592393090629 56171092906515861073704493)
    ·
      refine ⟨21064159839943447902639185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56171092906515861073704493 21064159839943447902639185)
      ·
        refine ⟨15798119879957585926979389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21064159839943447902639185 15798119879957585926979389)
        ·
          refine ⟨5924294954984094722617271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15798119879957585926979389 5924294954984094722617271)
          ·
            refine ⟨8886442432476142083925907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924294954984094722617271 8886442432476142083925907)
            ·
              refine ⟨13329663648714213125888861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886442432476142083925907 13329663648714213125888861)
              ·
                refine ⟨4998623868267829922208323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13329663648714213125888861 4998623868267829922208323)
                ·
                  refine ⟨7497935802401744883312485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998623868267829922208323 7497935802401744883312485)
                  ·
                    refine ⟨1405862962950327165621091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497935802401744883312485 1405862962950327165621091)
                    ·
                      rfl

theorem cell23_8213725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_8213725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213725 prefixEnd_8213725 := by exact prefixLift 8213725
  have htrace : WordTrace (prefixWord ++ tailWord_8213725) baseStart_8213725 baseEnd_8213725 := by
    simpa [prefixWord, tailWord_8213725, baseEnd_8213725] using wordTrace_append hprefix tailTrace_8213725
  have hstable : (prefixWord ++ tailWord_8213725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213725).length < 2 ^ (prefixWord ++ tailWord_8213725).sum := by decide
  have hdescent : baseEnd_8213725 < baseStart_8213725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213741 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_8213741 : Nat := 118140960795 + 8213741 * 2 ^ 59
def prefixEnd_8213741 : Nat := 4983230072969 + 3 ^ 40 * 8213741 * 2
def baseEnd_8213741 : Nat := 4217597104541453434263199

theorem tailTrace_8213741 : CollatzResearch.WordTrace tailWord_8213741 prefixEnd_8213741 4217597104541453434263199 := by
  unfold tailWord_8213741
  simp only [CollatzResearch.WordTrace]
  refine ⟨299579745736026627125673077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199719830490684418083782051 299579745736026627125673077)
  ·
    refine ⟨28085601162752496293031851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299579745736026627125673077 28085601162752496293031851)
    ·
      refine ⟨42128401744128744439547777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28085601162752496293031851 42128401744128744439547777)
      ·
        refine ⟨31596301308096558329660833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42128401744128744439547777 31596301308096558329660833)
        ·
          refine ⟨23697225981072418747245625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31596301308096558329660833 23697225981072418747245625)
          ·
            refine ⟨17772919485804314060434219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23697225981072418747245625 17772919485804314060434219)
            ·
              refine ⟨26659379228706471090651329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17772919485804314060434219 26659379228706471090651329)
              ·
                refine ⟨19994534421529853317988497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26659379228706471090651329 19994534421529853317988497)
                ·
                  refine ⟨14995900816147389988491373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19994534421529853317988497 14995900816147389988491373)
                  ·
                    refine ⟨5623462806055271245684265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14995900816147389988491373 5623462806055271245684265)
                    ·
                      refine ⟨4217597104541453434263199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623462806055271245684265 4217597104541453434263199)
                      ·
                        rfl

theorem cell23_8213741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_8213741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213741 prefixEnd_8213741 := by exact prefixLift 8213741
  have htrace : WordTrace (prefixWord ++ tailWord_8213741) baseStart_8213741 baseEnd_8213741 := by
    simpa [prefixWord, tailWord_8213741, baseEnd_8213741] using wordTrace_append hprefix tailTrace_8213741
  have hstable : (prefixWord ++ tailWord_8213741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213741).length < 2 ^ (prefixWord ++ tailWord_8213741).sum := by decide
  have hdescent : baseEnd_8213741 < baseStart_8213741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213747 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 4, 4]
def baseStart_8213747 : Nat := 118140960795 + 8213747 * 2 ^ 59
def prefixEnd_8213747 : Nat := 4983230072969 + 3 ^ 40 * 8213747 * 2
def baseEnd_8213747 : Nat := 1405866728475126803596057

theorem tailTrace_8213747 : CollatzResearch.WordTrace tailWord_8213747 prefixEnd_8213747 1405866728475126803596057 := by
  unfold tailWord_8213747
  simp only [CollatzResearch.WordTrace]
  refine ⟨299579964574004890150391495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199719976382669926766927663 299579964574004890150391495)
  ·
    refine ⟨449369946861007335225587243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299579964574004890150391495 449369946861007335225587243)
    ·
      refine ⟨674054920291511002838380865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449369946861007335225587243 674054920291511002838380865)
      ·
        refine ⟨505541190218633252128785649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674054920291511002838380865 505541190218633252128785649)
        ·
          refine ⟨379155892663974939096589237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505541190218633252128785649 379155892663974939096589237)
          ·
            refine ⟨35545864937247650540305241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379155892663974939096589237 35545864937247650540305241)
            ·
              refine ⟨26659398702935737905228931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35545864937247650540305241 26659398702935737905228931)
              ·
                refine ⟨39989098054403606857843397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26659398702935737905228931 39989098054403606857843397)
                ·
                  refine ⟨7497955885200676285845637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39989098054403606857843397 7497955885200676285845637)
                  ·
                    refine ⟨1405866728475126803596057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497955885200676285845637 1405866728475126803596057)
                    ·
                      rfl

theorem cell23_8213747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 4].length) (baseStart_8213747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213747 prefixEnd_8213747 := by exact prefixLift 8213747
  have htrace : WordTrace (prefixWord ++ tailWord_8213747) baseStart_8213747 baseEnd_8213747 := by
    simpa [prefixWord, tailWord_8213747, baseEnd_8213747] using wordTrace_append hprefix tailTrace_8213747
  have hstable : (prefixWord ++ tailWord_8213747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213747).length < 2 ^ (prefixWord ++ tailWord_8213747).sum := by decide
  have hdescent : baseEnd_8213747 < baseStart_8213747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213774 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_8213774 : Nat := 118140960795 + 8213774 * 2 ^ 59
def prefixEnd_8213774 : Nat := 4983230072969 + 3 ^ 40 * 8213774 * 2
def baseEnd_8213774 : Nat := 4217614049403051805150547

theorem tailTrace_8213774 : CollatzResearch.WordTrace tailWord_8213774 prefixEnd_8213774 4217614049403051805150547 := by
  unfold tailWord_8213774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37447618668113384220203047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199720632896604715841082917 37447618668113384220203047)
  ·
    refine ⟨56171428002170076330304571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37447618668113384220203047 56171428002170076330304571)
    ·
      refine ⟨84257142003255114495456857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56171428002170076330304571 84257142003255114495456857)
      ·
        refine ⟨63192856502441335871592643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84257142003255114495456857 63192856502441335871592643)
        ·
          refine ⟨94789284753662003807388965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63192856502441335871592643 94789284753662003807388965)
          ·
            refine ⟨17772990891311625713885431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94789284753662003807388965 17772990891311625713885431)
            ·
              refine ⟨26659486336967438570828147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17772990891311625713885431 26659486336967438570828147)
              ·
                refine ⟨39989229505451157856242221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26659486336967438570828147 39989229505451157856242221)
                ·
                  refine ⟨14995961064544184196090833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39989229505451157856242221 14995961064544184196090833)
                  ·
                    refine ⟨11246970798408138147068125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14995961064544184196090833 11246970798408138147068125)
                    ·
                      refine ⟨4217614049403051805150547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11246970798408138147068125 4217614049403051805150547)
                      ·
                        rfl

theorem cell23_8213774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_8213774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213774 prefixEnd_8213774 := by exact prefixLift 8213774
  have htrace : WordTrace (prefixWord ++ tailWord_8213774) baseStart_8213774 baseEnd_8213774 := by
    simpa [prefixWord, tailWord_8213774, baseEnd_8213774] using wordTrace_append hprefix tailTrace_8213774
  have hstable : (prefixWord ++ tailWord_8213774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213774).length < 2 ^ (prefixWord ++ tailWord_8213774).sum := by decide
  have hdescent : baseEnd_8213774 < baseStart_8213774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213791 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 1, 5]
def baseStart_8213791 : Nat := 118140960795 + 8213791 * 2 ^ 59
def prefixEnd_8213791 : Nat := 4983230072969 + 3 ^ 40 * 8213791 * 2
def baseEnd_8213791 : Nat := 4217622778574178238637969

theorem tailTrace_8213791 : CollatzResearch.WordTrace tailWord_8213791 prefixEnd_8213791 4217622778574178238637969 := by
  unfold tailWord_8213791
  simp only [CollatzResearch.WordTrace]
  refine ⟨299581569385845485664993227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199721046257230323776662151 299581569385845485664993227)
  ·
    refine ⟨449372354078768228497489841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299581569385845485664993227 449372354078768228497489841)
    ·
      refine ⟨337029265559076171373117381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449372354078768228497489841 337029265559076171373117381)
      ·
        refine ⟨63192987292326782132459509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337029265559076171373117381 63192987292326782132459509)
        ·
          refine ⟨5924342558655635824918079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63192987292326782132459509 5924342558655635824918079)
          ·
            refine ⟨8886513837983453737377119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924342558655635824918079 8886513837983453737377119)
            ·
              refine ⟨13329770756975180606065679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886513837983453737377119 13329770756975180606065679)
              ·
                refine ⟨19994656135462770909098519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329770756975180606065679 19994656135462770909098519)
                ·
                  refine ⟨29991984203194156363647779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19994656135462770909098519 29991984203194156363647779)
                  ·
                    refine ⟨44987976304791234545471669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29991984203194156363647779 44987976304791234545471669)
                    ·
                      refine ⟨4217622778574178238637969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44987976304791234545471669 4217622778574178238637969)
                      ·
                        rfl

theorem cell23_8213791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_8213791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213791 prefixEnd_8213791 := by exact prefixLift 8213791
  have htrace : WordTrace (prefixWord ++ tailWord_8213791) baseStart_8213791 baseEnd_8213791 := by
    simpa [prefixWord, tailWord_8213791, baseEnd_8213791] using wordTrace_append hprefix tailTrace_8213791
  have hstable : (prefixWord ++ tailWord_8213791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213791).length < 2 ^ (prefixWord ++ tailWord_8213791).sum := by decide
  have hdescent : baseEnd_8213791 < baseStart_8213791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213861 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_8213861 : Nat := 118140960795 + 8213861 * 2 ^ 59
def prefixEnd_8213861 : Nat := 4983230072969 + 3 ^ 40 * 8213861 * 2
def baseEnd_8213861 : Nat := 4217658722219992964762647

theorem tailTrace_8213861 : CollatzResearch.WordTrace tailWord_8213861 prefixEnd_8213861 4217658722219992964762647 := by
  unfold tailWord_8213861
  simp only [CollatzResearch.WordTrace]
  refine ⟨299584122495591887620041437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199722748330394591746694291 299584122495591887620041437)
  ·
    refine ⟨112344045935846957857515539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299584122495591887620041437 112344045935846957857515539)
    ·
      refine ⟨168516068903770436786273309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112344045935846957857515539 168516068903770436786273309)
      ·
        refine ⟨63193525838913913794852491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168516068903770436786273309 63193525838913913794852491)
        ·
          refine ⟨94790288758370870692278737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63193525838913913794852491 94790288758370870692278737)
          ·
            refine ⟨71092716568778153019209053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94790288758370870692278737 71092716568778153019209053)
            ·
              refine ⟨26659768713291807382203395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71092716568778153019209053 26659768713291807382203395)
              ·
                refine ⟨39989653069937711073305093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26659768713291807382203395 39989653069937711073305093)
                ·
                  refine ⟨7498059950613320826244705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39989653069937711073305093 7498059950613320826244705)
                  ·
                    refine ⟨5623544962959990619683529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7498059950613320826244705 5623544962959990619683529)
                    ·
                      refine ⟨4217658722219992964762647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623544962959990619683529 4217658722219992964762647)
                      ·
                        rfl

theorem cell23_8213861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_8213861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213861 prefixEnd_8213861 := by exact prefixLift 8213861
  have htrace : WordTrace (prefixWord ++ tailWord_8213861) baseStart_8213861 baseEnd_8213861 := by
    simpa [prefixWord, tailWord_8213861, baseEnd_8213861] using wordTrace_append hprefix tailTrace_8213861
  have hstable : (prefixWord ++ tailWord_8213861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213861).length < 2 ^ (prefixWord ++ tailWord_8213861).sum := by decide
  have hdescent : baseEnd_8213861 < baseStart_8213861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213914 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_8213914 : Nat := 118140960795 + 8213914 * 2 ^ 59
def prefixEnd_8213914 : Nat := 4983230072969 + 3 ^ 40 * 8213914 * 2
def baseEnd_8213914 : Nat := 1405895312231560419133301

theorem tailTrace_8213914 : CollatzResearch.WordTrace tailWord_8213914 prefixEnd_8213914 1405895312231560419133301 := by
  unfold tailWord_8213914
  simp only [CollatzResearch.WordTrace]
  refine ⟨74896513891099969417930199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199724037042933251781147197 74896513891099969417930199)
  ·
    refine ⟨112344770836649954126895299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74896513891099969417930199 112344770836649954126895299)
    ·
      refine ⟨168517156254974931190342949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112344770836649954126895299 168517156254974931190342949)
      ·
        refine ⟨31596966797807799598189303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168517156254974931190342949 31596966797807799598189303)
        ·
          refine ⟨47395450196711699397283955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31596966797807799598189303 47395450196711699397283955)
          ·
            refine ⟨71093175295067549095925933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47395450196711699397283955 71093175295067549095925933)
            ·
              refine ⟨26659940735650330910972225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71093175295067549095925933 26659940735650330910972225)
              ·
                refine ⟨19994955551737748183229169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26659940735650330910972225 19994955551737748183229169)
                ·
                  refine ⟨14996216663803311137421877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19994955551737748183229169 14996216663803311137421877)
                  ·
                    refine ⟨1405895312231560419133301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14996216663803311137421877 1405895312231560419133301)
                    ·
                      rfl

theorem cell23_8213914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_8213914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213914 prefixEnd_8213914 := by exact prefixLift 8213914
  have htrace : WordTrace (prefixWord ++ tailWord_8213914) baseStart_8213914 baseEnd_8213914 := by
    simpa [prefixWord, tailWord_8213914, baseEnd_8213914] using wordTrace_append hprefix tailTrace_8213914
  have hstable : (prefixWord ++ tailWord_8213914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213914).length < 2 ^ (prefixWord ++ tailWord_8213914).sum := by decide
  have hdescent : baseEnd_8213914 < baseStart_8213914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213918 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_8213918 : Nat := 118140960795 + 8213918 * 2 ^ 59
def prefixEnd_8213918 : Nat := 4983230072969 + 3 ^ 40 * 8213918 * 2
def baseEnd_8213918 : Nat := 468631998957477693527765

theorem tailTrace_8213918 : CollatzResearch.WordTrace tailWord_8213918 prefixEnd_8213918 468631998957477693527765 := by
  unfold tailWord_8213918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448275182048173294358301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199724134304256924236577605 37448275182048173294358301)
  ·
    refine ⟨14043103193268064985384363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37448275182048173294358301 14043103193268064985384363)
    ·
      refine ⟨21064654789902097478076545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043103193268064985384363 21064654789902097478076545)
      ·
        refine ⟨15798491092426573108557409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21064654789902097478076545 15798491092426573108557409)
        ·
          refine ⟨11848868319319929831418057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15798491092426573108557409 11848868319319929831418057)
          ·
            refine ⟨8886651239489947373563543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11848868319319929831418057 8886651239489947373563543)
            ·
              refine ⟨13329976859234921060345315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886651239489947373563543 13329976859234921060345315)
              ·
                refine ⟨19994965288852381590517973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329976859234921060345315 19994965288852381590517973)
                ·
                  refine ⟨468631998957477693527765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19994965288852381590517973 468631998957477693527765)
                  ·
                    rfl

theorem cell23_8213918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_8213918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213918 prefixEnd_8213918 := by exact prefixLift 8213918
  have htrace : WordTrace (prefixWord ++ tailWord_8213918) baseStart_8213918 baseEnd_8213918 := by
    simpa [prefixWord, tailWord_8213918, baseEnd_8213918] using wordTrace_append hprefix tailTrace_8213918
  have hstable : (prefixWord ++ tailWord_8213918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213918).length < 2 ^ (prefixWord ++ tailWord_8213918).sum := by decide
  have hdescent : baseEnd_8213918 < baseStart_8213918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213944 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_8213944 : Nat := 118140960795 + 8213944 * 2 ^ 59
def prefixEnd_8213944 : Nat := 4983230072969 + 3 ^ 40 * 8213944 * 2
def baseEnd_8213944 : Nat := 1405900447038105380008255

theorem tailTrace_8213944 : CollatzResearch.WordTrace tailWord_8213944 prefixEnd_8213944 1405900447038105380008255 := by
  unfold tailWord_8213944
  simp only [CollatzResearch.WordTrace]
  refine ⟨149793574877145596397656443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199724766502860795196875257 149793574877145596397656443)
  ·
    refine ⟨224690362315718394596484665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149793574877145596397656443 224690362315718394596484665)
    ·
      refine ⟨168517771736788795947363499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224690362315718394596484665 168517771736788795947363499)
      ·
        refine ⟨252776657605183193921045249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168517771736788795947363499 252776657605183193921045249)
        ·
          refine ⟨189582493203887395440783937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252776657605183193921045249 189582493203887395440783937)
          ·
            refine ⟨142186869902915546580587953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189582493203887395440783937 142186869902915546580587953)
            ·
              refine ⟨106640152427186659935440965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142186869902915546580587953 106640152427186659935440965)
              ·
                refine ⟨19995028580097498737895181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106640152427186659935440965 19995028580097498737895181)
                ·
                  refine ⟨7498135717536562026710693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19995028580097498737895181 7498135717536562026710693)
                  ·
                    refine ⟨1405900447038105380008255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498135717536562026710693 1405900447038105380008255)
                    ·
                      rfl

theorem cell23_8213944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_8213944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213944 prefixEnd_8213944 := by exact prefixLift 8213944
  have htrace : WordTrace (prefixWord ++ tailWord_8213944) baseStart_8213944 baseEnd_8213944 := by
    simpa [prefixWord, tailWord_8213944, baseEnd_8213944] using wordTrace_append hprefix tailTrace_8213944
  have hstable : (prefixWord ++ tailWord_8213944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213944).length < 2 ^ (prefixWord ++ tailWord_8213944).sum := by decide
  have hdescent : baseEnd_8213944 < baseStart_8213944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213961 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 1, 4]
def baseStart_8213961 : Nat := 118140960795 + 8213961 * 2 ^ 59
def prefixEnd_8213961 : Nat := 4983230072969 + 3 ^ 40 * 8213961 * 2
def baseEnd_8213961 : Nat := 1405903356761814191170729

theorem tailTrace_8213961 : CollatzResearch.WordTrace tailWord_8213961 prefixEnd_8213961 1405903356761814191170729 := by
  unfold tailWord_8213961
  simp only [CollatzResearch.WordTrace]
  refine ⟨299587769795229604698681737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199725179863486403132454491 299587769795229604698681737)
  ·
    refine ⟨224690827346422203524011303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299587769795229604698681737 224690827346422203524011303)
    ·
      refine ⟨337036241019633305286016955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224690827346422203524011303 337036241019633305286016955)
      ·
        refine ⟨505554361529449957929025433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337036241019633305286016955 505554361529449957929025433)
        ·
          refine ⟨379165771147087468446769075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505554361529449957929025433 379165771147087468446769075)
          ·
            refine ⟨568748656720631202670153613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379165771147087468446769075 568748656720631202670153613)
            ·
              refine ⟨213280746270236701001307605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568748656720631202670153613 213280746270236701001307605)
              ·
                refine ⟨4998767490708672679718147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213280746270236701001307605 4998767490708672679718147)
                ·
                  refine ⟨7498151236063009019577221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998767490708672679718147 7498151236063009019577221)
                  ·
                    refine ⟨1405903356761814191170729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498151236063009019577221 1405903356761814191170729)
                    ·
                      rfl

theorem cell23_8213961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_8213961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213961 prefixEnd_8213961 := by exact prefixLift 8213961
  have htrace : WordTrace (prefixWord ++ tailWord_8213961) baseStart_8213961 baseEnd_8213961 := by
    simpa [prefixWord, tailWord_8213961, baseEnd_8213961] using wordTrace_append hprefix tailTrace_8213961
  have hstable : (prefixWord ++ tailWord_8213961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213961).length < 2 ^ (prefixWord ++ tailWord_8213961).sum := by decide
  have hdescent : baseEnd_8213961 < baseStart_8213961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8213978 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_8213978 : Nat := 118140960795 + 8213978 * 2 ^ 59
def prefixEnd_8213978 : Nat := 4983230072969 + 3 ^ 40 * 8213978 * 2
def baseEnd_8213978 : Nat := 1405906266485523002333203

theorem tailTrace_8213978 : CollatzResearch.WordTrace tailWord_8213978 prefixEnd_8213978 1405906266485523002333203 := by
  unfold tailWord_8213978
  simp only [CollatzResearch.WordTrace]
  refine ⟨74897097459042004150512647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199725593224112011068033725 74897097459042004150512647)
  ·
    refine ⟨112345646188563006225768971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74897097459042004150512647 112345646188563006225768971)
    ·
      refine ⟨168518469282844509338653457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112345646188563006225768971 168518469282844509338653457)
      ·
        refine ⟨126388851962133382003990093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168518469282844509338653457 126388851962133382003990093)
        ·
          refine ⟨47395819485800018251496285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126388851962133382003990093 47395819485800018251496285)
          ·
            refine ⟨17773432307175006844311107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47395819485800018251496285 17773432307175006844311107)
            ·
              refine ⟨26660148460762510266466661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17773432307175006844311107 26660148460762510266466661)
              ·
                refine ⟨4998777836392970674962499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26660148460762510266466661 4998777836392970674962499)
                ·
                  refine ⟨7498166754589456012443749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998777836392970674962499 7498166754589456012443749)
                  ·
                    refine ⟨1405906266485523002333203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498166754589456012443749 1405906266485523002333203)
                    ·
                      rfl

theorem cell23_8213978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_8213978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8213978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8213978 prefixEnd_8213978 := by exact prefixLift 8213978
  have htrace : WordTrace (prefixWord ++ tailWord_8213978) baseStart_8213978 baseEnd_8213978 := by
    simpa [prefixWord, tailWord_8213978, baseEnd_8213978] using wordTrace_append hprefix tailTrace_8213978
  have hstable : (prefixWord ++ tailWord_8213978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8213978).length < 2 ^ (prefixWord ++ tailWord_8213978).sum := by decide
  have hdescent : baseEnd_8213978 < baseStart_8213978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8213978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214001 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_8214001 : Nat := 118140960795 + 8214001 * 2 ^ 59
def prefixEnd_8214001 : Nat := 4983230072969 + 3 ^ 40 * 8214001 * 2
def baseEnd_8214001 : Nat := 4217730609511622417012003

theorem tailTrace_8214001 : CollatzResearch.WordTrace tailWord_8214001 prefixEnd_8214001 4217730609511622417012003 := by
  unfold tailWord_8214001
  simp only [CollatzResearch.WordTrace]
  refine ⟨299589228715084691530137857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199726152476723127686758571 299589228715084691530137857)
  ·
    refine ⟨224691921536313518647603393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299589228715084691530137857 224691921536313518647603393)
    ·
      refine ⟨168518941152235138985702545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224691921536313518647603393 168518941152235138985702545)
      ·
        refine ⟨126389205864176354239276909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168518941152235138985702545 126389205864176354239276909)
        ·
          refine ⟨47395952199066132839728841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126389205864176354239276909 47395952199066132839728841)
          ·
            refine ⟨35546964149299599629796631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47395952199066132839728841 35546964149299599629796631)
            ·
              refine ⟨53320446223949399444694947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35546964149299599629796631 53320446223949399444694947)
              ·
                refine ⟨79980669335924099167042421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53320446223949399444694947 79980669335924099167042421)
                ·
                  refine ⟨7498187750242884296910227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79980669335924099167042421 7498187750242884296910227)
                  ·
                    refine ⟨11247281625364326445365341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498187750242884296910227 11247281625364326445365341)
                    ·
                      refine ⟨4217730609511622417012003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11247281625364326445365341 4217730609511622417012003)
                      ·
                        rfl

theorem cell23_8214001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_8214001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214001 prefixEnd_8214001 := by exact prefixLift 8214001
  have htrace : WordTrace (prefixWord ++ tailWord_8214001) baseStart_8214001 baseEnd_8214001 := by
    simpa [prefixWord, tailWord_8214001, baseEnd_8214001] using wordTrace_append hprefix tailTrace_8214001
  have hstable : (prefixWord ++ tailWord_8214001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214001).length < 2 ^ (prefixWord ++ tailWord_8214001).sum := by decide
  have hdescent : baseEnd_8214001 < baseStart_8214001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214005 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_8214005 : Nat := 118140960795 + 8214005 * 2 ^ 59
def prefixEnd_8214005 : Nat := 4983230072969 + 3 ^ 40 * 8214005 * 2
def baseEnd_8214005 : Nat := 4217732663434240401361985

theorem tailTrace_8214005 : CollatzResearch.WordTrace tailWord_8214005 prefixEnd_8214005 4217732663434240401361985 := by
  unfold tailWord_8214005
  simp only [CollatzResearch.WordTrace]
  refine ⟨299589374607070200213283469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199726249738046800142188979 299589374607070200213283469)
  ·
    refine ⟨112346015477651325079981301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299589374607070200213283469 112346015477651325079981301)
    ·
      refine ⟨10532438951029811726248247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112346015477651325079981301 10532438951029811726248247)
      ·
        refine ⟨15798658426544717589372371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10532438951029811726248247 15798658426544717589372371)
        ·
          refine ⟨23697987639817076384058557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15798658426544717589372371 23697987639817076384058557)
          ·
            refine ⟨8886745364931403644021959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23697987639817076384058557 8886745364931403644021959)
            ·
              refine ⟨13330118047397105466032939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886745364931403644021959 13330118047397105466032939)
              ·
                refine ⟨19995177071095658199049409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13330118047397105466032939 19995177071095658199049409)
                ·
                  refine ⟨14996382803321743649287057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19995177071095658199049409 14996382803321743649287057)
                  ·
                    refine ⟨11247287102491307736965293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14996382803321743649287057 11247287102491307736965293)
                    ·
                      refine ⟨4217732663434240401361985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11247287102491307736965293 4217732663434240401361985)
                      ·
                        rfl

theorem cell23_8214005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_8214005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214005 prefixEnd_8214005 := by exact prefixLift 8214005
  have htrace : WordTrace (prefixWord ++ tailWord_8214005) baseStart_8214005 baseEnd_8214005 := by
    simpa [prefixWord, tailWord_8214005, baseEnd_8214005] using wordTrace_append hprefix tailTrace_8214005
  have hstable : (prefixWord ++ tailWord_8214005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214005).length < 2 ^ (prefixWord ++ tailWord_8214005).sum := by decide
  have hdescent : baseEnd_8214005 < baseStart_8214005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214058 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_8214058 : Nat := 118140960795 + 8214058 * 2 ^ 59
def prefixEnd_8214058 : Nat := 4983230072969 + 3 ^ 40 * 8214058 * 2
def baseEnd_8214058 : Nat := 4217759877908928693999241

theorem tailTrace_8214058 : CollatzResearch.WordTrace tailWord_8214058 prefixEnd_8214058 4217759877908928693999241 := by
  unfold tailWord_8214058
  simp only [CollatzResearch.WordTrace]
  refine ⟨74897826918969547566240707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199727538450585460176641885 74897826918969547566240707)
  ·
    refine ⟨112346740378454321349361061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74897826918969547566240707 112346740378454321349361061)
    ·
      refine ⟨21065013820960185253005199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112346740378454321349361061 21065013820960185253005199)
      ·
        refine ⟨31597520731440277879507799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065013820960185253005199 31597520731440277879507799)
        ·
          refine ⟨47396281097160416819261699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31597520731440277879507799 47396281097160416819261699)
          ·
            refine ⟨71094421645740625228892549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47396281097160416819261699 71094421645740625228892549)
            ·
              refine ⟨13330204058576367230417353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71094421645740625228892549 13330204058576367230417353)
              ·
                refine ⟨9997653043932275422813015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13330204058576367230417353 9997653043932275422813015)
                ·
                  refine ⟨14996479565898413134219523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997653043932275422813015 14996479565898413134219523)
                  ·
                    refine ⟨22494719348847619701329285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14996479565898413134219523 22494719348847619701329285)
                    ·
                      refine ⟨4217759877908928693999241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22494719348847619701329285 4217759877908928693999241)
                      ·
                        rfl

theorem cell23_8214058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_8214058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214058 prefixEnd_8214058 := by exact prefixLift 8214058
  have htrace : WordTrace (prefixWord ++ tailWord_8214058) baseStart_8214058 baseEnd_8214058 := by
    simpa [prefixWord, tailWord_8214058, baseEnd_8214058] using wordTrace_append hprefix tailTrace_8214058
  have hstable : (prefixWord ++ tailWord_8214058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214058).length < 2 ^ (prefixWord ++ tailWord_8214058).sum := by decide
  have hdescent : baseEnd_8214058 < baseStart_8214058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214086 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_8214086 : Nat := 118140960795 + 8214086 * 2 ^ 59
def prefixEnd_8214086 : Nat := 4983230072969 + 3 ^ 40 * 8214086 * 2
def baseEnd_8214086 : Nat := 4217774255367254584449113

theorem tailTrace_8214086 : CollatzResearch.WordTrace tailWord_8214086 prefixEnd_8214086 4217774255367254584449113 := by
  unfold tailWord_8214086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362260278743023470218191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199728219279851167364654741 9362260278743023470218191)
  ·
    refine ⟨14043390418114535205327287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362260278743023470218191 14043390418114535205327287)
    ·
      refine ⟨21065085627171802807990931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043390418114535205327287 21065085627171802807990931)
      ·
        refine ⟨31597628440757704211986397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065085627171802807990931 31597628440757704211986397)
        ·
          refine ⟨11849110665284139079494899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31597628440757704211986397 11849110665284139079494899)
          ·
            refine ⟨17773665997926208619242349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849110665284139079494899 17773665997926208619242349)
            ·
              refine ⟨6665124749222328232215881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17773665997926208619242349 6665124749222328232215881)
              ·
                refine ⟨4998843561916746174161911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665124749222328232215881 4998843561916746174161911)
                ·
                  refine ⟨7498265342875119261242867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4998843561916746174161911 7498265342875119261242867)
                  ·
                    refine ⟨11247398014312678891864301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498265342875119261242867 11247398014312678891864301)
                    ·
                      refine ⟨4217774255367254584449113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11247398014312678891864301 4217774255367254584449113)
                      ·
                        rfl

theorem cell23_8214086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_8214086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214086 prefixEnd_8214086 := by exact prefixLift 8214086
  have htrace : WordTrace (prefixWord ++ tailWord_8214086) baseStart_8214086 baseEnd_8214086 := by
    simpa [prefixWord, tailWord_8214086, baseEnd_8214086] using wordTrace_append hprefix tailTrace_8214086
  have hstable : (prefixWord ++ tailWord_8214086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214086).length < 2 ^ (prefixWord ++ tailWord_8214086).sum := by decide
  have hdescent : baseEnd_8214086 < baseStart_8214086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214094 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_8214094 : Nat := 118140960795 + 8214094 * 2 ^ 59
def prefixEnd_8214094 : Nat := 4983230072969 + 3 ^ 40 * 8214094 * 2
def baseEnd_8214094 : Nat := 1405926121070830184383025

theorem tailTrace_8214094 : CollatzResearch.WordTrace tailWord_8214094 prefixEnd_8214094 1405926121070830184383025 := by
  unfold tailWord_8214094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449077587968471051659167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199728413802498512275515557 37449077587968471051659167)
  ·
    refine ⟨56173616381952706577488751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37449077587968471051659167 56173616381952706577488751)
    ·
      refine ⟨84260424572929059866233127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56173616381952706577488751 84260424572929059866233127)
      ·
        refine ⟨126390636859393589799349691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84260424572929059866233127 126390636859393589799349691)
        ·
          refine ⟨189585955289090384699024537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126390636859393589799349691 189585955289090384699024537)
          ·
            refine ⟨142189466466817788524268403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189585955289090384699024537 142189466466817788524268403)
            ·
              refine ⟨213284199700226682786402605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142189466466817788524268403 213284199700226682786402605)
              ·
                refine ⟨79981574887585006044900977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213284199700226682786402605 79981574887585006044900977)
                ·
                  refine ⟨59986181165688754533675733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79981574887585006044900977 59986181165688754533675733)
                  ·
                    refine ⟨1405926121070830184383025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59986181165688754533675733 1405926121070830184383025)
                    ·
                      rfl

theorem cell23_8214094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_8214094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214094 prefixEnd_8214094 := by exact prefixLift 8214094
  have htrace : WordTrace (prefixWord ++ tailWord_8214094) baseStart_8214094 baseEnd_8214094 := by
    simpa [prefixWord, tailWord_8214094, baseEnd_8214094] using wordTrace_append hprefix tailTrace_8214094
  have hstable : (prefixWord ++ tailWord_8214094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214094).length < 2 ^ (prefixWord ++ tailWord_8214094).sum := by decide
  have hdescent : baseEnd_8214094 < baseStart_8214094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214101 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_8214101 : Nat := 118140960795 + 8214101 * 2 ^ 59
def prefixEnd_8214101 : Nat := 4983230072969 + 3 ^ 40 * 8214101 * 2
def baseEnd_8214101 : Nat := 4217781957577072025761543

theorem tailTrace_8214101 : CollatzResearch.WordTrace tailWord_8214101 prefixEnd_8214101 4217781957577072025761543 := by
  unfold tailWord_8214101
  simp only [CollatzResearch.WordTrace]
  refine ⟨299592876014722408608778157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199728584009814939072518771 299592876014722408608778157)
  ·
    refine ⟨112347328505520903228291809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299592876014722408608778157 112347328505520903228291809)
    ·
      refine ⟨84260496379140677421218857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112347328505520903228291809 84260496379140677421218857)
      ·
        refine ⟨63195372284355508065914143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84260496379140677421218857 63195372284355508065914143)
        ·
          refine ⟨94793058426533262098871215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63195372284355508065914143 94793058426533262098871215)
          ·
            refine ⟨142189587639799893148306823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94793058426533262098871215 142189587639799893148306823)
            ·
              refine ⟨213284381459699839722460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142189587639799893148306823 213284381459699839722460235)
              ·
                refine ⟨319926572189549759583690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213284381459699839722460235 319926572189549759583690353)
                ·
                  refine ⟨239944929142162319687767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319926572189549759583690353 239944929142162319687767765)
                  ·
                    refine ⟨5623709276769429367682057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239944929142162319687767765 5623709276769429367682057)
                    ·
                      refine ⟨4217781957577072025761543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623709276769429367682057 4217781957577072025761543)
                      ·
                        rfl

theorem cell23_8214101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_8214101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214101 prefixEnd_8214101 := by exact prefixLift 8214101
  have htrace : WordTrace (prefixWord ++ tailWord_8214101) baseStart_8214101 baseEnd_8214101 := by
    simpa [prefixWord, tailWord_8214101, baseEnd_8214101] using wordTrace_append hprefix tailTrace_8214101
  have hstable : (prefixWord ++ tailWord_8214101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214101).length < 2 ^ (prefixWord ++ tailWord_8214101).sum := by decide
  have hdescent : baseEnd_8214101 < baseStart_8214101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214109 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8214109 : Nat := 118140960795 + 8214109 * 2 ^ 59
def prefixEnd_8214109 : Nat := 4983230072969 + 3 ^ 40 * 8214109 * 2
def baseEnd_8214109 : Nat := 4217786065422307994461507

theorem tailTrace_8214109 : CollatzResearch.WordTrace tailWord_8214109 prefixEnd_8214109 4217786065422307994461507 := by
  unfold tailWord_8214109
  simp only [CollatzResearch.WordTrace]
  refine ⟨299593167798693425975069381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199728778532462283983379587 299593167798693425975069381)
  ·
    refine ⟨56173718962255017370325509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299593167798693425975069381 56173718962255017370325509)
    ·
      refine ⟨10532572305422815756936033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56173718962255017370325509 10532572305422815756936033)
      ·
        refine ⟨7899429229067111817702025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10532572305422815756936033 7899429229067111817702025)
        ·
          refine ⟨5924571921800333863276519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899429229067111817702025 5924571921800333863276519)
          ·
            refine ⟨8886857882700500794914779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924571921800333863276519 8886857882700500794914779)
            ·
              refine ⟨13330286824050751192372169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8886857882700500794914779 13330286824050751192372169)
              ·
                refine ⟨9997715118038063394279127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13330286824050751192372169 9997715118038063394279127)
                ·
                  refine ⟨14996572677057095091418691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997715118038063394279127 14996572677057095091418691)
                  ·
                    refine ⟨22494859015585642637128037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14996572677057095091418691 22494859015585642637128037)
                    ·
                      refine ⟨4217786065422307994461507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22494859015585642637128037 4217786065422307994461507)
                      ·
                        rfl

theorem cell23_8214109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8214109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214109 prefixEnd_8214109 := by exact prefixLift 8214109
  have htrace : WordTrace (prefixWord ++ tailWord_8214109) baseStart_8214109 baseEnd_8214109 := by
    simpa [prefixWord, tailWord_8214109, baseEnd_8214109] using wordTrace_append hprefix tailTrace_8214109
  have hstable : (prefixWord ++ tailWord_8214109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214109).length < 2 ^ (prefixWord ++ tailWord_8214109).sum := by decide
  have hdescent : baseEnd_8214109 < baseStart_8214109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214124 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_8214124 : Nat := 118140960795 + 8214124 * 2 ^ 59
def prefixEnd_8214124 : Nat := 4983230072969 + 3 ^ 40 * 8214124 * 2
def baseEnd_8214124 : Nat := 1405931255877375145257979

theorem tailTrace_8214124 : CollatzResearch.WordTrace tailWord_8214124 prefixEnd_8214124 1405931255877375145257979 := by
  unfold tailWord_8214124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149796857446819541768432713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199729143262426055691243617 149796857446819541768432713)
  ·
    refine ⟨112347643085114656326324535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149796857446819541768432713 112347643085114656326324535)
    ·
      refine ⟨168521464627671984489486803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112347643085114656326324535 168521464627671984489486803)
      ·
        refine ⟨252782196941507976734230205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168521464627671984489486803 252782196941507976734230205)
        ·
          refine ⟨94793323853065491275336327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252782196941507976734230205 94793323853065491275336327)
          ·
            refine ⟨142189985779598236913004491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94793323853065491275336327 142189985779598236913004491)
            ·
              refine ⟨213284978669397355369506737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142189985779598236913004491 213284978669397355369506737)
              ·
                refine ⟨159963734002048016527130053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213284978669397355369506737 159963734002048016527130053)
                ·
                  refine ⟨29993200125384003098836885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159963734002048016527130053 29993200125384003098836885)
                  ·
                    refine ⟨1405931255877375145257979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29993200125384003098836885 1405931255877375145257979)
                    ·
                      rfl

theorem cell23_8214124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_8214124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214124 prefixEnd_8214124 := by exact prefixLift 8214124
  have htrace : WordTrace (prefixWord ++ tailWord_8214124) baseStart_8214124 baseEnd_8214124 := by
    simpa [prefixWord, tailWord_8214124, baseEnd_8214124] using wordTrace_append hprefix tailTrace_8214124
  have hstable : (prefixWord ++ tailWord_8214124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214124).length < 2 ^ (prefixWord ++ tailWord_8214124).sum := by decide
  have hdescent : baseEnd_8214124 < baseStart_8214124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214151 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_8214151 : Nat := 118140960795 + 8214151 * 2 ^ 59
def prefixEnd_8214151 : Nat := 4983230072969 + 3 ^ 40 * 8214151 * 2
def baseEnd_8214151 : Nat := 4217807631609796830136313

theorem tailTrace_8214151 : CollatzResearch.WordTrace tailWord_8214151 prefixEnd_8214151 4217807631609796830136313 := by
  unfold tailWord_8214151
  simp only [CollatzResearch.WordTrace]
  refine ⟨299594699664541267148098307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199729799776360844765398871 299594699664541267148098307)
  ·
    refine ⟨449392049496811900722147461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299594699664541267148098307 449392049496811900722147461)
    ·
      refine ⟨84261009280652231385402649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 449392049496811900722147461 84261009280652231385402649)
      ·
        refine ⟨63195756960489173539051987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84261009280652231385402649 63195756960489173539051987)
        ·
          refine ⟨94793635440733760308577981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63195756960489173539051987 94793635440733760308577981)
          ·
            refine ⟨35547613290275160115716743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94793635440733760308577981 35547613290275160115716743)
            ·
              refine ⟨53321419935412740173575115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35547613290275160115716743 53321419935412740173575115)
              ·
                refine ⟨79982129903119110260362673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53321419935412740173575115 79982129903119110260362673)
                ·
                  refine ⟨59986597427339332695272005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79982129903119110260362673 59986597427339332695272005)
                  ·
                    refine ⟨11247487017626124880363501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59986597427339332695272005 11247487017626124880363501)
                    ·
                      refine ⟨4217807631609796830136313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11247487017626124880363501 4217807631609796830136313)
                      ·
                        rfl

theorem cell23_8214151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_8214151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214151 prefixEnd_8214151 := by exact prefixLift 8214151
  have htrace : WordTrace (prefixWord ++ tailWord_8214151) baseStart_8214151 baseEnd_8214151 := by
    simpa [prefixWord, tailWord_8214151, baseEnd_8214151] using wordTrace_append hprefix tailTrace_8214151
  have hstable : (prefixWord ++ tailWord_8214151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214151).length < 2 ^ (prefixWord ++ tailWord_8214151).sum := by decide
  have hdescent : baseEnd_8214151 < baseStart_8214151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214201 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_8214201 : Nat := 118140960795 + 8214201 * 2 ^ 59
def prefixEnd_8214201 : Nat := 4983230072969 + 3 ^ 40 * 8214201 * 2
def baseEnd_8214201 : Nat := 1405944435214173878170361

theorem tailTrace_8214201 : CollatzResearch.WordTrace tailWord_8214201 prefixEnd_8214201 1405944435214173878170361 := by
  unfold tailWord_8214201
  simp only [CollatzResearch.WordTrace]
  refine ⟨299596523314360125687418457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199731015542906750458278971 299596523314360125687418457)
  ·
    refine ⟨224697392485770094265563843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299596523314360125687418457 224697392485770094265563843)
    ·
      refine ⟨337046088728655141398345765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224697392485770094265563843 337046088728655141398345765)
      ·
        refine ⟨63196141636622839012189831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337046088728655141398345765 63196141636622839012189831)
        ·
          refine ⟨94794212454934258518284747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63196141636622839012189831 94794212454934258518284747)
          ·
            refine ⟨142191318682401387777427121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94794212454934258518284747 142191318682401387777427121)
            ·
              refine ⟨106643489011801040833070341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142191318682401387777427121 106643489011801040833070341)
              ·
                refine ⟨19995654189712695156200689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106643489011801040833070341 19995654189712695156200689)
                ·
                  refine ⟨14996740642284521367150517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19995654189712695156200689 14996740642284521367150517)
                  ·
                    refine ⟨1405944435214173878170361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14996740642284521367150517 1405944435214173878170361)
                    ·
                      rfl

theorem cell23_8214201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_8214201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214201 prefixEnd_8214201 := by exact prefixLift 8214201
  have htrace : WordTrace (prefixWord ++ tailWord_8214201) baseStart_8214201 baseEnd_8214201 := by
    simpa [prefixWord, tailWord_8214201, baseEnd_8214201] using wordTrace_append hprefix tailTrace_8214201
  have hstable : (prefixWord ++ tailWord_8214201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214201).length < 2 ^ (prefixWord ++ tailWord_8214201).sum := by decide
  have hdescent : baseEnd_8214201 < baseStart_8214201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214328 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_8214328 : Nat := 118140960795 + 8214328 * 2 ^ 59
def prefixEnd_8214328 : Nat := 4983230072969 + 3 ^ 40 * 8214328 * 2
def baseEnd_8214328 : Nat := 4217898517685642637622999

theorem tailTrace_8214328 : CollatzResearch.WordTrace tailWord_8214328 prefixEnd_8214328 4217898517685642637622999 := by
  unfold tailWord_8214328
  simp only [CollatzResearch.WordTrace]
  refine ⟨149800577692450013188645819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199734103589933350918194425 149800577692450013188645819)
  ·
    refine ⟨224700866538675019782968729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149800577692450013188645819 224700866538675019782968729)
    ·
      refine ⟨168525649904006264837226547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224700866538675019782968729 168525649904006264837226547)
      ·
        refine ⟨252788474856009397255839821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168525649904006264837226547 252788474856009397255839821)
        ·
          refine ⟨94795678071003523970939933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252788474856009397255839821 94795678071003523970939933)
          ·
            refine ⟨35548379276626321489102475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94795678071003523970939933 35548379276626321489102475)
            ·
              refine ⟨53322568914939482233653713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35548379276626321489102475 53322568914939482233653713)
              ·
                refine ⟨39991926686204611675240285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53322568914939482233653713 39991926686204611675240285)
                ·
                  refine ⟨14996972507326729378215107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39991926686204611675240285 14996972507326729378215107)
                  ·
                    refine ⟨22495458760990094067322661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14996972507326729378215107 22495458760990094067322661)
                    ·
                      refine ⟨4217898517685642637622999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22495458760990094067322661 4217898517685642637622999)
                      ·
                        rfl

theorem cell23_8214328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_8214328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214328 prefixEnd_8214328 := by exact prefixLift 8214328
  have htrace : WordTrace (prefixWord ++ tailWord_8214328) baseStart_8214328 baseEnd_8214328 := by
    simpa [prefixWord, tailWord_8214328, baseEnd_8214328] using wordTrace_append hprefix tailTrace_8214328
  have hstable : (prefixWord ++ tailWord_8214328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214328).length < 2 ^ (prefixWord ++ tailWord_8214328).sum := by decide
  have hdescent : baseEnd_8214328 < baseStart_8214328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214342 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_8214342 : Nat := 118140960795 + 8214342 * 2 ^ 59
def prefixEnd_8214342 : Nat := 4983230072969 + 3 ^ 40 * 8214342 * 2
def baseEnd_8214342 : Nat := 1405968568804935194282645

theorem tailTrace_8214342 : CollatzResearch.WordTrace tailWord_8214342 prefixEnd_8214342 1405968568804935194282645 := by
  unfold tailWord_8214342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362552062714040836509415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199734444004566204512200853 9362552062714040836509415)
  ·
    refine ⟨14043828094071061254764123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362552062714040836509415 14043828094071061254764123)
    ·
      refine ⟨21065742141106591882146185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043828094071061254764123 21065742141106591882146185)
      ·
        refine ⟨15799306605829943911609639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21065742141106591882146185 15799306605829943911609639)
        ·
          refine ⟨23698959908744915867414459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15799306605829943911609639 23698959908744915867414459)
          ·
            refine ⟨35548439863117373801121689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23698959908744915867414459 35548439863117373801121689)
            ·
              refine ⟨26661329897338030350841267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35548439863117373801121689 26661329897338030350841267)
              ·
                refine ⟨39991994846007045526261901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26661329897338030350841267 39991994846007045526261901)
                ·
                  refine ⟨14996998067252642072348213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39991994846007045526261901 14996998067252642072348213)
                  ·
                    refine ⟨1405968568804935194282645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14996998067252642072348213 1405968568804935194282645)
                    ·
                      rfl

theorem cell23_8214342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_8214342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214342 prefixEnd_8214342 := by exact prefixLift 8214342
  have htrace : WordTrace (prefixWord ++ tailWord_8214342) baseStart_8214342 baseEnd_8214342 := by
    simpa [prefixWord, tailWord_8214342, baseEnd_8214342] using wordTrace_append hprefix tailTrace_8214342
  have hstable : (prefixWord ++ tailWord_8214342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214342).length < 2 ^ (prefixWord ++ tailWord_8214342).sum := by decide
  have hdescent : baseEnd_8214342 < baseStart_8214342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214349 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_8214349 : Nat := 118140960795 + 8214349 * 2 ^ 59
def prefixEnd_8214349 : Nat := 4983230072969 + 3 ^ 40 * 8214349 * 2
def baseEnd_8214349 : Nat := 4217909300779387055460403

theorem tailTrace_8214349 : CollatzResearch.WordTrace tailWord_8214349 prefixEnd_8214349 4217909300779387055460403 := by
  unfold tailWord_8214349
  simp only [CollatzResearch.WordTrace]
  refine ⟨299601921317823946963806101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199734614211882631309204067 299601921317823946963806101)
  ·
    refine ⟨14043840061772997513928411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299601921317823946963806101 14043840061772997513928411)
    ·
      refine ⟨21065760092659496270892617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043840061772997513928411 21065760092659496270892617)
      ·
        refine ⟨15799320069494622203169463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21065760092659496270892617 15799320069494622203169463)
        ·
          refine ⟨23698980104241933304754195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15799320069494622203169463 23698980104241933304754195)
          ·
            refine ⟨35548470156362899957131293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23698980104241933304754195 35548470156362899957131293)
            ·
              refine ⟨13330676308636087483924235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35548470156362899957131293 13330676308636087483924235)
              ·
                refine ⟨19996014462954131225886353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13330676308636087483924235 19996014462954131225886353)
                ·
                  refine ⟨14997010847215598419414765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19996014462954131225886353 14997010847215598419414765)
                  ·
                    refine ⟨5623879067705849407280537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14997010847215598419414765 5623879067705849407280537)
                    ·
                      refine ⟨4217909300779387055460403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623879067705849407280537 4217909300779387055460403)
                      ·
                        rfl

theorem cell23_8214349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_8214349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214349 prefixEnd_8214349 := by exact prefixLift 8214349
  have htrace : WordTrace (prefixWord ++ tailWord_8214349) baseStart_8214349 baseEnd_8214349 := by
    simpa [prefixWord, tailWord_8214349, baseEnd_8214349] using wordTrace_append hprefix tailTrace_8214349
  have hstable : (prefixWord ++ tailWord_8214349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214349).length < 2 ^ (prefixWord ++ tailWord_8214349).sum := by decide
  have hdescent : baseEnd_8214349 < baseStart_8214349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214359 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 1, 5]
def baseStart_8214359 : Nat := 118140960795 + 8214359 * 2 ^ 59
def prefixEnd_8214359 : Nat := 4983230072969 + 3 ^ 40 * 8214359 * 2
def baseEnd_8214359 : Nat := 1405971478528644005445119

theorem tailTrace_8214359 : CollatzResearch.WordTrace tailWord_8214359 prefixEnd_8214359 1405971478528644005445119 := by
  unfold tailWord_8214359
  simp only [CollatzResearch.WordTrace]
  refine ⟨299602286047787718671670131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199734857365191812447780087 299602286047787718671670131)
  ·
    refine ⟨449403429071681578007505197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299602286047787718671670131 449403429071681578007505197)
    ·
      refine ⟨168526285901880591752814449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449403429071681578007505197 168526285901880591752814449)
      ·
        refine ⟨126394714426410443814610837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168526285901880591752814449 126394714426410443814610837)
        ·
          refine ⟨5924752238737989553809883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126394714426410443814610837 5924752238737989553809883)
          ·
            refine ⟨8887128358106984330714825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924752238737989553809883 8887128358106984330714825)
            ·
              refine ⟨6665346268580238248036119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887128358106984330714825 6665346268580238248036119)
              ·
                refine ⟨9998019402870357372054179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665346268580238248036119 9998019402870357372054179)
                ·
                  refine ⟨14997029104305536058081269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998019402870357372054179 14997029104305536058081269)
                  ·
                    refine ⟨1405971478528644005445119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14997029104305536058081269 1405971478528644005445119)
                    ·
                      rfl

theorem cell23_8214359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_8214359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214359 prefixEnd_8214359 := by exact prefixLift 8214359
  have htrace : WordTrace (prefixWord ++ tailWord_8214359) baseStart_8214359 baseEnd_8214359 := by
    simpa [prefixWord, tailWord_8214359, baseEnd_8214359] using wordTrace_append hprefix tailTrace_8214359
  have hstable : (prefixWord ++ tailWord_8214359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214359).length < 2 ^ (prefixWord ++ tailWord_8214359).sum := by decide
  have hdescent : baseEnd_8214359 < baseStart_8214359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214430 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8214430 : Nat := 118140960795 + 8214430 * 2 ^ 59
def prefixEnd_8214430 : Nat := 4983230072969 + 3 ^ 40 * 8214430 * 2
def baseEnd_8214430 : Nat := 4217950892712401238547531

theorem tailTrace_8214430 : CollatzResearch.WordTrace tailWord_8214430 prefixEnd_8214430 4217950892712401238547531 := by
  unfold tailWord_8214430
  simp only [CollatzResearch.WordTrace]
  refine ⟨37450609453816312224688093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199736583753686998531669829 37450609453816312224688093)
  ·
    refine ⟨14043978545181117084258035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37450609453816312224688093 14043978545181117084258035)
    ·
      refine ⟨21065967817771675626387053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043978545181117084258035 21065967817771675626387053)
      ·
        refine ⟨7899737931664378359895145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21065967817771675626387053 7899737931664378359895145)
        ·
          refine ⟨5924803448748283769921359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7899737931664378359895145 5924803448748283769921359)
          ·
            refine ⟨8887205173122425654882039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5924803448748283769921359 8887205173122425654882039)
            ·
              refine ⟨13330807759683638482323059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887205173122425654882039 13330807759683638482323059)
              ·
                refine ⟨19996211639525457723484589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13330807759683638482323059 19996211639525457723484589)
                ·
                  refine ⟨7498579364822046646306721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19996211639525457723484589 7498579364822046646306721)
                  ·
                    refine ⟨5623934523616534984730041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7498579364822046646306721 5623934523616534984730041)
                    ·
                      refine ⟨4217950892712401238547531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5623934523616534984730041 4217950892712401238547531)
                      ·
                        rfl

theorem cell23_8214430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8214430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214430 prefixEnd_8214430 := by exact prefixLift 8214430
  have htrace : WordTrace (prefixWord ++ tailWord_8214430) baseStart_8214430 baseEnd_8214430 := by
    simpa [prefixWord, tailWord_8214430, baseEnd_8214430] using wordTrace_append hprefix tailTrace_8214430
  have hstable : (prefixWord ++ tailWord_8214430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214430).length < 2 ^ (prefixWord ++ tailWord_8214430).sum := by decide
  have hdescent : baseEnd_8214430 < baseStart_8214430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214475 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 5]
def baseStart_8214475 : Nat := 118140960795 + 8214475 * 2 ^ 59
def prefixEnd_8214475 : Nat := 4983230072969 + 3 ^ 40 * 8214475 * 2
def baseEnd_8214475 : Nat := 468663777704650395831647

theorem tailTrace_8214475 : CollatzResearch.WordTrace tailWord_8214475 prefixEnd_8214475 468663777704650395831647 := by
  unfold tailWord_8214475
  simp only [CollatzResearch.WordTrace]
  refine ⟨299606516915367470482892879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199737677943578313655261919 299606516915367470482892879)
  ·
    refine ⟨449409775373051205724339319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299606516915367470482892879 449409775373051205724339319)
    ·
      refine ⟨674114663059576808586508979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449409775373051205724339319 674114663059576808586508979)
      ·
        refine ⟨1011171994589365212879763469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674114663059576808586508979 1011171994589365212879763469)
        ·
          refine ⟨379189497971011954829911301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1011171994589365212879763469 379189497971011954829911301)
          ·
            refine ⟨71098030869564741530608369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 379189497971011954829911301 71098030869564741530608369)
            ·
              refine ⟨53323523152173556147956277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71098030869564741530608369 53323523152173556147956277)
              ·
                refine ⟨4999080295516270888870901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53323523152173556147956277 4999080295516270888870901)
                ·
                  refine ⟨468663777704650395831647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999080295516270888870901 468663777704650395831647)
                  ·
                    rfl

theorem cell23_8214475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 5].length) (baseStart_8214475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214475 prefixEnd_8214475 := by exact prefixLift 8214475
  have htrace : WordTrace (prefixWord ++ tailWord_8214475) baseStart_8214475 baseEnd_8214475 := by
    simpa [prefixWord, tailWord_8214475, baseEnd_8214475] using wordTrace_append hprefix tailTrace_8214475
  have hstable : (prefixWord ++ tailWord_8214475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214475).length < 2 ^ (prefixWord ++ tailWord_8214475).sum := by decide
  have hdescent : baseEnd_8214475 < baseStart_8214475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214528 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_8214528 : Nat := 118140960795 + 8214528 * 2 ^ 59
def prefixEnd_8214528 : Nat := 4983230072969 + 3 ^ 40 * 8214528 * 2
def baseEnd_8214528 : Nat := 4218001213816541855122079

theorem tailTrace_8214528 : CollatzResearch.WordTrace tailWord_8214528 prefixEnd_8214528 4218001213816541855122079 := by
  unfold tailWord_8214528
  simp only [CollatzResearch.WordTrace]
  refine ⟨149804224992087730267286119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199738966656116973689714825 149804224992087730267286119)
  ·
    refine ⟨224706337488131595400929179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149804224992087730267286119 224706337488131595400929179)
    ·
      refine ⟨337059506232197393101393769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224706337488131595400929179 337059506232197393101393769)
      ·
        refine ⟨252794629674148044826045327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337059506232197393101393769 252794629674148044826045327)
        ·
          refine ⟨379191944511222067239067991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252794629674148044826045327 379191944511222067239067991)
          ·
            refine ⟨568787916766833100858601987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379191944511222067239067991 568787916766833100858601987)
            ·
              refine ⟨853181875150249651287902981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568787916766833100858601987 853181875150249651287902981)
              ·
                refine ⟨159971601590671809616481809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 853181875150249651287902981 159971601590671809616481809)
                ·
                  refine ⟨119978701193003857212361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159971601590671809616481809 119978701193003857212361357)
                  ·
                    refine ⟨44992012947376446454635509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119978701193003857212361357 44992012947376446454635509)
                    ·
                      refine ⟨4218001213816541855122079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44992012947376446454635509 4218001213816541855122079)
                      ·
                        rfl

theorem cell23_8214528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_8214528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214528 prefixEnd_8214528 := by exact prefixLift 8214528
  have htrace : WordTrace (prefixWord ++ tailWord_8214528) baseStart_8214528 baseEnd_8214528 := by
    simpa [prefixWord, tailWord_8214528, baseEnd_8214528] using wordTrace_append hprefix tailTrace_8214528
  have hstable : (prefixWord ++ tailWord_8214528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214528).length < 2 ^ (prefixWord ++ tailWord_8214528).sum := by decide
  have hdescent : baseEnd_8214528 < baseStart_8214528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214542 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_8214542 : Nat := 118140960795 + 8214542 * 2 ^ 59
def prefixEnd_8214542 : Nat := 4983230072969 + 3 ^ 40 * 8214542 * 2
def baseEnd_8214542 : Nat := 4218008402545704800347015

theorem tailTrace_8214542 : CollatzResearch.WordTrace tailWord_8214542 prefixEnd_8214542 4218008402545704800347015 := by
  unfold tailWord_8214542
  simp only [CollatzResearch.WordTrace]
  refine ⟨37451120075765592615697735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199739307070749827283721253 37451120075765592615697735)
  ·
    refine ⟨56176680113648388923546603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37451120075765592615697735 56176680113648388923546603)
    ·
      refine ⟨84265020170472583385319905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56176680113648388923546603 84265020170472583385319905)
      ·
        refine ⟨63198765127854437538989929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84265020170472583385319905 63198765127854437538989929)
        ·
          refine ⟨47399073845890828154242447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63198765127854437538989929 47399073845890828154242447)
          ·
            refine ⟨71098610768836242231363671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47399073845890828154242447 71098610768836242231363671)
            ·
              refine ⟨106647916153254363347045507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71098610768836242231363671 106647916153254363347045507)
              ·
                refine ⟨159971874229881545020568261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106647916153254363347045507 159971874229881545020568261)
                ·
                  refine ⟨29994726418102789691356549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159971874229881545020568261 29994726418102789691356549)
                  ·
                    refine ⟨5624011203394273067129353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29994726418102789691356549 5624011203394273067129353)
                    ·
                      refine ⟨4218008402545704800347015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624011203394273067129353 4218008402545704800347015)
                      ·
                        rfl

theorem cell23_8214542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_8214542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214542 prefixEnd_8214542 := by exact prefixLift 8214542
  have htrace : WordTrace (prefixWord ++ tailWord_8214542) baseStart_8214542 baseEnd_8214542 := by
    simpa [prefixWord, tailWord_8214542, baseEnd_8214542] using wordTrace_append hprefix tailTrace_8214542
  have hstable : (prefixWord ++ tailWord_8214542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214542).length < 2 ^ (prefixWord ++ tailWord_8214542).sum := by decide
  have hdescent : baseEnd_8214542 < baseStart_8214542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214552 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_8214552 : Nat := 118140960795 + 8214552 * 2 ^ 59
def prefixEnd_8214552 : Nat := 4983230072969 + 3 ^ 40 * 8214552 * 2
def baseEnd_8214552 : Nat := 1406004512450749920407323

theorem tailTrace_8214552 : CollatzResearch.WordTrace tailWord_8214552 prefixEnd_8214552 1406004512450749920407323 := by
  unfold tailWord_8214552
  simp only [CollatzResearch.WordTrace]
  refine ⟨149804662668044256316722955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199739550224059008422297273 149804662668044256316722955)
  ·
    refine ⟨224706994002066384475084433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149804662668044256316722955 224706994002066384475084433)
    ·
      refine ⟨168530245501549788356313325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224706994002066384475084433 168530245501549788356313325)
      ·
        refine ⟨63198842063081170633617497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168530245501549788356313325 63198842063081170633617497)
        ·
          refine ⟨47399131547310877975213123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63198842063081170633617497 47399131547310877975213123)
          ·
            refine ⟨71098697320966316962819685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47399131547310877975213123 71098697320966316962819685)
            ·
              refine ⟨13331005747681184430528691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71098697320966316962819685 13331005747681184430528691)
              ·
                refine ⟨19996508621521776645793037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331005747681184430528691 19996508621521776645793037)
                ·
                  refine ⟨7498690733070666242172389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19996508621521776645793037 7498690733070666242172389)
                  ·
                    refine ⟨1406004512450749920407323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498690733070666242172389 1406004512450749920407323)
                    ·
                      rfl

theorem cell23_8214552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_8214552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214552 prefixEnd_8214552 := by exact prefixLift 8214552
  have htrace : WordTrace (prefixWord ++ tailWord_8214552) baseStart_8214552 baseEnd_8214552 := by
    simpa [prefixWord, tailWord_8214552, baseEnd_8214552] using wordTrace_append hprefix tailTrace_8214552
  have hstable : (prefixWord ++ tailWord_8214552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214552).length < 2 ^ (prefixWord ++ tailWord_8214552).sum := by decide
  have hdescent : baseEnd_8214552 < baseStart_8214552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214625 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_8214625 : Nat := 118140960795 + 8214625 * 2 ^ 59
def prefixEnd_8214625 : Nat := 4983230072969 + 3 ^ 40 * 8214625 * 2
def baseEnd_8214625 : Nat := 1406017007146675991869711

theorem tailTrace_8214625 : CollatzResearch.WordTrace tailWord_8214625 prefixEnd_8214625 1406017007146675991869711 := by
  unfold tailWord_8214625
  simp only [CollatzResearch.WordTrace]
  refine ⟨299611987864824046100853329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199741325243216030733902219 299611987864824046100853329)
  ·
    refine ⟨224708990898618034575639997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299611987864824046100853329 224708990898618034575639997)
    ·
      refine ⟨84265871586981762965864999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224708990898618034575639997 84265871586981762965864999)
      ·
        refine ⟨126398807380472644448797499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84265871586981762965864999 126398807380472644448797499)
        ·
          refine ⟨189598211070708966673196249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126398807380472644448797499 189598211070708966673196249)
          ·
            refine ⟨142198658303031725004897187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189598211070708966673196249 142198658303031725004897187)
            ·
              refine ⟨213297987454547587507345781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142198658303031725004897187 213297987454547587507345781)
              ·
                refine ⟨19996686323863836328813667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213297987454547587507345781 19996686323863836328813667)
                ·
                  refine ⟨29995029485795754493220501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996686323863836328813667 29995029485795754493220501)
                  ·
                    refine ⟨1406017007146675991869711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29995029485795754493220501 1406017007146675991869711)
                    ·
                      rfl

theorem cell23_8214625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_8214625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214625 prefixEnd_8214625 := by exact prefixLift 8214625
  have htrace : WordTrace (prefixWord ++ tailWord_8214625) baseStart_8214625 baseEnd_8214625 := by
    simpa [prefixWord, tailWord_8214625, baseEnd_8214625] using wordTrace_append hprefix tailTrace_8214625
  have hstable : (prefixWord ++ tailWord_8214625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214625).length < 2 ^ (prefixWord ++ tailWord_8214625).sum := by decide
  have hdescent : baseEnd_8214625 < baseStart_8214625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214629 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_8214629 : Nat := 118140960795 + 8214629 * 2 ^ 59
def prefixEnd_8214629 : Nat := 4983230072969 + 3 ^ 40 * 8214629 * 2
def baseEnd_8214629 : Nat := 1406017691787548653319705

theorem tailTrace_8214629 : CollatzResearch.WordTrace tailWord_8214629 prefixEnd_8214629 1406017691787548653319705 := by
  unfold tailWord_8214629
  simp only [CollatzResearch.WordTrace]
  refine ⟨299612133756809554783998941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199741422504539703189332627 299612133756809554783998941)
  ·
    refine ⟨112354550158803583043999603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299612133756809554783998941 112354550158803583043999603)
    ·
      refine ⟨168531825238205374565999405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112354550158803583043999603 168531825238205374565999405)
      ·
        refine ⟨63199434464327015462249777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168531825238205374565999405 63199434464327015462249777)
        ·
          refine ⟨47399575848245261596687333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63199434464327015462249777 47399575848245261596687333)
          ·
            refine ⟨8887420471545986549378875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47399575848245261596687333 8887420471545986549378875)
            ·
              refine ⟨13331130707318979824068313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887420471545986549378875 13331130707318979824068313)
              ·
                refine ⟨9998348030489234868051235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331130707318979824068313 9998348030489234868051235)
                ·
                  refine ⟨14997522045733852302076853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998348030489234868051235 14997522045733852302076853)
                  ·
                    refine ⟨1406017691787548653319705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14997522045733852302076853 1406017691787548653319705)
                    ·
                      rfl

theorem cell23_8214629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_8214629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214629 prefixEnd_8214629 := by exact prefixLift 8214629
  have htrace : WordTrace (prefixWord ++ tailWord_8214629) baseStart_8214629 baseEnd_8214629 := by
    simpa [prefixWord, tailWord_8214629, baseEnd_8214629] using wordTrace_append hprefix tailTrace_8214629
  have hstable : (prefixWord ++ tailWord_8214629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214629).length < 2 ^ (prefixWord ++ tailWord_8214629).sum := by decide
  have hdescent : baseEnd_8214629 < baseStart_8214629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214642 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_8214642 : Nat := 118140960795 + 8214642 * 2 ^ 59
def prefixEnd_8214642 : Nat := 4983230072969 + 3 ^ 40 * 8214642 * 2
def baseEnd_8214642 : Nat := 1406019916870384803032185

theorem tailTrace_8214642 : CollatzResearch.WordTrace tailWord_8214642 prefixEnd_8214642 1406019916870384803032185 := by
  unfold tailWord_8214642
  simp only [CollatzResearch.WordTrace]
  refine ⟨74903151976440614501055545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199741738603841638669481453 74903151976440614501055545)
  ·
    refine ⟨56177363982330460875791659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74903151976440614501055545 56177363982330460875791659)
    ·
      refine ⟨84266045973495691313687489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56177363982330460875791659 84266045973495691313687489)
      ·
        refine ⟨63199534480121768485265617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84266045973495691313687489 63199534480121768485265617)
        ·
          refine ⟨47399650860091326363949213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63199534480121768485265617 47399650860091326363949213)
          ·
            refine ⟨17774869072534247386480955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47399650860091326363949213 17774869072534247386480955)
            ·
              refine ⟨26662303608801371079721433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17774869072534247386480955 26662303608801371079721433)
              ·
                refine ⟨19996727706601028309791075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26662303608801371079721433 19996727706601028309791075)
                ·
                  refine ⟨29995091559901542464686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996727706601028309791075 29995091559901542464686613)
                  ·
                    refine ⟨1406019916870384803032185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29995091559901542464686613 1406019916870384803032185)
                    ·
                      rfl

theorem cell23_8214642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_8214642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214642 prefixEnd_8214642 := by exact prefixLift 8214642
  have htrace : WordTrace (prefixWord ++ tailWord_8214642) baseStart_8214642 baseEnd_8214642 := by
    simpa [prefixWord, tailWord_8214642, baseEnd_8214642] using wordTrace_append hprefix tailTrace_8214642
  have hstable : (prefixWord ++ tailWord_8214642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214642).length < 2 ^ (prefixWord ++ tailWord_8214642).sum := by decide
  have hdescent : baseEnd_8214642 < baseStart_8214642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214646 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_8214646 : Nat := 118140960795 + 8214646 * 2 ^ 59
def prefixEnd_8214646 : Nat := 4983230072969 + 3 ^ 40 * 8214646 * 2
def baseEnd_8214646 : Nat := 1406020601511257464482179

theorem tailTrace_8214646 : CollatzResearch.WordTrace tailWord_8214646 prefixEnd_8214646 1406020601511257464482179 := by
  unfold tailWord_8214646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725797112359247917960487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199741835865165311124911861 18725797112359247917960487)
  ·
    refine ⟨28088695668538871876940731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18725797112359247917960487 28088695668538871876940731)
    ·
      refine ⟨42133043502808307815411097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28088695668538871876940731 42133043502808307815411097)
      ·
        refine ⟨31599782627106230861558323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42133043502808307815411097 31599782627106230861558323)
        ·
          refine ⟨47399673940659346292337485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31599782627106230861558323 47399673940659346292337485)
          ·
            refine ⟨17774877727747254859626557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47399673940659346292337485 17774877727747254859626557)
            ·
              refine ⟨6665579147905220572359959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17774877727747254859626557 6665579147905220572359959)
              ·
                refine ⟨9998368721857830858539939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665579147905220572359959 9998368721857830858539939)
                ·
                  refine ⟨14997553082786746287809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998368721857830858539939 14997553082786746287809909)
                  ·
                    refine ⟨1406020601511257464482179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14997553082786746287809909 1406020601511257464482179)
                    ·
                      rfl

theorem cell23_8214646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_8214646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214646 prefixEnd_8214646 := by exact prefixLift 8214646
  have htrace : WordTrace (prefixWord ++ tailWord_8214646) baseStart_8214646 baseEnd_8214646 := by
    simpa [prefixWord, tailWord_8214646, baseEnd_8214646] using wordTrace_append hprefix tailTrace_8214646
  have hstable : (prefixWord ++ tailWord_8214646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214646).length < 2 ^ (prefixWord ++ tailWord_8214646).sum := by decide
  have hdescent : baseEnd_8214646 < baseStart_8214646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214652 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_8214652 : Nat := 118140960795 + 8214652 * 2 ^ 59
def prefixEnd_8214652 : Nat := 4983230072969 + 3 ^ 40 * 8214652 * 2
def baseEnd_8214652 : Nat := 4218064885417699369971509

theorem tailTrace_8214652 : CollatzResearch.WordTrace tailWord_8214652 prefixEnd_8214652 4218064885417699369971509 := by
  unfold tailWord_8214652
  simp only [CollatzResearch.WordTrace]
  refine ⟨149806486317863114856043105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199741981757150819808057473 149806486317863114856043105)
  ·
    refine ⟨112354864738397336142032329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149806486317863114856043105 112354864738397336142032329)
    ·
      refine ⟨84266148553798002106524247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112354864738397336142032329 84266148553798002106524247)
      ·
        refine ⟨126399222830697003159786371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84266148553798002106524247 126399222830697003159786371)
        ·
          refine ⟨189598834246045504739679557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126399222830697003159786371 189598834246045504739679557)
          ·
            refine ⟨35549781421133532138689917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189598834246045504739679557 35549781421133532138689917)
            ·
              refine ⟨13331168032925074552008719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35549781421133532138689917 13331168032925074552008719)
              ·
                refine ⟨19996752049387611828013079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331168032925074552008719 19996752049387611828013079)
                ·
                  refine ⟨29995128074081417742019619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996752049387611828013079 29995128074081417742019619)
                  ·
                    refine ⟨44992692111122126613029429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29995128074081417742019619 44992692111122126613029429)
                    ·
                      refine ⟨4218064885417699369971509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44992692111122126613029429 4218064885417699369971509)
                      ·
                        rfl

theorem cell23_8214652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_8214652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214652 prefixEnd_8214652 := by exact prefixLift 8214652
  have htrace : WordTrace (prefixWord ++ tailWord_8214652) baseStart_8214652 baseEnd_8214652 := by
    simpa [prefixWord, tailWord_8214652, baseEnd_8214652] using wordTrace_append hprefix tailTrace_8214652
  have hstable : (prefixWord ++ tailWord_8214652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214652).length < 2 ^ (prefixWord ++ tailWord_8214652).sum := by decide
  have hdescent : baseEnd_8214652 < baseStart_8214652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214659 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 2, 4]
def baseStart_8214659 : Nat := 118140960795 + 8214659 * 2 ^ 59
def prefixEnd_8214659 : Nat := 4983230072969 + 3 ^ 40 * 8214659 * 2
def baseEnd_8214659 : Nat := 1406022826594093614194659

theorem tailTrace_8214659 : CollatzResearch.WordTrace tailWord_8214659 prefixEnd_8214659 1406022826594093614194659 := by
  unfold tailWord_8214659
  simp only [CollatzResearch.WordTrace]
  refine ⟨299613227946700869907591031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199742151964467246605060687 299613227946700869907591031)
  ·
    refine ⟨449419841920051304861386547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299613227946700869907591031 449419841920051304861386547)
    ·
      refine ⟨674129762880076957292079821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449419841920051304861386547 674129762880076957292079821)
      ·
        refine ⟨252798661080028858984529933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674129762880076957292079821 252798661080028858984529933)
        ·
          refine ⟨94799497905010822119198725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252798661080028858984529933 94799497905010822119198725)
          ·
            refine ⟨17774905857189529147349761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94799497905010822119198725 17774905857189529147349761)
            ·
              refine ⟨13331179392892146860512321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774905857189529147349761 13331179392892146860512321)
              ·
                refine ⟨9998384544669110145384241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331179392892146860512321 9998384544669110145384241)
                ·
                  refine ⟨7498788408501832609038181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9998384544669110145384241 7498788408501832609038181)
                  ·
                    refine ⟨1406022826594093614194659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498788408501832609038181 1406022826594093614194659)
                    ·
                      rfl

theorem cell23_8214659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 4].length) (baseStart_8214659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214659 prefixEnd_8214659 := by exact prefixLift 8214659
  have htrace : WordTrace (prefixWord ++ tailWord_8214659) baseStart_8214659 baseEnd_8214659 := by
    simpa [prefixWord, tailWord_8214659, baseEnd_8214659] using wordTrace_append hprefix tailTrace_8214659
  have hstable : (prefixWord ++ tailWord_8214659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214659).length < 2 ^ (prefixWord ++ tailWord_8214659).sum := by decide
  have hdescent : baseEnd_8214659 < baseStart_8214659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214676 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_8214676 : Nat := 118140960795 + 8214676 * 2 ^ 59
def prefixEnd_8214676 : Nat := 4983230072969 + 3 ^ 40 * 8214676 * 2
def baseEnd_8214676 : Nat := 1406025736317802425357133

theorem tailTrace_8214676 : CollatzResearch.WordTrace tailWord_8214676 prefixEnd_8214676 1406025736317802425357133 := by
  unfold tailWord_8214676
  simp only [CollatzResearch.WordTrace]
  refine ⟨149806923993819640905479941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199742565325092854540639921 149806923993819640905479941)
  ·
    refine ⟨28088798248841182669777489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149806923993819640905479941 28088798248841182669777489)
    ·
      refine ⟨21066598686630887002333117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28088798248841182669777489 21066598686630887002333117)
      ·
        refine ⟨7899974507486582625874919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21066598686630887002333117 7899974507486582625874919)
        ·
          refine ⟨11849961761229873938812379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899974507486582625874919 11849961761229873938812379)
          ·
            refine ⟨17774942641844810908218569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849961761229873938812379 17774942641844810908218569)
            ·
              refine ⟨13331206981383608181163927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774942641844810908218569 13331206981383608181163927)
              ·
                refine ⟨19996810472075412271745891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331206981383608181163927 19996810472075412271745891)
                ·
                  refine ⟨29995215708113118407618837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996810472075412271745891 29995215708113118407618837)
                  ·
                    refine ⟨1406025736317802425357133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29995215708113118407618837 1406025736317802425357133)
                    ·
                      rfl

theorem cell23_8214676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_8214676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214676 prefixEnd_8214676 := by exact prefixLift 8214676
  have htrace : WordTrace (prefixWord ++ tailWord_8214676) baseStart_8214676 baseEnd_8214676 := by
    simpa [prefixWord, tailWord_8214676, baseEnd_8214676] using wordTrace_append hprefix tailTrace_8214676
  have hstable : (prefixWord ++ tailWord_8214676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214676).length < 2 ^ (prefixWord ++ tailWord_8214676).sum := by decide
  have hdescent : baseEnd_8214676 < baseStart_8214676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214679 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_8214679 : Nat := 118140960795 + 8214679 * 2 ^ 59
def prefixEnd_8214679 : Nat := 4983230072969 + 3 ^ 40 * 8214679 * 2
def baseEnd_8214679 : Nat := 4218078749395370764333885

theorem tailTrace_8214679 : CollatzResearch.WordTrace tailWord_8214679 prefixEnd_8214679 4218078749395370764333885 := by
  unfold tailWord_8214679
  simp only [CollatzResearch.WordTrace]
  refine ⟨299613957406628413323319091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199742638271085608882212727 299613957406628413323319091)
  ·
    refine ⟨449420936109942619984978637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299613957406628413323319091 449420936109942619984978637)
    ·
      refine ⟨168532851041228482494366989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 449420936109942619984978637 168532851041228482494366989)
      ·
        refine ⟨63199819140460680935387621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168532851041228482494366989 63199819140460680935387621)
        ·
          refine ⟨11849966088836377675385179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63199819140460680935387621 11849966088836377675385179)
          ·
            refine ⟨17774949133254566513077769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849966088836377675385179 17774949133254566513077769)
            ·
              refine ⟨13331211849940924884808327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774949133254566513077769 13331211849940924884808327)
              ·
                refine ⟨19996817774911387327212491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331211849940924884808327 19996817774911387327212491)
                ·
                  refine ⟨29995226662367080990818737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19996817774911387327212491 29995226662367080990818737)
                  ·
                    refine ⟨22496419996775310743114053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29995226662367080990818737 22496419996775310743114053)
                    ·
                      refine ⟨4218078749395370764333885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22496419996775310743114053 4218078749395370764333885)
                      ·
                        rfl

theorem cell23_8214679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_8214679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214679 prefixEnd_8214679 := by exact prefixLift 8214679
  have htrace : WordTrace (prefixWord ++ tailWord_8214679) baseStart_8214679 baseEnd_8214679 := by
    simpa [prefixWord, tailWord_8214679, baseEnd_8214679] using wordTrace_append hprefix tailTrace_8214679
  have hstable : (prefixWord ++ tailWord_8214679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214679).length < 2 ^ (prefixWord ++ tailWord_8214679).sum := by decide
  have hdescent : baseEnd_8214679 < baseStart_8214679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214715 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 6]
def baseStart_8214715 : Nat := 118140960795 + 8214715 * 2 ^ 59
def prefixEnd_8214715 : Nat := 4983230072969 + 3 ^ 40 * 8214715 * 2
def baseEnd_8214715 : Nat := 1406032411566310874494573

theorem tailTrace_8214715 : CollatzResearch.WordTrace tailWord_8214715 prefixEnd_8214715 1406032411566310874494573 := by
  unfold tailWord_8214715
  simp only [CollatzResearch.WordTrace]
  refine ⟨299615270434497991471629599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199743513622998660981086399 299615270434497991471629599)
  ·
    refine ⟨449422905651746987207444399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299615270434497991471629599 449422905651746987207444399)
    ·
      refine ⟨674134358477620480811166599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449422905651746987207444399 674134358477620480811166599)
      ·
        refine ⟨1011201537716430721216749899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674134358477620480811166599 1011201537716430721216749899)
        ·
          refine ⟨1516802306574646081825124849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011201537716430721216749899 1516802306574646081825124849)
          ·
            refine ⟨1137601729930984561368843637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1516802306574646081825124849 1137601729930984561368843637)
            ·
              refine ⟨106650162181029802628329091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1137601729930984561368843637 106650162181029802628329091)
              ·
                refine ⟨159975243271544703942493637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106650162181029802628329091 159975243271544703942493637)
                ·
                  refine ⟨29995358113414631989217557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159975243271544703942493637 29995358113414631989217557)
                  ·
                    refine ⟨1406032411566310874494573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29995358113414631989217557 1406032411566310874494573)
                    ·
                      rfl

theorem cell23_8214715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_8214715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214715 prefixEnd_8214715 := by exact prefixLift 8214715
  have htrace : WordTrace (prefixWord ++ tailWord_8214715) baseStart_8214715 baseEnd_8214715 := by
    simpa [prefixWord, tailWord_8214715, baseEnd_8214715] using wordTrace_append hprefix tailTrace_8214715
  have hstable : (prefixWord ++ tailWord_8214715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214715).length < 2 ^ (prefixWord ++ tailWord_8214715).sum := by decide
  have hdescent : baseEnd_8214715 < baseStart_8214715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214716 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_8214716 : Nat := 118140960795 + 8214716 * 2 ^ 59
def prefixEnd_8214716 : Nat := 4983230072969 + 3 ^ 40 * 8214716 * 2
def baseEnd_8214716 : Nat := 4218097748179587119571215

theorem tailTrace_8214716 : CollatzResearch.WordTrace tailWord_8214716 prefixEnd_8214716 4218097748179587119571215 := by
  unfold tailWord_8214716
  simp only [CollatzResearch.WordTrace]
  refine ⟨149807653453747184321208001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199743537938329579094944001 149807653453747184321208001)
  ·
    refine ⟨112355740090310388240906001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149807653453747184321208001 112355740090310388240906001)
    ·
      refine ⟨84266805067732791180679501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112355740090310388240906001 84266805067732791180679501)
      ·
        refine ⟨31600051900399796692754813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84266805067732791180679501 31600051900399796692754813)
        ·
          refine ⟨11850019462649923759783055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31600051900399796692754813 11850019462649923759783055)
          ·
            refine ⟨17775029193974885639674583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11850019462649923759783055 17775029193974885639674583)
            ·
              refine ⟨26662543790962328459511875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17775029193974885639674583 26662543790962328459511875)
              ·
                refine ⟨39993815686443492689267813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26662543790962328459511875 39993815686443492689267813)
                ·
                  refine ⟨7498840441208154879237715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39993815686443492689267813 7498840441208154879237715)
                  ·
                    refine ⟨11248260661812232318856573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7498840441208154879237715 11248260661812232318856573)
                    ·
                      refine ⟨4218097748179587119571215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248260661812232318856573 4218097748179587119571215)
                      ·
                        rfl

theorem cell23_8214716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_8214716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214716 prefixEnd_8214716 := by exact prefixLift 8214716
  have htrace : WordTrace (prefixWord ++ tailWord_8214716) baseStart_8214716 baseEnd_8214716 := by
    simpa [prefixWord, tailWord_8214716, baseEnd_8214716] using wordTrace_append hprefix tailTrace_8214716
  have hstable : (prefixWord ++ tailWord_8214716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214716).length < 2 ^ (prefixWord ++ tailWord_8214716).sum := by decide
  have hdescent : baseEnd_8214716 < baseStart_8214716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214739 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 8, 2, 2]
def baseStart_8214739 : Nat := 118140960795 + 8214739 * 2 ^ 59
def prefixEnd_8214739 : Nat := 4983230072969 + 3 ^ 40 * 8214739 * 2
def baseEnd_8214739 : Nat := 4218109558234640529583609

theorem tailTrace_8214739 : CollatzResearch.WordTrace tailWord_8214739 prefixEnd_8214739 4218109558234640529583609 := by
  unfold tailWord_8214739
  simp only [CollatzResearch.WordTrace]
  refine ⟨299616145786411043570503271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199744097190940695713668847 299616145786411043570503271)
  ·
    refine ⟨449424218679616565355754907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299616145786411043570503271 449424218679616565355754907)
    ·
      refine ⟨674136328019424848033632361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449424218679616565355754907 674136328019424848033632361)
      ·
        refine ⟨505602246014568636025224271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674136328019424848033632361 505602246014568636025224271)
        ·
          refine ⟨758403369021852954037836407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505602246014568636025224271 758403369021852954037836407)
          ·
            refine ⟨1137605053532779431056754611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758403369021852954037836407 1137605053532779431056754611)
            ·
              refine ⟨1706407580299169146585131917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137605053532779431056754611 1706407580299169146585131917)
              ·
                refine ⟨639902842612188429969424469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706407580299169146585131917 639902842612188429969424469)
                ·
                  refine ⟨7498861436861583163704193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 639902842612188429969424469 7498861436861583163704193)
                  ·
                    refine ⟨5624146077646187372778145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7498861436861583163704193 5624146077646187372778145)
                    ·
                      refine ⟨4218109558234640529583609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624146077646187372778145 4218109558234640529583609)
                      ·
                        rfl

theorem cell23_8214739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2, 2].length) (baseStart_8214739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214739 prefixEnd_8214739 := by exact prefixLift 8214739
  have htrace : WordTrace (prefixWord ++ tailWord_8214739) baseStart_8214739 baseEnd_8214739 := by
    simpa [prefixWord, tailWord_8214739, baseEnd_8214739] using wordTrace_append hprefix tailTrace_8214739
  have hstable : (prefixWord ++ tailWord_8214739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214739).length < 2 ^ (prefixWord ++ tailWord_8214739).sum := by decide
  have hdescent : baseEnd_8214739 < baseStart_8214739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214759 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8214759 : Nat := 118140960795 + 8214759 * 2 ^ 59
def prefixEnd_8214759 : Nat := 4983230072969 + 3 ^ 40 * 8214759 * 2
def baseEnd_8214759 : Nat := 4218119827847730451333517

theorem tailTrace_8214759 : CollatzResearch.WordTrace tailWord_8214759 prefixEnd_8214759 4218119827847730451333517 := by
  unfold tailWord_8214759
  simp only [CollatzResearch.WordTrace]
  refine ⟨299616875246338586986231331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199744583497559057990820887 299616875246338586986231331)
  ·
    refine ⟨449425312869507880479346997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299616875246338586986231331 449425312869507880479346997)
    ·
      refine ⟨42133623081516363794938781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 449425312869507880479346997 42133623081516363794938781)
      ·
        refine ⟨15800108655568636423102043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42133623081516363794938781 15800108655568636423102043)
        ·
          refine ⟨23700162983352954634653065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15800108655568636423102043 23700162983352954634653065)
          ·
            refine ⟨17775122237514715975989799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23700162983352954634653065 17775122237514715975989799)
            ·
              refine ⟨26662683356272073963984699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17775122237514715975989799 26662683356272073963984699)
              ·
                refine ⟨39994025034408110945977049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26662683356272073963984699 39994025034408110945977049)
                ·
                  refine ⟨29995518775806083209482787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39994025034408110945977049 29995518775806083209482787)
                  ·
                    refine ⟨44993278163709124814224181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29995518775806083209482787 44993278163709124814224181)
                    ·
                      refine ⟨4218119827847730451333517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44993278163709124814224181 4218119827847730451333517)
                      ·
                        rfl

theorem cell23_8214759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8214759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214759 prefixEnd_8214759 := by exact prefixLift 8214759
  have htrace : WordTrace (prefixWord ++ tailWord_8214759) baseStart_8214759 baseEnd_8214759 := by
    simpa [prefixWord, tailWord_8214759, baseEnd_8214759] using wordTrace_append hprefix tailTrace_8214759
  have hstable : (prefixWord ++ tailWord_8214759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214759).length < 2 ^ (prefixWord ++ tailWord_8214759).sum := by decide
  have hdescent : baseEnd_8214759 < baseStart_8214759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214846 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_8214846 : Nat := 118140960795 + 8214846 * 2 ^ 59
def prefixEnd_8214846 : Nat := 4983230072969 + 3 ^ 40 * 8214846 * 2
def baseEnd_8214846 : Nat := 4218164500664671610945617

theorem tailTrace_8214846 : CollatzResearch.WordTrace tailWord_8214846 prefixEnd_8214846 4218164500664671610945617 := by
  unfold tailWord_8214846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37452506049627925105581049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199746698931348933896432261 37452506049627925105581049)
  ·
    refine ⟨28089379537220943829185787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37452506049627925105581049 28089379537220943829185787)
    ·
      refine ⟨42134069305831415743778681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28089379537220943829185787 42134069305831415743778681)
      ·
        refine ⟨31600551979373561807834011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42134069305831415743778681 31600551979373561807834011)
        ·
          refine ⟨47400827969060342711751017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31600551979373561807834011 47400827969060342711751017)
          ·
            refine ⟨35550620976795257033813263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47400827969060342711751017 35550620976795257033813263)
            ·
              refine ⟨53325931465192885550719895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35550620976795257033813263 53325931465192885550719895)
              ·
                refine ⟨79988897197789328326079843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53325931465192885550719895 79988897197789328326079843)
                ·
                  refine ⟨119983345796683992489119765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79988897197789328326079843 119983345796683992489119765)
                  ·
                    refine ⟨5624219334219562147927489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119983345796683992489119765 5624219334219562147927489)
                    ·
                      refine ⟨4218164500664671610945617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624219334219562147927489 4218164500664671610945617)
                      ·
                        rfl

theorem cell23_8214846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_8214846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214846 prefixEnd_8214846 := by exact prefixLift 8214846
  have htrace : WordTrace (prefixWord ++ tailWord_8214846) baseStart_8214846 baseEnd_8214846 := by
    simpa [prefixWord, tailWord_8214846, baseEnd_8214846] using wordTrace_append hprefix tailTrace_8214846
  have hstable : (prefixWord ++ tailWord_8214846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214846).length < 2 ^ (prefixWord ++ tailWord_8214846).sum := by decide
  have hdescent : baseEnd_8214846 < baseStart_8214846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214866 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_8214866 : Nat := 118140960795 + 8214866 * 2 ^ 59
def prefixEnd_8214866 : Nat := 4983230072969 + 3 ^ 40 * 8214866 * 2
def baseEnd_8214866 : Nat := 4218174770277761532695525

theorem tailTrace_8214866 : CollatzResearch.WordTrace tailWord_8214866 prefixEnd_8214866 4218174770277761532695525 := by
  unfold tailWord_8214866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74905194464237736065094113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199747185237967296173584301 74905194464237736065094113)
  ·
    refine ⟨56178895848178302048820585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74905194464237736065094113 56178895848178302048820585)
    ·
      refine ⟨42134171886133726536615439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56178895848178302048820585 42134171886133726536615439)
      ·
        refine ⟨63201257829200589804923159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42134171886133726536615439 63201257829200589804923159)
        ·
          refine ⟨94801886743800884707384739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63201257829200589804923159 94801886743800884707384739)
          ·
            refine ⟨142202830115701327061077109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94801886743800884707384739 142202830115701327061077109)
            ·
              refine ⟨13331515323346999411975979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142202830115701327061077109 13331515323346999411975979)
              ·
                refine ⟨19997272985020499117963969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13331515323346999411975979 19997272985020499117963969)
                ·
                  refine ⟨14997954738765374338472977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19997272985020499117963969 14997954738765374338472977)
                  ·
                    refine ⟨11248466054074030753854733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14997954738765374338472977 11248466054074030753854733)
                    ·
                      refine ⟨4218174770277761532695525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248466054074030753854733 4218174770277761532695525)
                      ·
                        rfl

theorem cell23_8214866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_8214866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214866 prefixEnd_8214866 := by exact prefixLift 8214866
  have htrace : WordTrace (prefixWord ++ tailWord_8214866) baseStart_8214866 baseEnd_8214866 := by
    simpa [prefixWord, tailWord_8214866, baseEnd_8214866] using wordTrace_append hprefix tailTrace_8214866
  have hstable : (prefixWord ++ tailWord_8214866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214866).length < 2 ^ (prefixWord ++ tailWord_8214866).sum := by decide
  have hdescent : baseEnd_8214866 < baseStart_8214866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214896 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_8214896 : Nat := 118140960795 + 8214896 * 2 ^ 59
def prefixEnd_8214896 : Nat := 4983230072969 + 3 ^ 40 * 8214896 * 2
def baseEnd_8214896 : Nat := 4218190174697396415320387

theorem tailTrace_8214896 : CollatzResearch.WordTrace tailWord_8214896 prefixEnd_8214896 4218190174697396415320387 := by
  unfold tailWord_8214896
  simp only [CollatzResearch.WordTrace]
  refine ⟨149810936023421129691984271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199747914697894839589312361 149810936023421129691984271)
  ·
    refine ⟨224716404035131694537976407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149810936023421129691984271 224716404035131694537976407)
    ·
      refine ⟨337074606052697541806964611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224716404035131694537976407 337074606052697541806964611)
      ·
        refine ⟨505611909079046312710446917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337074606052697541806964611 505611909079046312710446917)
        ·
          refine ⟨94802232952321183633208797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 505611909079046312710446917 94802232952321183633208797)
          ·
            refine ⟨35550837357120443862453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94802232952321183633208797 35550837357120443862453299)
            ·
              refine ⟨53326256035680665793679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35550837357120443862453299 53326256035680665793679949)
              ·
                refine ⟨19997346013380249672629981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53326256035680665793679949 19997346013380249672629981)
                ·
                  refine ⟨7499004755017593627236243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19997346013380249672629981 7499004755017593627236243)
                  ·
                    refine ⟨11248507132526390440854365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499004755017593627236243 11248507132526390440854365)
                    ·
                      refine ⟨4218190174697396415320387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248507132526390440854365 4218190174697396415320387)
                      ·
                        rfl

theorem cell23_8214896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_8214896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214896 prefixEnd_8214896 := by exact prefixLift 8214896
  have htrace : WordTrace (prefixWord ++ tailWord_8214896) baseStart_8214896 baseEnd_8214896 := by
    simpa [prefixWord, tailWord_8214896, baseEnd_8214896] using wordTrace_append hprefix tailTrace_8214896
  have hstable : (prefixWord ++ tailWord_8214896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214896).length < 2 ^ (prefixWord ++ tailWord_8214896).sum := by decide
  have hdescent : baseEnd_8214896 < baseStart_8214896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214913 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_8214913 : Nat := 118140960795 + 8214913 * 2 ^ 59
def prefixEnd_8214913 : Nat := 4983230072969 + 3 ^ 40 * 8214913 * 2
def baseEnd_8214913 : Nat := 4218198903868522848807809

theorem tailTrace_8214913 : CollatzResearch.WordTrace tailWord_8214913 prefixEnd_8214913 4218198903868522848807809 := by
  unfold tailWord_8214913
  simp only [CollatzResearch.WordTrace]
  refine ⟨299622492087780671287337393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199748328058520447524891595 299622492087780671287337393)
  ·
    refine ⟨224716869065835503465503045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299622492087780671287337393 224716869065835503465503045)
    ·
      refine ⟨42134412949844156899781821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224716869065835503465503045 42134412949844156899781821)
      ·
        refine ⟨15800404856191558837418183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42134412949844156899781821 15800404856191558837418183)
        ·
          refine ⟨23700607284287338256127275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15800404856191558837418183 23700607284287338256127275)
          ·
            refine ⟨35550910926431007384190913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23700607284287338256127275 35550910926431007384190913)
            ·
              refine ⟨26663183194823255538143185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35550910926431007384190913 26663183194823255538143185)
              ·
                refine ⟨19997387396117441653607389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26663183194823255538143185 19997387396117441653607389)
                ·
                  refine ⟨7499020273544040620102771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19997387396117441653607389 7499020273544040620102771)
                  ·
                    refine ⟨11248530410316060930154157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7499020273544040620102771 11248530410316060930154157)
                    ·
                      refine ⟨4218198903868522848807809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248530410316060930154157 4218198903868522848807809)
                      ·
                        rfl

theorem cell23_8214913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_8214913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214913 prefixEnd_8214913 := by exact prefixLift 8214913
  have htrace : WordTrace (prefixWord ++ tailWord_8214913) baseStart_8214913 baseEnd_8214913 := by
    simpa [prefixWord, tailWord_8214913, baseEnd_8214913] using wordTrace_append hprefix tailTrace_8214913
  have hstable : (prefixWord ++ tailWord_8214913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214913).length < 2 ^ (prefixWord ++ tailWord_8214913).sum := by decide
  have hdescent : baseEnd_8214913 < baseStart_8214913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214916 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_8214916 : Nat := 118140960795 + 8214916 * 2 ^ 59
def prefixEnd_8214916 : Nat := 4983230072969 + 3 ^ 40 * 8214916 * 2
def baseEnd_8214916 : Nat := 1406066814770162112356765

theorem tailTrace_8214916 : CollatzResearch.WordTrace tailWord_8214916 prefixEnd_8214916 1406066814770162112356765 := by
  unfold tailWord_8214916
  simp only [CollatzResearch.WordTrace]
  refine ⟨149811300753384901399848301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199748401004513201866464401 149811300753384901399848301)
  ·
    refine ⟨56179237782519338024943113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149811300753384901399848301 56179237782519338024943113)
    ·
      refine ⟨42134428336889503518707335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56179237782519338024943113 42134428336889503518707335)
      ·
        refine ⟨63201642505334255278061003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42134428336889503518707335 63201642505334255278061003)
        ·
          refine ⟨94802463758001382917091505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63201642505334255278061003 94802463758001382917091505)
          ·
            refine ⟨71101847818501037187818629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94802463758001382917091505 71101847818501037187818629)
            ·
              refine ⟨13331596465968944472715993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71101847818501037187818629 13331596465968944472715993)
              ·
                refine ⟨9998697349476708354536995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331596465968944472715993 9998697349476708354536995)
                ·
                  refine ⟨14998046024215062531805493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998697349476708354536995 14998046024215062531805493)
                  ·
                    refine ⟨1406066814770162112356765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14998046024215062531805493 1406066814770162112356765)
                    ·
                      rfl

theorem cell23_8214916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_8214916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214916 prefixEnd_8214916 := by exact prefixLift 8214916
  have htrace : WordTrace (prefixWord ++ tailWord_8214916) baseStart_8214916 baseEnd_8214916 := by
    simpa [prefixWord, tailWord_8214916, baseEnd_8214916] using wordTrace_append hprefix tailTrace_8214916
  have hstable : (prefixWord ++ tailWord_8214916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214916).length < 2 ^ (prefixWord ++ tailWord_8214916).sum := by decide
  have hdescent : baseEnd_8214916 < baseStart_8214916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214946 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_8214946 : Nat := 118140960795 + 8214946 * 2 ^ 59
def prefixEnd_8214946 : Nat := 4983230072969 + 3 ^ 40 * 8214946 * 2
def baseEnd_8214946 : Nat := 1406071949576707073231719

theorem tailTrace_8214946 : CollatzResearch.WordTrace tailWord_8214946 prefixEnd_8214946 1406071949576707073231719 := by
  unfold tailWord_8214946
  simp only [CollatzResearch.WordTrace]
  refine ⟨74905923924165279480822173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199749130464440745282192461 74905923924165279480822173)
  ·
    refine ⟨28089721471561979805308315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74905923924165279480822173 28089721471561979805308315)
    ·
      refine ⟨42134582207342969707962473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28089721471561979805308315 42134582207342969707962473)
      ·
        refine ⟨31600936655507227280971855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42134582207342969707962473 31600936655507227280971855)
        ·
          refine ⟨47401404983260840921457783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31600936655507227280971855 47401404983260840921457783)
          ·
            refine ⟨71102107474891261382186675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47401404983260840921457783 71102107474891261382186675)
            ·
              refine ⟨106653161212336892073280013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71102107474891261382186675 106653161212336892073280013)
              ·
                refine ⟨39994935454626334527480005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106653161212336892073280013 39994935454626334527480005)
                ·
                  refine ⟨7499050397742437723902501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39994935454626334527480005 7499050397742437723902501)
                  ·
                    refine ⟨1406071949576707073231719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499050397742437723902501 1406071949576707073231719)
                    ·
                      rfl

theorem cell23_8214946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_8214946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214946 prefixEnd_8214946 := by exact prefixLift 8214946
  have htrace : WordTrace (prefixWord ++ tailWord_8214946) baseStart_8214946 baseEnd_8214946 := by
    simpa [prefixWord, tailWord_8214946, baseEnd_8214946] using wordTrace_append hprefix tailTrace_8214946
  have hstable : (prefixWord ++ tailWord_8214946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214946).length < 2 ^ (prefixWord ++ tailWord_8214946).sum := by decide
  have hdescent : baseEnd_8214946 < baseStart_8214946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214954 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_8214954 : Nat := 118140960795 + 8214954 * 2 ^ 59
def prefixEnd_8214954 : Nat := 4983230072969 + 3 ^ 40 * 8214954 * 2
def baseEnd_8214954 : Nat := 468691106286150798710569

theorem tailTrace_8214954 : CollatzResearch.WordTrace tailWord_8214954 prefixEnd_8214954 468691106286150798710569 := by
  unfold tailWord_8214954
  simp only [CollatzResearch.WordTrace]
  refine ⟨74905996870158033822394979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199749324987088090193053277 74905996870158033822394979)
  ·
    refine ⟨112358995305237050733592469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74905996870158033822394979 112358995305237050733592469)
    ·
      refine ⟨5266827904932986753137147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112358995305237050733592469 5266827904932986753137147)
      ·
        refine ⟨7900241857399480129705721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266827904932986753137147 7900241857399480129705721)
        ·
          refine ⟨5925181393049610097279291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7900241857399480129705721 5925181393049610097279291)
          ·
            refine ⟨8887772089574415145918937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925181393049610097279291 8887772089574415145918937)
            ·
              refine ⟨6665829067180811359439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887772089574415145918937 6665829067180811359439203)
              ·
                refine ⟨9998743600771217039158805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665829067180811359439203 9998743600771217039158805)
                ·
                  refine ⟨468691106286150798710569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9998743600771217039158805 468691106286150798710569)
                  ·
                    rfl

theorem cell23_8214954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_8214954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214954 prefixEnd_8214954 := by exact prefixLift 8214954
  have htrace : WordTrace (prefixWord ++ tailWord_8214954) baseStart_8214954 baseEnd_8214954 := by
    simpa [prefixWord, tailWord_8214954, baseEnd_8214954] using wordTrace_append hprefix tailTrace_8214954
  have hstable : (prefixWord ++ tailWord_8214954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214954).length < 2 ^ (prefixWord ++ tailWord_8214954).sum := by decide
  have hdescent : baseEnd_8214954 < baseStart_8214954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214973 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_8214973 : Nat := 118140960795 + 8214973 * 2 ^ 59
def prefixEnd_8214973 : Nat := 4983230072969 + 3 ^ 40 * 8214973 * 2
def baseEnd_8214973 : Nat := 4218229712707792614057533

theorem tailTrace_8214973 : CollatzResearch.WordTrace tailWord_8214973 prefixEnd_8214973 4218229712707792614057533 := by
  unfold tailWord_8214973
  simp only [CollatzResearch.WordTrace]
  refine ⟨299624680467563301534521573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199749786978375534356347715 299624680467563301534521573)
  ·
    refine ⟨56179627587668119037722795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299624680467563301534521573 56179627587668119037722795)
    ·
      refine ⟨84269441381502178556584193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56179627587668119037722795 84269441381502178556584193)
      ·
        refine ⟨63202081036126633917438145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84269441381502178556584193 63202081036126633917438145)
        ·
          refine ⟨47401560777094975438078609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63202081036126633917438145 47401560777094975438078609)
          ·
            refine ⟨35551170582821231578558957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47401560777094975438078609 35551170582821231578558957)
            ·
              refine ⟨13331688968557961841959609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35551170582821231578558957 13331688968557961841959609)
              ·
                refine ⟨9998766726418471381469707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13331688968557961841959609 9998766726418471381469707)
                ·
                  refine ⟨14998150089627707072204561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998766726418471381469707 14998150089627707072204561)
                  ·
                    refine ⟨11248612567220780304153421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14998150089627707072204561 11248612567220780304153421)
                    ·
                      refine ⟨4218229712707792614057533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248612567220780304153421 4218229712707792614057533)
                      ·
                        rfl

theorem cell23_8214973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_8214973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214973 prefixEnd_8214973 := by exact prefixLift 8214973
  have htrace : WordTrace (prefixWord ++ tailWord_8214973) baseStart_8214973 baseEnd_8214973 := by
    simpa [prefixWord, tailWord_8214973, baseEnd_8214973] using wordTrace_append hprefix tailTrace_8214973
  have hstable : (prefixWord ++ tailWord_8214973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214973).length < 2 ^ (prefixWord ++ tailWord_8214973).sum := by decide
  have hdescent : baseEnd_8214973 < baseStart_8214973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8214986 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_8214986 : Nat := 118140960795 + 8214986 * 2 ^ 59
def prefixEnd_8214986 : Nat := 4983230072969 + 3 ^ 40 * 8214986 * 2
def baseEnd_8214986 : Nat := 4218236387956301063194973

theorem tailTrace_8214986 : CollatzResearch.WordTrace tailWord_8214986 prefixEnd_8214986 4218236387956301063194973 := by
  unfold tailWord_8214986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74906288654129051188686203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199750103077677469836496541 74906288654129051188686203)
  ·
    refine ⟨112359432981193576783029305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74906288654129051188686203 112359432981193576783029305)
    ·
      refine ⟨84269574735895182587271979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112359432981193576783029305 84269574735895182587271979)
      ·
        refine ⟨126404362103842773880907969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84269574735895182587271979 126404362103842773880907969)
        ·
          refine ⟨94803271577882080410680977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126404362103842773880907969 94803271577882080410680977)
          ·
            refine ⟨71102453683411560308010733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94803271577882080410680977 71102453683411560308010733)
            ·
              refine ⟨26663420131279335115504025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71102453683411560308010733 26663420131279335115504025)
              ·
                refine ⟨19997565098459501336628019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26663420131279335115504025 19997565098459501336628019)
                ·
                  refine ⟨29996347647689252004942029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19997565098459501336628019 29996347647689252004942029)
                  ·
                    refine ⟨11248630367883469501853261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29996347647689252004942029 11248630367883469501853261)
                    ·
                      refine ⟨4218236387956301063194973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11248630367883469501853261 4218236387956301063194973)
                      ·
                        rfl

theorem cell23_8214986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_8214986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8214986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8214986 prefixEnd_8214986 := by exact prefixLift 8214986
  have htrace : WordTrace (prefixWord ++ tailWord_8214986) baseStart_8214986 baseEnd_8214986 := by
    simpa [prefixWord, tailWord_8214986, baseEnd_8214986] using wordTrace_append hprefix tailTrace_8214986
  have hstable : (prefixWord ++ tailWord_8214986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8214986).length < 2 ^ (prefixWord ++ tailWord_8214986).sum := by decide
  have hdescent : baseEnd_8214986 < baseStart_8214986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8214986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215009 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_8215009 : Nat := 118140960795 + 8215009 * 2 ^ 59
def prefixEnd_8215009 : Nat := 4983230072969 + 3 ^ 40 * 8215009 * 2
def baseEnd_8215009 : Nat := 4218248198011354473207367

theorem tailTrace_8215009 : CollatzResearch.WordTrace tailWord_8215009 prefixEnd_8215009 4218248198011354473207367 := by
  unfold tailWord_8215009
  simp only [CollatzResearch.WordTrace]
  refine ⟨299625993495432879682832081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199750662330288586455221387 299625993495432879682832081)
  ·
    refine ⟨224719495121574659762124061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299625993495432879682832081 224719495121574659762124061)
    ·
      refine ⟨84269810670590497410796523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224719495121574659762124061 84269810670590497410796523)
      ·
        refine ⟨126404716005885746116194785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84269810670590497410796523 126404716005885746116194785)
        ·
          refine ⟨94803537004414309587146089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126404716005885746116194785 94803537004414309587146089)
          ·
            refine ⟨71102652753310732190359567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94803537004414309587146089 71102652753310732190359567)
            ·
              refine ⟨106653979129966098285539351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71102652753310732190359567 106653979129966098285539351)
              ·
                refine ⟨159980968694949147428309027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106653979129966098285539351 159980968694949147428309027)
                ·
                  refine ⟨239971453042423721142463541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159980968694949147428309027 239971453042423721142463541)
                  ·
                    refine ⟨22497323722727223857105957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239971453042423721142463541 22497323722727223857105957)
                    ·
                      refine ⟨4218248198011354473207367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22497323722727223857105957 4218248198011354473207367)
                      ·
                        rfl

theorem cell23_8215009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_8215009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215009 prefixEnd_8215009 := by exact prefixLift 8215009
  have htrace : WordTrace (prefixWord ++ tailWord_8215009) baseStart_8215009 baseEnd_8215009 := by
    simpa [prefixWord, tailWord_8215009, baseEnd_8215009] using wordTrace_append hprefix tailTrace_8215009
  have hstable : (prefixWord ++ tailWord_8215009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215009).length < 2 ^ (prefixWord ++ tailWord_8215009).sum := by decide
  have hdescent : baseEnd_8215009 < baseStart_8215009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215010 : List Nat := [3, 3, 3, 2, 1, 2, 1, 8]
def baseStart_8215010 : Nat := 118140960795 + 8215010 * 2 ^ 59
def prefixEnd_8215010 : Nat := 4983230072969 + 3 ^ 40 * 8215010 * 2
def baseEnd_8215010 : Nat := 156231433758963295159069

theorem tailTrace_8215010 : CollatzResearch.WordTrace tailWord_8215010 prefixEnd_8215010 156231433758963295159069 := by
  unfold tailWord_8215010
  simp only [CollatzResearch.WordTrace]
  refine ⟨74906507492107314213404621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199750686645619504569078989 74906507492107314213404621)
  ·
    refine ⟨28089940309540242830026733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74906507492107314213404621 28089940309540242830026733)
    ·
      refine ⟨10533727616077591061260025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28089940309540242830026733 10533727616077591061260025)
      ·
        refine ⟨7900295712058193295945019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10533727616077591061260025 7900295712058193295945019)
        ·
          refine ⟨11850443568087289943917529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7900295712058193295945019 11850443568087289943917529)
          ·
            refine ⟨8887832676065467457938147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11850443568087289943917529 8887832676065467457938147)
            ·
              refine ⟨13331749014098201186907221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887832676065467457938147 13331749014098201186907221)
              ·
                refine ⟨156231433758963295159069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13331749014098201186907221 156231433758963295159069)
                ·
                  rfl

theorem cell23_8215010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_8215010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215010 prefixEnd_8215010 := by exact prefixLift 8215010
  have htrace : WordTrace (prefixWord ++ tailWord_8215010) baseStart_8215010 baseEnd_8215010 := by
    simpa [prefixWord, tailWord_8215010, baseEnd_8215010] using wordTrace_append hprefix tailTrace_8215010
  have hstable : (prefixWord ++ tailWord_8215010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215010).length < 2 ^ (prefixWord ++ tailWord_8215010).sum := by decide
  have hdescent : baseEnd_8215010 < baseStart_8215010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215019 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 6]
def baseStart_8215019 : Nat := 118140960795 + 8215019 * 2 ^ 59
def prefixEnd_8215019 : Nat := 4983230072969 + 3 ^ 40 * 8215019 * 2
def baseEnd_8215019 : Nat := 1406084444272633144694107

theorem tailTrace_8215019 : CollatzResearch.WordTrace tailWord_8215019 prefixEnd_8215019 1406084444272633144694107 := by
  unfold tailWord_8215019
  simp only [CollatzResearch.WordTrace]
  refine ⟨299626358225396651390696111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199750905483597767593797407 299626358225396651390696111)
  ·
    refine ⟨449439537338094977086044167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299626358225396651390696111 449439537338094977086044167)
    ·
      refine ⟨674159306007142465629066251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449439537338094977086044167 674159306007142465629066251)
      ·
        refine ⟨1011238959010713698443599377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674159306007142465629066251 1011238959010713698443599377)
        ·
          refine ⟨758429219258035273832699533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011238959010713698443599377 758429219258035273832699533)
          ·
            refine ⟨284410957221763227687262325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758429219258035273832699533 284410957221763227687262325)
            ·
              refine ⟨26663527239540302595680843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284410957221763227687262325 26663527239540302595680843)
              ·
                refine ⟨39995290859310453893521265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26663527239540302595680843 39995290859310453893521265)
                ·
                  refine ⟨29996468144482840420140949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39995290859310453893521265 29996468144482840420140949)
                  ·
                    refine ⟨1406084444272633144694107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29996468144482840420140949 1406084444272633144694107)
                    ·
                      rfl

theorem cell23_8215019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_8215019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215019 prefixEnd_8215019 := by exact prefixLift 8215019
  have htrace : WordTrace (prefixWord ++ tailWord_8215019) baseStart_8215019 baseEnd_8215019 := by
    simpa [prefixWord, tailWord_8215019, baseEnd_8215019] using wordTrace_append hprefix tailTrace_8215019
  have hstable : (prefixWord ++ tailWord_8215019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215019).length < 2 ^ (prefixWord ++ tailWord_8215019).sum := by decide
  have hdescent : baseEnd_8215019 < baseStart_8215019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215030 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_8215030 : Nat := 118140960795 + 8215030 * 2 ^ 59
def prefixEnd_8215030 : Nat := 4983230072969 + 3 ^ 40 * 8215030 * 2
def baseEnd_8215030 : Nat := 4218258981105098891044771

theorem tailTrace_8215030 : CollatzResearch.WordTrace tailWord_8215030 prefixEnd_8215030 4218258981105098891044771 := by
  unfold tailWord_8215030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18726672464272300016834159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199751172952237866846231029 18726672464272300016834159)
  ·
    refine ⟨28090008696408450025251239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18726672464272300016834159 28090008696408450025251239)
    ·
      refine ⟨42135013044612675037876859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28090008696408450025251239 42135013044612675037876859)
      ·
        refine ⟨63202519566919012556815289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42135013044612675037876859 63202519566919012556815289)
        ·
          refine ⟨47401889675189259417611467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63202519566919012556815289 47401889675189259417611467)
          ·
            refine ⟨71102834512783889126417201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47401889675189259417611467 71102834512783889126417201)
            ·
              refine ⟨53327125884587916844812901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71102834512783889126417201 53327125884587916844812901)
              ·
                refine ⟨9998836103360234408402419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53327125884587916844812901 9998836103360234408402419)
                ·
                  refine ⟨14998254155040351612603629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9998836103360234408402419 14998254155040351612603629)
                  ·
                    refine ⟨5624345308140131854726361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14998254155040351612603629 5624345308140131854726361)
                    ·
                      refine ⟨4218258981105098891044771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624345308140131854726361 4218258981105098891044771)
                      ·
                        rfl

theorem cell23_8215030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_8215030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215030 prefixEnd_8215030 := by exact prefixLift 8215030
  have htrace : WordTrace (prefixWord ++ tailWord_8215030) baseStart_8215030 baseEnd_8215030 := by
    simpa [prefixWord, tailWord_8215030, baseEnd_8215030] using wordTrace_append hprefix tailTrace_8215030
  have hstable : (prefixWord ++ tailWord_8215030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215030).length < 2 ^ (prefixWord ++ tailWord_8215030).sum := by decide
  have hdescent : baseEnd_8215030 < baseStart_8215030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215039 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_8215039 : Nat := 118140960795 + 8215039 * 2 ^ 59
def prefixEnd_8215039 : Nat := 4983230072969 + 3 ^ 40 * 8215039 * 2
def baseEnd_8215039 : Nat := 4218263602430989355832229

theorem tailTrace_8215039 : CollatzResearch.WordTrace tailWord_8215039 prefixEnd_8215039 4218263602430989355832229 := by
  unfold tailWord_8215039
  simp only [CollatzResearch.WordTrace]
  refine ⟨299627087685324194806424171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199751391790216129870949447 299627087685324194806424171)
  ·
    refine ⟨449440631527986292209636257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299627087685324194806424171 449440631527986292209636257)
    ·
      refine ⟨337080473645989719157227193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449440631527986292209636257 337080473645989719157227193)
      ·
        refine ⟨252810355234492289367920395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337080473645989719157227193 252810355234492289367920395)
        ·
          refine ⟨379215532851738434051880593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252810355234492289367920395 379215532851738434051880593)
          ·
            refine ⟨284411649638803825538910445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379215532851738434051880593 284411649638803825538910445)
            ·
              refine ⟨106654368614551434577091417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284411649638803825538910445 106654368614551434577091417)
              ·
                refine ⟨79990776460913575932818563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106654368614551434577091417 79990776460913575932818563)
                ·
                  refine ⟨119986164691370363899227845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79990776460913575932818563 119986164691370363899227845)
                  ·
                    refine ⟨22497405879631943231105221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119986164691370363899227845 22497405879631943231105221)
                    ·
                      refine ⟨4218263602430989355832229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22497405879631943231105221 4218263602430989355832229)
                      ·
                        rfl

theorem cell23_8215039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_8215039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215039 prefixEnd_8215039 := by exact prefixLift 8215039
  have htrace : WordTrace (prefixWord ++ tailWord_8215039) baseStart_8215039 baseEnd_8215039 := by
    simpa [prefixWord, tailWord_8215039, baseEnd_8215039] using wordTrace_append hprefix tailTrace_8215039
  have hstable : (prefixWord ++ tailWord_8215039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215039).length < 2 ^ (prefixWord ++ tailWord_8215039).sum := by decide
  have hdescent : baseEnd_8215039 < baseStart_8215039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215043 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 4, 2, 2]
def baseStart_8215043 : Nat := 118140960795 + 8215043 * 2 ^ 59
def prefixEnd_8215043 : Nat := 4983230072969 + 3 ^ 40 * 8215043 * 2
def baseEnd_8215043 : Nat := 4218265656353607340182211

theorem tailTrace_8215043 : CollatzResearch.WordTrace tailWord_8215043 prefixEnd_8215043 4218265656353607340182211 := by
  unfold tailWord_8215043
  simp only [CollatzResearch.WordTrace]
  refine ⟨299627233577309703489569783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199751489051539802326379855 299627233577309703489569783)
  ·
    refine ⟨449440850365964555234354675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299627233577309703489569783 449440850365964555234354675)
    ·
      refine ⟨674161275548946832851532013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449440850365964555234354675 674161275548946832851532013)
      ·
        refine ⟨252810478330855062319324505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674161275548946832851532013 252810478330855062319324505)
        ·
          refine ⟨189607858748141296739493379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252810478330855062319324505 189607858748141296739493379)
          ·
            refine ⟨284411788122211945109240069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189607858748141296739493379 284411788122211945109240069)
            ·
              refine ⟨53327210272914739707982513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284411788122211945109240069 53327210272914739707982513)
              ·
                refine ⟨39995407704686054780986885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53327210272914739707982513 39995407704686054780986885)
                ·
                  refine ⟨7499138944628635271435041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39995407704686054780986885 7499138944628635271435041)
                  ·
                    refine ⟨5624354208471476453576281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7499138944628635271435041 5624354208471476453576281)
                    ·
                      refine ⟨4218265656353607340182211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5624354208471476453576281 4218265656353607340182211)
                      ·
                        rfl

theorem cell23_8215043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_8215043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215043 prefixEnd_8215043 := by exact prefixLift 8215043
  have htrace : WordTrace (prefixWord ++ tailWord_8215043) baseStart_8215043 baseEnd_8215043 := by
    simpa [prefixWord, tailWord_8215043, baseEnd_8215043] using wordTrace_append hprefix tailTrace_8215043
  have hstable : (prefixWord ++ tailWord_8215043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215043).length < 2 ^ (prefixWord ++ tailWord_8215043).sum := by decide
  have hdescent : baseEnd_8215043 < baseStart_8215043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215096 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_8215096 : Nat := 118140960795 + 8215096 * 2 ^ 59
def prefixEnd_8215096 : Nat := 4983230072969 + 3 ^ 40 * 8215096 * 2
def baseEnd_8215096 : Nat := 1406097623609431877606489

theorem tailTrace_8215096 : CollatzResearch.WordTrace tailWord_8215096 prefixEnd_8215096 1406097623609431877606489 := by
  unfold tailWord_8215096
  simp only [CollatzResearch.WordTrace]
  refine ⟨149814583323058846770624571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199752777764078462360832761 149814583323058846770624571)
  ·
    refine ⟨224721874984588270155936857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149814583323058846770624571 224721874984588270155936857)
    ·
      refine ⟨168541406238441202616952643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224721874984588270155936857 168541406238441202616952643)
      ·
        refine ⟨252812109357661803925428965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168541406238441202616952643 252812109357661803925428965)
        ·
          refine ⟨47402270504561588236017931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252812109357661803925428965 47402270504561588236017931)
          ·
            refine ⟨71103405756842382354026897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47402270504561588236017931 71103405756842382354026897)
            ·
              refine ⟨53327554317631786765520173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71103405756842382354026897 53327554317631786765520173)
              ·
                refine ⟨19997832869111920037070065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53327554317631786765520173 19997832869111920037070065)
                ·
                  refine ⟨14998374651833940027802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19997832869111920037070065 14998374651833940027802549)
                  ·
                    refine ⟨1406097623609431877606489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14998374651833940027802549 1406097623609431877606489)
                    ·
                      rfl

theorem cell23_8215096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_8215096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215096 prefixEnd_8215096 := by exact prefixLift 8215096
  have htrace : WordTrace (prefixWord ++ tailWord_8215096) baseStart_8215096 baseEnd_8215096 := by
    simpa [prefixWord, tailWord_8215096, baseEnd_8215096] using wordTrace_append hprefix tailTrace_8215096
  have hstable : (prefixWord ++ tailWord_8215096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215096).length < 2 ^ (prefixWord ++ tailWord_8215096).sum := by decide
  have hdescent : baseEnd_8215096 < baseStart_8215096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8215100 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 5]
def baseStart_8215100 : Nat := 118140960795 + 8215100 * 2 ^ 59
def prefixEnd_8215100 : Nat := 4983230072969 + 3 ^ 40 * 8215100 * 2
def baseEnd_8215100 : Nat := 468699436083434846352161

theorem tailTrace_8215100 : CollatzResearch.WordTrace tailWord_8215100 prefixEnd_8215100 468699436083434846352161 := by
  unfold tailWord_8215100
  simp only [CollatzResearch.WordTrace]
  refine ⟨149814656269051601112197377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199752875025402134816263169 149814656269051601112197377)
  ·
    refine ⟨112360992201788700834148033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149814656269051601112197377 112360992201788700834148033)
    ·
      refine ⟨84270744151341525625611025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112360992201788700834148033 84270744151341525625611025)
      ·
        refine ⟨63203058113506144219208269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84270744151341525625611025 63203058113506144219208269)
        ·
          refine ⟨23701146792564804082203101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63203058113506144219208269 23701146792564804082203101)
          ·
            refine ⟨8887930047211801530826163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23701146792564804082203101 8887930047211801530826163)
            ·
              refine ⟨13331895070817702296239245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8887930047211801530826163 13331895070817702296239245)
              ·
                refine ⟨4999460651556638361089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13331895070817702296239245 4999460651556638361089717)
                ·
                  refine ⟨468699436083434846352161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999460651556638361089717 468699436083434846352161)
                  ·
                    rfl

theorem cell23_8215100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_8215100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8215100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8215100 prefixEnd_8215100 := by exact prefixLift 8215100
  have htrace : WordTrace (prefixWord ++ tailWord_8215100) baseStart_8215100 baseEnd_8215100 := by
    simpa [prefixWord, tailWord_8215100, baseEnd_8215100] using wordTrace_append hprefix tailTrace_8215100
  have hstable : (prefixWord ++ tailWord_8215100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8215100).length < 2 ^ (prefixWord ++ tailWord_8215100).sum := by decide
  have hdescent : baseEnd_8215100 < baseStart_8215100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8215100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
