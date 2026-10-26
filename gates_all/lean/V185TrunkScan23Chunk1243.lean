import V185TrunkScan23Chunk1242

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7363571 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 6]
def baseStart_7363571 : Nat := 118140960795 + 7363571 * 2 ^ 59
def prefixEnd_7363571 : Nat := 4983230072969 + 3 ^ 40 * 7363571 * 2
def baseEnd_7363571 : Nat := 1260350418836171576099353

theorem tailTrace_7363571 : CollatzResearch.WordTrace tailWord_7363571 prefixEnd_7363571 1260350418836171576099353 := by
  unfold tailWord_7363571
  simp only [CollatzResearch.WordTrace]
  refine ⟨268571498406047339649434567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179047665604031559766289711 268571498406047339649434567)
  ·
    refine ⟨402857247609071009474151851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268571498406047339649434567 402857247609071009474151851)
    ·
      refine ⟨604285871413606514211227777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402857247609071009474151851 604285871413606514211227777)
      ·
        refine ⟨453214403560204885658420833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604285871413606514211227777 453214403560204885658420833)
        ·
          refine ⟨339910802670153664243815625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453214403560204885658420833 339910802670153664243815625)
          ·
            refine ⟨254933102002615248182861719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339910802670153664243815625 254933102002615248182861719)
            ·
              refine ⟨382399653003922872274292579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254933102002615248182861719 382399653003922872274292579)
              ·
                refine ⟨573599479505884308411438869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382399653003922872274292579 573599479505884308411438869)
                ·
                  refine ⟨26887475601838326956786197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 573599479505884308411438869 26887475601838326956786197)
                  ·
                    refine ⟨1260350418836171576099353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26887475601838326956786197 1260350418836171576099353)
                    ·
                      rfl

theorem cell23_7363571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_7363571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363571 prefixEnd_7363571 := by exact prefixLift 7363571
  have htrace : WordTrace (prefixWord ++ tailWord_7363571) baseStart_7363571 baseEnd_7363571 := by
    simpa [prefixWord, tailWord_7363571, baseEnd_7363571] using wordTrace_append hprefix tailTrace_7363571
  have hstable : (prefixWord ++ tailWord_7363571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363571).length < 2 ^ (prefixWord ++ tailWord_7363571).sum := by decide
  have hdescent : baseEnd_7363571 < baseStart_7363571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363601 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 11]
def baseStart_7363601 : Nat := 118140960795 + 7363601 * 2 ^ 59
def prefixEnd_7363601 : Nat := 4983230072969 + 3 ^ 40 * 7363601 * 2
def baseEnd_7363601 : Nat := 420118517880905512324769

theorem tailTrace_7363601 : CollatzResearch.WordTrace tailWord_7363601 prefixEnd_7363601 420118517880905512324769 := by
  unfold tailWord_7363601
  simp only [CollatzResearch.WordTrace]
  refine ⟨268572592595938654773026657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179048395063959103182017771 268572592595938654773026657)
  ·
    refine ⟨201429444446953991079769993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268572592595938654773026657 201429444446953991079769993)
    ·
      refine ⟨151072083335215493309827495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201429444446953991079769993 151072083335215493309827495)
      ·
        refine ⟨226608125002823239964741243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151072083335215493309827495 226608125002823239964741243)
        ·
          refine ⟨339912187504234859947111865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226608125002823239964741243 339912187504234859947111865)
          ·
            refine ⟨254934140628176144960333899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339912187504234859947111865 254934140628176144960333899)
            ·
              refine ⟨382401210942264217440500849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254934140628176144960333899 382401210942264217440500849)
              ·
                refine ⟨286800908206698163080375637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382401210942264217440500849 286800908206698163080375637)
                ·
                  refine ⟨420118517880905512324769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 286800908206698163080375637 420118517880905512324769)
                  ·
                    rfl

theorem cell23_7363601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_7363601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363601 prefixEnd_7363601 := by exact prefixLift 7363601
  have htrace : WordTrace (prefixWord ++ tailWord_7363601) baseStart_7363601 baseEnd_7363601 := by
    simpa [prefixWord, tailWord_7363601, baseEnd_7363601] using wordTrace_append hprefix tailTrace_7363601
  have hstable : (prefixWord ++ tailWord_7363601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363601).length < 2 ^ (prefixWord ++ tailWord_7363601).sum := by decide
  have hdescent : baseEnd_7363601 < baseStart_7363601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363608 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7363608 : Nat := 118140960795 + 7363608 * 2 ^ 59
def prefixEnd_7363608 : Nat := 4983230072969 + 3 ^ 40 * 7363608 * 2
def baseEnd_7363608 : Nat := 3781070255292731083535389

theorem tailTrace_7363608 : CollatzResearch.WordTrace tailWord_7363608 prefixEnd_7363608 3781070255292731083535389 := by
  unfold tailWord_7363608
  simp only [CollatzResearch.WordTrace]
  refine ⟨134286423953456647484265739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179048565271275529979020985 134286423953456647484265739)
  ·
    refine ⟨201429635930184971226398609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134286423953456647484265739 201429635930184971226398609)
    ·
      refine ⟨151072226947638728419798957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201429635930184971226398609 151072226947638728419798957)
      ·
        refine ⟨56652085105364523157424609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151072226947638728419798957 56652085105364523157424609)
        ·
          refine ⟨42489063829023392368068457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56652085105364523157424609 42489063829023392368068457)
          ·
            refine ⟨31866797871767544276051343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42489063829023392368068457 31866797871767544276051343)
            ·
              refine ⟨47800196807651316414077015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31866797871767544276051343 47800196807651316414077015)
              ·
                refine ⟨71700295211476974621115523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47800196807651316414077015 71700295211476974621115523)
                ·
                  refine ⟨107550442817215461931673285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71700295211476974621115523 107550442817215461931673285)
                  ·
                    refine ⟨20165708028227899112188741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107550442817215461931673285 20165708028227899112188741)
                    ·
                      refine ⟨3781070255292731083535389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20165708028227899112188741 3781070255292731083535389)
                      ·
                        rfl

theorem cell23_7363608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7363608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363608 prefixEnd_7363608 := by exact prefixLift 7363608
  have htrace : WordTrace (prefixWord ++ tailWord_7363608) baseStart_7363608 baseEnd_7363608 := by
    simpa [prefixWord, tailWord_7363608, baseEnd_7363608] using wordTrace_append hprefix tailTrace_7363608
  have hstable : (prefixWord ++ tailWord_7363608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363608).length < 2 ^ (prefixWord ++ tailWord_7363608).sum := by decide
  have hdescent : baseEnd_7363608 < baseStart_7363608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363611 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_7363611 : Nat := 118140960795 + 7363611 * 2 ^ 59
def prefixEnd_7363611 : Nat := 4983230072969 + 3 ^ 40 * 7363611 * 2
def baseEnd_7363611 : Nat := 3781071795734694571797875

theorem tailTrace_7363611 : CollatzResearch.WordTrace tailWord_7363611 prefixEnd_7363611 3781071795734694571797875 := by
  unfold tailWord_7363611
  simp only [CollatzResearch.WordTrace]
  refine ⟨268572957325902426480890687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179048638217268284320593791 268572957325902426480890687)
  ·
    refine ⟨402859435988853639721336031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268572957325902426480890687 402859435988853639721336031)
    ·
      refine ⟨604289153983280459582004047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402859435988853639721336031 604289153983280459582004047)
      ·
        refine ⟨906433730974920689373006071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604289153983280459582004047 906433730974920689373006071)
        ·
          refine ⟨1359650596462381034059509107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906433730974920689373006071 1359650596462381034059509107)
          ·
            refine ⟨2039475894693571551089263661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359650596462381034059509107 2039475894693571551089263661)
            ·
              refine ⟨764803460510089331658473873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039475894693571551089263661 764803460510089331658473873)
              ·
                refine ⟨573602595382566998743855405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764803460510089331658473873 573602595382566998743855405)
                ·
                  refine ⟨215100973268462624528945777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 573602595382566998743855405 215100973268462624528945777)
                  ·
                    refine ⟨161325729951346968396709333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215100973268462624528945777 161325729951346968396709333)
                    ·
                      refine ⟨3781071795734694571797875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161325729951346968396709333 3781071795734694571797875)
                      ·
                        rfl

theorem cell23_7363611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_7363611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363611 prefixEnd_7363611 := by exact prefixLift 7363611
  have htrace : WordTrace (prefixWord ++ tailWord_7363611) baseStart_7363611 baseEnd_7363611 := by
    simpa [prefixWord, tailWord_7363611, baseEnd_7363611] using wordTrace_append hprefix tailTrace_7363611
  have hstable : (prefixWord ++ tailWord_7363611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363611).length < 2 ^ (prefixWord ++ tailWord_7363611).sum := by decide
  have hdescent : baseEnd_7363611 < baseStart_7363611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363618 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_7363618 : Nat := 118140960795 + 7363618 * 2 ^ 59
def prefixEnd_7363618 : Nat := 4983230072969 + 3 ^ 40 * 7363618 * 2
def baseEnd_7363618 : Nat := 420119487788808449378927

theorem tailTrace_7363618 : CollatzResearch.WordTrace tailWord_7363618 prefixEnd_7363618 420119487788808449378927 := by
  unfold tailWord_7363618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67143303159219266669098877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179048808424584711117597005 67143303159219266669098877)
  ·
    refine ⟨25178738684707225000912079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67143303159219266669098877 25178738684707225000912079)
    ·
      refine ⟨37768108027060837501368119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25178738684707225000912079 37768108027060837501368119)
      ·
        refine ⟨56652162040591256252052179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37768108027060837501368119 56652162040591256252052179)
        ·
          refine ⟨84978243060886884378078269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56652162040591256252052179 84978243060886884378078269)
          ·
            refine ⟨31866841147832581641779351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84978243060886884378078269 31866841147832581641779351)
            ·
              refine ⟨47800261721748872462669027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31866841147832581641779351 47800261721748872462669027)
              ·
                refine ⟨71700392582623308694003541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47800261721748872462669027 71700392582623308694003541)
                ·
                  refine ⟨420119487788808449378927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71700392582623308694003541 420119487788808449378927)
                  ·
                    rfl

theorem cell23_7363618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_7363618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363618 prefixEnd_7363618 := by exact prefixLift 7363618
  have htrace : WordTrace (prefixWord ++ tailWord_7363618) baseStart_7363618 baseEnd_7363618 := by
    simpa [prefixWord, tailWord_7363618, baseEnd_7363618] using wordTrace_append hprefix tailTrace_7363618
  have hstable : (prefixWord ++ tailWord_7363618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363618).length < 2 ^ (prefixWord ++ tailWord_7363618).sum := by decide
  have hdescent : baseEnd_7363618 < baseStart_7363618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363628 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_7363628 : Nat := 118140960795 + 7363628 * 2 ^ 59
def prefixEnd_7363628 : Nat := 4983230072969 + 3 ^ 40 * 7363628 * 2
def baseEnd_7363628 : Nat := 3781080524905821005285297

theorem tailTrace_7363628 : CollatzResearch.WordTrace tailWord_7363628 prefixEnd_7363628 3781080524905821005285297 := by
  unfold tailWord_7363628
  simp only [CollatzResearch.WordTrace]
  refine ⟨134286788683420419192129769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179049051577893892256173025 134286788683420419192129769)
  ·
    refine ⟨100715091512565314394097327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134286788683420419192129769 100715091512565314394097327)
    ·
      refine ⟨151072637268847971591145991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100715091512565314394097327 151072637268847971591145991)
      ·
        refine ⟨226608955903271957386718987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151072637268847971591145991 226608955903271957386718987)
        ·
          refine ⟨339913433854907936080078481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226608955903271957386718987 339913433854907936080078481)
          ·
            refine ⟨254935075391180952060058861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339913433854907936080078481 254935075391180952060058861)
            ·
              refine ⟨95600653271692857022522073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254935075391180952060058861 95600653271692857022522073)
              ·
                refine ⟨71700489953769642766891555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95600653271692857022522073 71700489953769642766891555)
                ·
                  refine ⟨107550734930654464150337333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71700489953769642766891555 107550734930654464150337333)
                  ·
                    refine ⟨10082881399748856014094125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107550734930654464150337333 10082881399748856014094125)
                    ·
                      refine ⟨3781080524905821005285297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082881399748856014094125 3781080524905821005285297)
                      ·
                        rfl

theorem cell23_7363628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_7363628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363628 prefixEnd_7363628 := by exact prefixLift 7363628
  have htrace : WordTrace (prefixWord ++ tailWord_7363628) baseStart_7363628 baseEnd_7363628 := by
    simpa [prefixWord, tailWord_7363628, baseEnd_7363628] using wordTrace_append hprefix tailTrace_7363628
  have hstable : (prefixWord ++ tailWord_7363628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363628).length < 2 ^ (prefixWord ++ tailWord_7363628).sum := by decide
  have hdescent : baseEnd_7363628 < baseStart_7363628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363645 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7363645 : Nat := 118140960795 + 7363645 * 2 ^ 59
def prefixEnd_7363645 : Nat := 4983230072969 + 3 ^ 40 * 7363645 * 2
def baseEnd_7363645 : Nat := 3781089254076947438772719

theorem tailTrace_7363645 : CollatzResearch.WordTrace tailWord_7363645 prefixEnd_7363645 3781089254076947438772719 := by
  unfold tailWord_7363645
  simp only [CollatzResearch.WordTrace]
  refine ⟨268574197407779250287628389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179049464938519500191752259 268574197407779250287628389)
  ·
    refine ⟨50357662013958609428930323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268574197407779250287628389 50357662013958609428930323)
    ·
      refine ⟨75536493020937914143395485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50357662013958609428930323 75536493020937914143395485)
      ·
        refine ⟨28326184882851717803773307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75536493020937914143395485 28326184882851717803773307)
        ·
          refine ⟨42489277324277576705659961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28326184882851717803773307 42489277324277576705659961)
          ·
            refine ⟨31866957993208182529244971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42489277324277576705659961 31866957993208182529244971)
            ·
              refine ⟨47800436989812273793867457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31866957993208182529244971 47800436989812273793867457)
              ·
                refine ⟨35850327742359205345400593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47800436989812273793867457 35850327742359205345400593)
                ·
                  refine ⟨26887745806769404009050445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35850327742359205345400593 26887745806769404009050445)
                  ·
                    refine ⟨10082904677538526503393917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26887745806769404009050445 10082904677538526503393917)
                    ·
                      refine ⟨3781089254076947438772719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10082904677538526503393917 3781089254076947438772719)
                      ·
                        rfl

theorem cell23_7363645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7363645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363645 prefixEnd_7363645 := by exact prefixLift 7363645
  have htrace : WordTrace (prefixWord ++ tailWord_7363645) baseStart_7363645 baseEnd_7363645 := by
    simpa [prefixWord, tailWord_7363645, baseEnd_7363645] using wordTrace_append hprefix tailTrace_7363645
  have hstable : (prefixWord ++ tailWord_7363645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363645).length < 2 ^ (prefixWord ++ tailWord_7363645).sum := by decide
  have hdescent : baseEnd_7363645 < baseStart_7363645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363646 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7363646 : Nat := 118140960795 + 7363646 * 2 ^ 59
def prefixEnd_7363646 : Nat := 4983230072969 + 3 ^ 40 * 7363646 * 2
def baseEnd_7363646 : Nat := 3781089767557601934860215

theorem tailTrace_7363646 : CollatzResearch.WordTrace tailWord_7363646 prefixEnd_7363646 3781089767557601934860215 := by
  unfold tailWord_7363646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33571779235096953432301849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179049489253850418305609861 33571779235096953432301849)
  ·
    refine ⟨25178834426322715074226387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33571779235096953432301849 25178834426322715074226387)
    ·
      refine ⟨37768251639484072611339581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25178834426322715074226387 37768251639484072611339581)
      ·
        refine ⟨14163094364806527229252343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37768251639484072611339581 14163094364806527229252343)
        ·
          refine ⟨21244641547209790843878515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163094364806527229252343 21244641547209790843878515)
          ·
            refine ⟨31866962320814686265817773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21244641547209790843878515 31866962320814686265817773)
            ·
              refine ⟨11950110870305507349681665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31866962320814686265817773 11950110870305507349681665)
              ·
                refine ⟨8962583152729130512261249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11950110870305507349681665 8962583152729130512261249)
                ·
                  refine ⟨6721937364546847884195937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962583152729130512261249 6721937364546847884195937)
                  ·
                    refine ⟨5041453023410135913146953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6721937364546847884195937 5041453023410135913146953)
                    ·
                      refine ⟨3781089767557601934860215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041453023410135913146953 3781089767557601934860215)
                      ·
                        rfl

theorem cell23_7363646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7363646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363646 prefixEnd_7363646 := by exact prefixLift 7363646
  have htrace : WordTrace (prefixWord ++ tailWord_7363646) baseStart_7363646 baseEnd_7363646 := by
    simpa [prefixWord, tailWord_7363646, baseEnd_7363646] using wordTrace_append hprefix tailTrace_7363646
  have hstable : (prefixWord ++ tailWord_7363646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363646).length < 2 ^ (prefixWord ++ tailWord_7363646).sum := by decide
  have hdescent : baseEnd_7363646 < baseStart_7363646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363648 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_7363648 : Nat := 118140960795 + 7363648 * 2 ^ 59
def prefixEnd_7363648 : Nat := 4983230072969 + 3 ^ 40 * 7363648 * 2
def baseEnd_7363648 : Nat := 1260363598172970309011735

theorem tailTrace_7363648 : CollatzResearch.WordTrace tailWord_7363648 prefixEnd_7363648 1260363598172970309011735 := by
  unfold tailWord_7363648
  simp only [CollatzResearch.WordTrace]
  refine ⟨134287153413384190899993799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179049537884512254533325065 134287153413384190899993799)
  ·
    refine ⟨201430730120076286349990699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134287153413384190899993799 201430730120076286349990699)
    ·
      refine ⟨302146095180114429524986049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201430730120076286349990699 302146095180114429524986049)
      ·
        refine ⟨226609571385085822143739537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302146095180114429524986049 226609571385085822143739537)
        ·
          refine ⟨169957178538814366607804653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226609571385085822143739537 169957178538814366607804653)
          ·
            refine ⟨63733941952055387477926745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169957178538814366607804653 63733941952055387477926745)
            ·
              refine ⟨47800456464041540608445059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63733941952055387477926745 47800456464041540608445059)
              ·
                refine ⟨71700684696062310912667589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47800456464041540608445059 71700684696062310912667589)
                ·
                  refine ⟨13443878380511683296125173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71700684696062310912667589 13443878380511683296125173)
                  ·
                    refine ⟨1260363598172970309011735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13443878380511683296125173 1260363598172970309011735)
                    ·
                      rfl

theorem cell23_7363648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_7363648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363648 prefixEnd_7363648 := by exact prefixLift 7363648
  have htrace : WordTrace (prefixWord ++ tailWord_7363648) baseStart_7363648 baseEnd_7363648 := by
    simpa [prefixWord, tailWord_7363648, baseEnd_7363648] using wordTrace_append hprefix tailTrace_7363648
  have hstable : (prefixWord ++ tailWord_7363648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363648).length < 2 ^ (prefixWord ++ tailWord_7363648).sum := by decide
  have hdescent : baseEnd_7363648 < baseStart_7363648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363658 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_7363658 : Nat := 118140960795 + 7363658 * 2 ^ 59
def prefixEnd_7363658 : Nat := 4983230072969 + 3 ^ 40 * 7363658 * 2
def baseEnd_7363658 : Nat := 3781095929325455887910159

theorem tailTrace_7363658 : CollatzResearch.WordTrace tailWord_7363658 prefixEnd_7363658 3781095929325455887910159 := by
  unfold tailWord_7363658
  simp only [CollatzResearch.WordTrace]
  refine ⟨67143667889183038376962907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179049781037821435671901085 67143667889183038376962907)
  ·
    refine ⟨100715501833774557565444361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67143667889183038376962907 100715501833774557565444361)
    ·
      refine ⟨75536626375330918174083271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100715501833774557565444361 75536626375330918174083271)
      ·
        refine ⟨113304939562996377261124907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75536626375330918174083271 113304939562996377261124907)
        ·
          refine ⟨169957409344494565891687361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113304939562996377261124907 169957409344494565891687361)
          ·
            refine ⟨127468057008370924418765521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169957409344494565891687361 127468057008370924418765521)
            ·
              refine ⟨95601042756278193314074141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127468057008370924418765521 95601042756278193314074141)
              ·
                refine ⟨35850391033604322492777803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95601042756278193314074141 35850391033604322492777803)
                ·
                  refine ⟨53775586550406483739166705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35850391033604322492777803 53775586550406483739166705)
                  ·
                    refine ⟨40331689912804862804375029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53775586550406483739166705 40331689912804862804375029)
                    ·
                      refine ⟨3781095929325455887910159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40331689912804862804375029 3781095929325455887910159)
                      ·
                        rfl

theorem cell23_7363658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_7363658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363658 prefixEnd_7363658 := by exact prefixLift 7363658
  have htrace : WordTrace (prefixWord ++ tailWord_7363658) baseStart_7363658 baseEnd_7363658 := by
    simpa [prefixWord, tailWord_7363658, baseEnd_7363658] using wordTrace_append hprefix tailTrace_7363658
  have hstable : (prefixWord ++ tailWord_7363658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363658).length < 2 ^ (prefixWord ++ tailWord_7363658).sum := by decide
  have hdescent : baseEnd_7363658 < baseStart_7363658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363685 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7363685 : Nat := 118140960795 + 7363685 * 2 ^ 59
def prefixEnd_7363685 : Nat := 4983230072969 + 3 ^ 40 * 7363685 * 2
def baseEnd_7363685 : Nat := 3781109793303127282272535

theorem tailTrace_7363685 : CollatzResearch.WordTrace tailWord_7363685 prefixEnd_7363685 3781109793303127282272535 := by
  unfold tailWord_7363685
  simp only [CollatzResearch.WordTrace]
  refine ⟨268575656327634337119084509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179050437551756224746056339 268575656327634337119084509)
  ·
    refine ⟨100715871122862876419656691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268575656327634337119084509 100715871122862876419656691)
    ·
      refine ⟨151073806684294314629485037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100715871122862876419656691 151073806684294314629485037)
      ·
        refine ⟨56652677506610367986056889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151073806684294314629485037 56652677506610367986056889)
        ·
          refine ⟨42489508129957775989542667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56652677506610367986056889 42489508129957775989542667)
          ·
            refine ⟨63734262194936663984314001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42489508129957775989542667 63734262194936663984314001)
            ·
              refine ⟨47800696646202497988235501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63734262194936663984314001 47800696646202497988235501)
              ·
                refine ⟨17925261242325936745588313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47800696646202497988235501 17925261242325936745588313)
                ·
                  refine ⟨13443945931744452559191235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17925261242325936745588313 13443945931744452559191235)
                  ·
                    refine ⟨20165918897616678838786853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13443945931744452559191235 20165918897616678838786853)
                    ·
                      refine ⟨3781109793303127282272535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20165918897616678838786853 3781109793303127282272535)
                      ·
                        rfl

theorem cell23_7363685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7363685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363685 prefixEnd_7363685 := by exact prefixLift 7363685
  have htrace : WordTrace (prefixWord ++ tailWord_7363685) baseStart_7363685 baseEnd_7363685 := by
    simpa [prefixWord, tailWord_7363685, baseEnd_7363685] using wordTrace_append hprefix tailTrace_7363685
  have hstable : (prefixWord ++ tailWord_7363685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363685).length < 2 ^ (prefixWord ++ tailWord_7363685).sum := by decide
  have hdescent : baseEnd_7363685 < baseStart_7363685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363702 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7363702 : Nat := 118140960795 + 7363702 * 2 ^ 59
def prefixEnd_7363702 : Nat := 4983230072969 + 3 ^ 40 * 7363702 * 2
def baseEnd_7363702 : Nat := 3781118522474253715759957

theorem tailTrace_7363702 : CollatzResearch.WordTrace tailWord_7363702 prefixEnd_7363702 3781118522474253715759957 := by
  unfold tailWord_7363702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16786017273035796813903335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179050850912381832681635573 16786017273035796813903335)
  ·
    refine ⟨25179025909553695220855003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16786017273035796813903335 25179025909553695220855003)
    ·
      refine ⟨37768538864330542831282505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25179025909553695220855003 37768538864330542831282505)
      ·
        refine ⟨28326404148247907123461879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37768538864330542831282505 28326404148247907123461879)
        ·
          refine ⟨42489606222371860685192819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28326404148247907123461879 42489606222371860685192819)
          ·
            refine ⟨63734409333557791027789229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42489606222371860685192819 63734409333557791027789229)
            ·
              refine ⟨23900403500084171635420961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63734409333557791027789229 23900403500084171635420961)
              ·
                refine ⟨17925302625063128726565721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23900403500084171635420961 17925302625063128726565721)
                ·
                  refine ⟨13443976968797346544924291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17925302625063128726565721 13443976968797346544924291)
                  ·
                    refine ⟨20165965453196019817386437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13443976968797346544924291 20165965453196019817386437)
                    ·
                      refine ⟨3781118522474253715759957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20165965453196019817386437 3781118522474253715759957)
                      ·
                        rfl

theorem cell23_7363702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7363702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363702 prefixEnd_7363702 := by exact prefixLift 7363702
  have htrace : WordTrace (prefixWord ++ tailWord_7363702) baseStart_7363702 baseEnd_7363702 := by
    simpa [prefixWord, tailWord_7363702, baseEnd_7363702] using wordTrace_append hprefix tailTrace_7363702
  have hstable : (prefixWord ++ tailWord_7363702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363702).length < 2 ^ (prefixWord ++ tailWord_7363702).sum := by decide
  have hdescent : baseEnd_7363702 < baseStart_7363702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363708 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 8]
def baseStart_7363708 : Nat := 118140960795 + 7363708 * 2 ^ 59
def prefixEnd_7363708 : Nat := 4983230072969 + 3 ^ 40 * 7363708 * 2
def baseEnd_7363708 : Nat := 420124622595353410253881

theorem tailTrace_7363708 : CollatzResearch.WordTrace tailWord_7363708 prefixEnd_7363708 420124622595353410253881 := by
  unfold tailWord_7363708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134288247603275506023585889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179050996804367341364781185 134288247603275506023585889)
  ·
    refine ⟨100716185702456629517689417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134288247603275506023585889 100716185702456629517689417)
    ·
      refine ⟨75537139276842472138267063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100716185702456629517689417 75537139276842472138267063)
      ·
        refine ⟨113305708915263708207400595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75537139276842472138267063 113305708915263708207400595)
        ·
          refine ⟨169958563372895562311100893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113305708915263708207400595 169958563372895562311100893)
          ·
            refine ⟨63734461264835835866662835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169958563372895562311100893 63734461264835835866662835)
            ·
              refine ⟨95601691897253753799994253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63734461264835835866662835 95601691897253753799994253)
              ·
                refine ⟨35850634461470157674997845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95601691897253753799994253 35850634461470157674997845)
                ·
                  refine ⟨420124622595353410253881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35850634461470157674997845 420124622595353410253881)
                  ·
                    rfl

theorem cell23_7363708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_7363708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363708 prefixEnd_7363708 := by exact prefixLift 7363708
  have htrace : WordTrace (prefixWord ++ tailWord_7363708) baseStart_7363708 baseEnd_7363708 := by
    simpa [prefixWord, tailWord_7363708, baseEnd_7363708] using wordTrace_append hprefix tailTrace_7363708
  have hstable : (prefixWord ++ tailWord_7363708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363708).length < 2 ^ (prefixWord ++ tailWord_7363708).sum := by decide
  have hdescent : baseEnd_7363708 < baseStart_7363708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363712 : List Nat := [2, 1, 1, 2, 1, 3, 2, 6, 1, 4]
def baseStart_7363712 : Nat := 118140960795 + 7363712 * 2 ^ 59
def prefixEnd_7363712 : Nat := 4983230072969 + 3 ^ 40 * 7363712 * 2
def baseEnd_7363712 : Nat := 1260374552426932892211637

theorem tailTrace_7363712 : CollatzResearch.WordTrace tailWord_7363712 prefixEnd_7363712 1260374552426932892211637 := by
  unfold tailWord_7363712
  simp only [CollatzResearch.WordTrace]
  refine ⟨134288320549268260365158695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179051094065691013820211593 134288320549268260365158695)
  ·
    refine ⟨201432480823902390547738043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134288320549268260365158695 201432480823902390547738043)
    ·
      refine ⟨302148721235853585821607065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201432480823902390547738043 302148721235853585821607065)
      ·
        refine ⟨226611540926890189366205299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302148721235853585821607065 226611540926890189366205299)
        ·
          refine ⟨339917311390335284049307949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226611540926890189366205299 339917311390335284049307949)
          ·
            refine ⟨127468991771375731518490481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339917311390335284049307949 127468991771375731518490481)
            ·
              refine ⟨95601743828531798638867861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127468991771375731518490481 95601743828531798638867861)
              ·
                refine ⟨4481331741962428061196931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95601743828531798638867861 4481331741962428061196931)
                ·
                  refine ⟨6721997612943642091795397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481331741962428061196931 6721997612943642091795397)
                  ·
                    refine ⟨1260374552426932892211637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6721997612943642091795397 1260374552426932892211637)
                    ·
                      rfl

theorem cell23_7363712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_7363712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363712 prefixEnd_7363712 := by exact prefixLift 7363712
  have htrace : WordTrace (prefixWord ++ tailWord_7363712) baseStart_7363712 baseEnd_7363712 := by
    simpa [prefixWord, tailWord_7363712, baseEnd_7363712] using wordTrace_append hprefix tailTrace_7363712
  have hstable : (prefixWord ++ tailWord_7363712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363712).length < 2 ^ (prefixWord ++ tailWord_7363712).sum := by decide
  have hdescent : baseEnd_7363712 < baseStart_7363712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363775 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_7363775 : Nat := 118140960795 + 7363775 * 2 ^ 59
def prefixEnd_7363775 : Nat := 4983230072969 + 3 ^ 40 * 7363775 * 2
def baseEnd_7363775 : Nat := 3781156006562031930147121

theorem tailTrace_7363775 : CollatzResearch.WordTrace tailWord_7363775 prefixEnd_7363775 3781156006562031930147121 := by
  unfold tailWord_7363775
  simp only [CollatzResearch.WordTrace]
  refine ⟨268578938897308282489860779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179052625931538854993240519 268578938897308282489860779)
  ·
    refine ⟨402868408345962423734791169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268578938897308282489860779 402868408345962423734791169)
    ·
      refine ⟨302151306259471817801093377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402868408345962423734791169 302151306259471817801093377)
      ·
        refine ⟨226613479694603863350820033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302151306259471817801093377 226613479694603863350820033)
        ·
          refine ⟨169960109770952897513115025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226613479694603863350820033 169960109770952897513115025)
          ·
            refine ⟨127470082328214673134836269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169960109770952897513115025 127470082328214673134836269)
            ·
              refine ⟨47801280873080502425563601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127470082328214673134836269 47801280873080502425563601)
              ·
                refine ⟨35850960654810376819172701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47801280873080502425563601 35850960654810376819172701)
                ·
                  refine ⟨13444110245553891307189763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35850960654810376819172701 13444110245553891307189763)
                  ·
                    refine ⟨20166165368330836960784645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13444110245553891307189763 20166165368330836960784645)
                    ·
                      refine ⟨3781156006562031930147121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20166165368330836960784645 3781156006562031930147121)
                      ·
                        rfl

theorem cell23_7363775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_7363775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363775 prefixEnd_7363775 := by exact prefixLift 7363775
  have htrace : WordTrace (prefixWord ++ tailWord_7363775) baseStart_7363775 baseEnd_7363775 := by
    simpa [prefixWord, tailWord_7363775, baseEnd_7363775] using wordTrace_append hprefix tailTrace_7363775
  have hstable : (prefixWord ++ tailWord_7363775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363775).length < 2 ^ (prefixWord ++ tailWord_7363775).sum := by decide
  have hdescent : baseEnd_7363775 < baseStart_7363775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363796 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7363796 : Nat := 118140960795 + 7363796 * 2 ^ 59
def prefixEnd_7363796 : Nat := 4983230072969 + 3 ^ 40 * 7363796 * 2
def baseEnd_7363796 : Nat := 3781166789655776347984525

theorem tailTrace_7363796 : CollatzResearch.WordTrace tailWord_7363796 prefixEnd_7363796 3781166789655776347984525 := by
  unfold tailWord_7363796
  simp only [CollatzResearch.WordTrace]
  refine ⟨134289852415116101538187621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179053136553488135384250161 134289852415116101538187621)
  ·
    refine ⟨25179347327834269038410179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134289852415116101538187621 25179347327834269038410179)
    ·
      refine ⟨37769020991751403557615269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25179347327834269038410179 37769020991751403557615269)
      ·
        refine ⟨7081691435953388167052863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37769020991751403557615269 7081691435953388167052863)
        ·
          refine ⟨10622537153930082250579295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081691435953388167052863 10622537153930082250579295)
          ·
            refine ⟨15933805730895123375868943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622537153930082250579295 15933805730895123375868943)
            ·
              refine ⟨23900708596342685063803415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15933805730895123375868943 23900708596342685063803415)
              ·
                refine ⟨35851062894514027595705123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23900708596342685063803415 35851062894514027595705123)
                ·
                  refine ⟨53776594341771041393557685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35851062894514027595705123 53776594341771041393557685)
                  ·
                    refine ⟨5041555719541035130646033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53776594341771041393557685 5041555719541035130646033)
                    ·
                      refine ⟨3781166789655776347984525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041555719541035130646033 3781166789655776347984525)
                      ·
                        rfl

theorem cell23_7363796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7363796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363796 prefixEnd_7363796 := by exact prefixLift 7363796
  have htrace : WordTrace (prefixWord ++ tailWord_7363796) baseStart_7363796 baseEnd_7363796 := by
    simpa [prefixWord, tailWord_7363796, baseEnd_7363796] using wordTrace_append hprefix tailTrace_7363796
  have hstable : (prefixWord ++ tailWord_7363796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363796).length < 2 ^ (prefixWord ++ tailWord_7363796).sum := by decide
  have hdescent : baseEnd_7363796 < baseStart_7363796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363809 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 1, 1, 4]
def baseStart_7363809 : Nat := 118140960795 + 7363809 * 2 ^ 59
def prefixEnd_7363809 : Nat := 4983230072969 + 3 ^ 40 * 7363809 * 2
def baseEnd_7363809 : Nat := 3781173464904284797121965

theorem tailTrace_7363809 : CollatzResearch.WordTrace tailWord_7363809 prefixEnd_7363809 3781173464904284797121965 := by
  unfold tailWord_7363809
  simp only [CollatzResearch.WordTrace]
  refine ⟨268580178979185106296598481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179053452652790070864398987 268580178979185106296598481)
  ·
    refine ⟨201435134234388829722448861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268580178979185106296598481 201435134234388829722448861)
    ·
      refine ⟨75538175337895811145918323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201435134234388829722448861 75538175337895811145918323)
      ·
        refine ⟨113307263006843716718877485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75538175337895811145918323 113307263006843716718877485)
        ·
          refine ⟨42490223627566393769579057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113307263006843716718877485 42490223627566393769579057)
          ·
            refine ⟨31867667720674795327184293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42490223627566393769579057 31867667720674795327184293)
            ·
              refine ⟨5975187697626524123847055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31867667720674795327184293 5975187697626524123847055)
              ·
                refine ⟨8962781546439786185770583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975187697626524123847055 8962781546439786185770583)
                ·
                  refine ⟨13444172319659679278655875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8962781546439786185770583 13444172319659679278655875)
                  ·
                    refine ⟨20166258479489518917983813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13444172319659679278655875 20166258479489518917983813)
                    ·
                      refine ⟨3781173464904284797121965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20166258479489518917983813 3781173464904284797121965)
                      ·
                        rfl

theorem cell23_7363809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_7363809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363809 prefixEnd_7363809 := by exact prefixLift 7363809
  have htrace : WordTrace (prefixWord ++ tailWord_7363809) baseStart_7363809 baseEnd_7363809 := by
    simpa [prefixWord, tailWord_7363809, baseEnd_7363809] using wordTrace_append hprefix tailTrace_7363809
  have hstable : (prefixWord ++ tailWord_7363809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363809).length < 2 ^ (prefixWord ++ tailWord_7363809).sum := by decide
  have hdescent : baseEnd_7363809 < baseStart_7363809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363819 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 2, 4]
def baseStart_7363819 : Nat := 118140960795 + 7363819 * 2 ^ 59
def prefixEnd_7363819 : Nat := 4983230072969 + 3 ^ 40 * 7363819 * 2
def baseEnd_7363819 : Nat := 1260392866570276585998973

theorem tailTrace_7363819 : CollatzResearch.WordTrace tailWord_7363819 prefixEnd_7363819 1260392866570276585998973 := by
  unfold tailWord_7363819
  simp only [CollatzResearch.WordTrace]
  refine ⟨268580543709148878004462511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179053695806099252002975007 268580543709148878004462511)
  ·
    refine ⟨402870815563723317006693767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268580543709148878004462511 402870815563723317006693767)
    ·
      refine ⟨604306223345584975510040651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402870815563723317006693767 604306223345584975510040651)
      ·
        refine ⟨906459335018377463265060977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604306223345584975510040651 906459335018377463265060977)
        ·
          refine ⟨679844501263783097448795733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906459335018377463265060977 679844501263783097448795733)
          ·
            refine ⟨7966927749184958173228075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 679844501263783097448795733 7966927749184958173228075)
            ·
              refine ⟨11950391623777437259842113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966927749184958173228075 11950391623777437259842113)
              ·
                refine ⟨8962793717833077944881585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11950391623777437259842113 8962793717833077944881585)
                ·
                  refine ⟨6722095288374808458661189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962793717833077944881585 6722095288374808458661189)
                  ·
                    refine ⟨1260392866570276585998973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722095288374808458661189 1260392866570276585998973)
                    ·
                      rfl

theorem cell23_7363819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 4].length) (baseStart_7363819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363819 prefixEnd_7363819 := by exact prefixLift 7363819
  have htrace : WordTrace (prefixWord ++ tailWord_7363819) baseStart_7363819 baseEnd_7363819 := by
    simpa [prefixWord, tailWord_7363819, baseEnd_7363819] using wordTrace_append hprefix tailTrace_7363819
  have hstable : (prefixWord ++ tailWord_7363819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363819).length < 2 ^ (prefixWord ++ tailWord_7363819).sum := by decide
  have hdescent : baseEnd_7363819 < baseStart_7363819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363836 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_7363836 : Nat := 118140960795 + 7363836 * 2 ^ 59
def prefixEnd_7363836 : Nat := 4983230072969 + 3 ^ 40 * 7363836 * 2
def baseEnd_7363836 : Nat := 1260395776293985397161447

theorem tailTrace_7363836 : CollatzResearch.WordTrace tailWord_7363836 prefixEnd_7363836 1260395776293985397161447 := by
  unfold tailWord_7363836
  simp only [CollatzResearch.WordTrace]
  refine ⟨134290581875043644953915681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179054109166724859938554241 134290581875043644953915681)
  ·
    refine ⟨100717936406282733715436761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134290581875043644953915681 100717936406282733715436761)
    ·
      refine ⟨75538452304712050286577571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100717936406282733715436761 75538452304712050286577571)
      ·
        refine ⟨113307678457068075429866357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75538452304712050286577571 113307678457068075429866357)
        ·
          refine ⟨10622594855350132071549971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113307678457068075429866357 10622594855350132071549971)
          ·
            refine ⟨15933892283025198107324957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622594855350132071549971 15933892283025198107324957)
            ·
              refine ⟨5975209606134449290246859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15933892283025198107324957 5975209606134449290246859)
              ·
                refine ⟨8962814409201673935370289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975209606134449290246859 8962814409201673935370289)
                ·
                  refine ⟨6722110806901255451527717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962814409201673935370289 6722110806901255451527717)
                  ·
                    refine ⟨1260395776293985397161447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722110806901255451527717 1260395776293985397161447)
                    ·
                      rfl

theorem cell23_7363836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_7363836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363836 prefixEnd_7363836 := by exact prefixLift 7363836
  have htrace : WordTrace (prefixWord ++ tailWord_7363836) baseStart_7363836 baseEnd_7363836 := by
    simpa [prefixWord, tailWord_7363836, baseEnd_7363836] using wordTrace_append hprefix tailTrace_7363836
  have hstable : (prefixWord ++ tailWord_7363836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363836).length < 2 ^ (prefixWord ++ tailWord_7363836).sum := by decide
  have hdescent : baseEnd_7363836 < baseStart_7363836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363892 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_7363892 : Nat := 118140960795 + 7363892 * 2 ^ 59
def prefixEnd_7363892 : Nat := 4983230072969 + 3 ^ 40 * 7363892 * 2
def baseEnd_7363892 : Nat := 1260405361266202657461361

theorem tailTrace_7363892 : CollatzResearch.WordTrace tailWord_7363892 prefixEnd_7363892 1260405361266202657461361 := by
  unfold tailWord_7363892
  simp only [CollatzResearch.WordTrace]
  refine ⟨134291603118942205735934965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179055470825256274314579953 134291603118942205735934965)
  ·
    refine ⟨12589837792400831787743903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134291603118942205735934965 12589837792400831787743903)
    ·
      refine ⟨18884756688601247681615855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12589837792400831787743903 18884756688601247681615855)
      ·
        refine ⟨28327135032901871522423783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18884756688601247681615855 28327135032901871522423783)
        ·
          refine ⟨42490702549352807283635675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28327135032901871522423783 42490702549352807283635675)
          ·
            refine ⟨63736053824029210925453513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42490702549352807283635675 63736053824029210925453513)
            ·
              refine ⟨47802040368021908194090135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63736053824029210925453513 47802040368021908194090135)
              ·
                refine ⟨71703060552032862291135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47802040368021908194090135 71703060552032862291135203)
                ·
                  refine ⟨107554590828049293436702805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71703060552032862291135203 107554590828049293436702805)
                  ·
                    refine ⟨1260405361266202657461361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107554590828049293436702805 1260405361266202657461361)
                    ·
                      rfl

theorem cell23_7363892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_7363892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363892 prefixEnd_7363892 := by exact prefixLift 7363892
  have htrace : WordTrace (prefixWord ++ tailWord_7363892) baseStart_7363892 baseEnd_7363892 := by
    simpa [prefixWord, tailWord_7363892, baseEnd_7363892] using wordTrace_append hprefix tailTrace_7363892
  have hstable : (prefixWord ++ tailWord_7363892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363892).length < 2 ^ (prefixWord ++ tailWord_7363892).sum := by decide
  have hdescent : baseEnd_7363892 < baseStart_7363892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363893 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_7363893 : Nat := 118140960795 + 7363893 * 2 ^ 59
def prefixEnd_7363893 : Nat := 4983230072969 + 3 ^ 40 * 7363893 * 2
def baseEnd_7363893 : Nat := 3781216597279262468471579

theorem tailTrace_7363893 : CollatzResearch.WordTrace tailWord_7363893 prefixEnd_7363893 3781216597279262468471579 := by
  unfold tailWord_7363893
  simp only [CollatzResearch.WordTrace]
  refine ⟨268583242710880788642656333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179055495140587192428437555 268583242710880788642656333)
  ·
    refine ⟨100718716016580295740996125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268583242710880788642656333 100718716016580295740996125)
    ·
      refine ⟨37769518506217610902873547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100718716016580295740996125 37769518506217610902873547)
      ·
        refine ⟨56654277759326416354310321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37769518506217610902873547 56654277759326416354310321)
        ·
          refine ⟨42490708319494812265732741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56654277759326416354310321 42490708319494812265732741)
          ·
            refine ⟨7967007809905277299824889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42490708319494812265732741 7967007809905277299824889)
            ·
              refine ⟨5975255857428957974868667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967007809905277299824889 5975255857428957974868667)
              ·
                refine ⟨8962883786143436962303001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975255857428957974868667 8962883786143436962303001)
                ·
                  refine ⟨6722162839607577721727251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962883786143436962303001 6722162839607577721727251)
                  ·
                    refine ⟨10083244259411366582590877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722162839607577721727251 10083244259411366582590877)
                    ·
                      refine ⟨3781216597279262468471579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083244259411366582590877 3781216597279262468471579)
                      ·
                        rfl

theorem cell23_7363893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_7363893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363893 prefixEnd_7363893 := by exact prefixLift 7363893
  have htrace : WordTrace (prefixWord ++ tailWord_7363893) baseStart_7363893 baseEnd_7363893 := by
    simpa [prefixWord, tailWord_7363893, baseEnd_7363893] using wordTrace_append hprefix tailTrace_7363893
  have hstable : (prefixWord ++ tailWord_7363893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363893).length < 2 ^ (prefixWord ++ tailWord_7363893).sum := by decide
  have hdescent : baseEnd_7363893 < baseStart_7363893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363902 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7363902 : Nat := 118140960795 + 7363902 * 2 ^ 59
def prefixEnd_7363902 : Nat := 4983230072969 + 3 ^ 40 * 7363902 * 2
def baseEnd_7363902 : Nat := 3781221218605152933259037

theorem tailTrace_7363902 : CollatzResearch.WordTrace tailWord_7363902 prefixEnd_7363902 3781221218605152933259037 := by
  unfold tailWord_7363902
  simp only [CollatzResearch.WordTrace]
  refine ⟨33572946370981022897466745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179055713978565455453155973 33572946370981022897466745)
  ·
    refine ⟨25179709778235767173100059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33572946370981022897466745 25179709778235767173100059)
    ·
      refine ⟨37769564667353650759650089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25179709778235767173100059 37769564667353650759650089)
      ·
        refine ⟨28327173500515238069737567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37769564667353650759650089 28327173500515238069737567)
        ·
          refine ⟨42490760250772857104606351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28327173500515238069737567 42490760250772857104606351)
          ·
            refine ⟨63736140376159285656909527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42490760250772857104606351 63736140376159285656909527)
            ·
              refine ⟨95604210564238928485364291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63736140376159285656909527 95604210564238928485364291)
              ·
                refine ⟨143406315846358392728046437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95604210564238928485364291 143406315846358392728046437)
                ·
                  refine ⟨26888684221192198636508707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143406315846358392728046437 26888684221192198636508707)
                  ·
                    refine ⟨40333026331788297954763061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26888684221192198636508707 40333026331788297954763061)
                    ·
                      refine ⟨3781221218605152933259037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40333026331788297954763061 3781221218605152933259037)
                      ·
                        rfl

theorem cell23_7363902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7363902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363902 prefixEnd_7363902 := by exact prefixLift 7363902
  have htrace : WordTrace (prefixWord ++ tailWord_7363902) baseStart_7363902 baseEnd_7363902 := by
    simpa [prefixWord, tailWord_7363902, baseEnd_7363902] using wordTrace_append hprefix tailTrace_7363902
  have hstable : (prefixWord ++ tailWord_7363902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363902).length < 2 ^ (prefixWord ++ tailWord_7363902).sum := by decide
  have hdescent : baseEnd_7363902 < baseStart_7363902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363935 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 7]
def baseStart_7363935 : Nat := 118140960795 + 7363935 * 2 ^ 59
def prefixEnd_7363935 : Nat := 4983230072969 + 3 ^ 40 * 7363935 * 2
def baseEnd_7363935 : Nat := 1260412721155583768048795

theorem tailTrace_7363935 : CollatzResearch.WordTrace tailWord_7363935 prefixEnd_7363935 1260412721155583768048795 := by
  unfold tailWord_7363935
  simp only [CollatzResearch.WordTrace]
  refine ⟨268584774576728629815685259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179056516384485753210456839 268584774576728629815685259)
  ·
    refine ⟨402877161865092944723527889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268584774576728629815685259 402877161865092944723527889)
    ·
      refine ⟨302157871398819708542645917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402877161865092944723527889 302157871398819708542645917)
      ·
        refine ⟨113309201774557390703492219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302157871398819708542645917 113309201774557390703492219)
        ·
          refine ⟨169963802661836086055238329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113309201774557390703492219 169963802661836086055238329)
          ·
            refine ⟨127472851996377064541428747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169963802661836086055238329 127472851996377064541428747)
            ·
              refine ⟨191209277994565596812143121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127472851996377064541428747 191209277994565596812143121)
              ·
                refine ⟨143406958495924197609107341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191209277994565596812143121 143406958495924197609107341)
                ·
                  refine ⟨53777609435971574103415253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143406958495924197609107341 53777609435971574103415253)
                  ·
                    refine ⟨1260412721155583768048795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53777609435971574103415253 1260412721155583768048795)
                    ·
                      rfl

theorem cell23_7363935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_7363935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363935 prefixEnd_7363935 := by exact prefixLift 7363935
  have htrace : WordTrace (prefixWord ++ tailWord_7363935) baseStart_7363935 baseEnd_7363935 := by
    simpa [prefixWord, tailWord_7363935, baseEnd_7363935] using wordTrace_append hprefix tailTrace_7363935
  have hstable : (prefixWord ++ tailWord_7363935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363935).length < 2 ^ (prefixWord ++ tailWord_7363935).sum := by decide
  have hdescent : baseEnd_7363935 < baseStart_7363935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363939 : List Nat := [1, 1, 1, 5, 2, 3, 1, 4, 5]
def baseStart_7363939 : Nat := 118140960795 + 7363939 * 2 ^ 59
def prefixEnd_7363939 : Nat := 4983230072969 + 3 ^ 40 * 7363939 * 2
def baseEnd_7363939 : Nat := 420137801932152143166263

theorem tailTrace_7363939 : CollatzResearch.WordTrace tailWord_7363939 prefixEnd_7363939 420137801932152143166263 := by
  unfold tailWord_7363939
  simp only [CollatzResearch.WordTrace]
  refine ⟨268584920468714138498830871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179056613645809425665887247 268584920468714138498830871)
  ·
    refine ⟨402877380703071207748246307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268584920468714138498830871 402877380703071207748246307)
    ·
      refine ⟨604316071054606811622369461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402877380703071207748246307 604316071054606811622369461)
      ·
        refine ⟨56654631661369388589597137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 604316071054606811622369461 56654631661369388589597137)
        ·
          refine ⟨42490973746027041442197853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56654631661369388589597137 42490973746027041442197853)
          ·
            refine ⟨15934115154760140540824195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42490973746027041442197853 15934115154760140540824195)
            ·
              refine ⟨23901172732140210811236293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934115154760140540824195 23901172732140210811236293)
              ·
                refine ⟨4481469887276289527106805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23901172732140210811236293 4481469887276289527106805)
                ·
                  refine ⟨420137801932152143166263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4481469887276289527106805 420137801932152143166263)
                  ·
                    rfl

theorem cell23_7363939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 4, 5].length) (baseStart_7363939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363939 prefixEnd_7363939 := by exact prefixLift 7363939
  have htrace : WordTrace (prefixWord ++ tailWord_7363939) baseStart_7363939 baseEnd_7363939 := by
    simpa [prefixWord, tailWord_7363939, baseEnd_7363939] using wordTrace_append hprefix tailTrace_7363939
  have hstable : (prefixWord ++ tailWord_7363939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363939).length < 2 ^ (prefixWord ++ tailWord_7363939).sum := by decide
  have hdescent : baseEnd_7363939 < baseStart_7363939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363945 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_7363945 : Nat := 118140960795 + 7363945 * 2 ^ 59
def prefixEnd_7363945 : Nat := 4983230072969 + 3 ^ 40 * 7363945 * 2
def baseEnd_7363945 : Nat := 3781243298273296265021339

theorem tailTrace_7363945 : CollatzResearch.WordTrace tailWord_7363945 prefixEnd_7363945 3781243298273296265021339 := by
  unfold tailWord_7363945
  simp only [CollatzResearch.WordTrace]
  refine ⟨268585139306692401523549289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179056759537794934349032859 268585139306692401523549289)
  ·
    refine ⟨201438854480019301142661967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268585139306692401523549289 201438854480019301142661967)
    ·
      refine ⟨302158281720028951713992951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201438854480019301142661967 302158281720028951713992951)
      ·
        refine ⟨453237422580043427570989427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302158281720028951713992951 453237422580043427570989427)
        ·
          refine ⟨679856133870065141356484141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453237422580043427570989427 679856133870065141356484141)
          ·
            refine ⟨254946050201274428008681553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 679856133870065141356484141 254946050201274428008681553)
            ·
              refine ⟨191209537650955821006511165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254946050201274428008681553 191209537650955821006511165)
              ·
                refine ⟨71703576619108432877441687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191209537650955821006511165 71703576619108432877441687)
                ·
                  refine ⟨107555364928662649316162531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71703576619108432877441687 107555364928662649316162531)
                  ·
                    refine ⟨161333047392993973974243797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107555364928662649316162531 161333047392993973974243797)
                    ·
                      refine ⟨3781243298273296265021339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161333047392993973974243797 3781243298273296265021339)
                      ·
                        rfl

theorem cell23_7363945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_7363945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363945 prefixEnd_7363945 := by exact prefixLift 7363945
  have htrace : WordTrace (prefixWord ++ tailWord_7363945) baseStart_7363945 baseEnd_7363945 := by
    simpa [prefixWord, tailWord_7363945, baseEnd_7363945] using wordTrace_append hprefix tailTrace_7363945
  have hstable : (prefixWord ++ tailWord_7363945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363945).length < 2 ^ (prefixWord ++ tailWord_7363945).sum := by decide
  have hdescent : baseEnd_7363945 < baseStart_7363945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363949 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7363949 : Nat := 118140960795 + 7363949 * 2 ^ 59
def prefixEnd_7363949 : Nat := 4983230072969 + 3 ^ 40 * 7363949 * 2
def baseEnd_7363949 : Nat := 3781245352195914249371321

theorem tailTrace_7363949 : CollatzResearch.WordTrace tailWord_7363949 prefixEnd_7363949 3781245352195914249371321 := by
  unfold tailWord_7363949
  simp only [CollatzResearch.WordTrace]
  refine ⟨268585285198677910206694901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179056856799118606804463267 268585285198677910206694901)
  ·
    refine ⟨25179870487376054081877647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268585285198677910206694901 25179870487376054081877647)
    ·
      refine ⟨37769805731064081122816471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25179870487376054081877647 37769805731064081122816471)
      ·
        refine ⟨56654708596596121684224707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37769805731064081122816471 56654708596596121684224707)
        ·
          refine ⟨84982062894894182526337061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56654708596596121684224707 84982062894894182526337061)
          ·
            refine ⟨15934136792792659223688199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84982062894894182526337061 15934136792792659223688199)
            ·
              refine ⟨23901205189188988835532299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934136792792659223688199 23901205189188988835532299)
              ·
                refine ⟨35851807783783483253298449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23901205189188988835532299 35851807783783483253298449)
                ·
                  refine ⟨26888855837837612439973837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35851807783783483253298449 26888855837837612439973837)
                  ·
                    refine ⟨10083320939189104664990189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26888855837837612439973837 10083320939189104664990189)
                    ·
                      refine ⟨3781245352195914249371321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083320939189104664990189 3781245352195914249371321)
                      ·
                        rfl

theorem cell23_7363949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7363949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363949 prefixEnd_7363949 := by exact prefixLift 7363949
  have htrace : WordTrace (prefixWord ++ tailWord_7363949) baseStart_7363949 baseEnd_7363949 := by
    simpa [prefixWord, tailWord_7363949, baseEnd_7363949] using wordTrace_append hprefix tailTrace_7363949
  have hstable : (prefixWord ++ tailWord_7363949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363949).length < 2 ^ (prefixWord ++ tailWord_7363949).sum := by decide
  have hdescent : baseEnd_7363949 < baseStart_7363949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363969 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_7363969 : Nat := 118140960795 + 7363969 * 2 ^ 59
def prefixEnd_7363969 : Nat := 4983230072969 + 3 ^ 40 * 7363969 * 2
def baseEnd_7363969 : Nat := 1260418540603001390373743

theorem tailTrace_7363969 : CollatzResearch.WordTrace tailWord_7363969 prefixEnd_7363969 1260418540603001390373743 := by
  unfold tailWord_7363969
  simp only [CollatzResearch.WordTrace]
  refine ⟨268586014658605453622422961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179057343105736969081615307 268586014658605453622422961)
  ·
    refine ⟨201439510993954090216817221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268586014658605453622422961 201439510993954090216817221)
    ·
      refine ⟨37769908311366391915653229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201439510993954090216817221 37769908311366391915653229)
      ·
        refine ⟨14163715616762396968369961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37769908311366391915653229 14163715616762396968369961)
        ·
          refine ⟨10622786712571797726277471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14163715616762396968369961 10622786712571797726277471)
          ·
            refine ⟨15934180068857696589416207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622786712571797726277471 15934180068857696589416207)
            ·
              refine ⟨23901270103286544884124311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934180068857696589416207 23901270103286544884124311)
              ·
                refine ⟨35851905154929817326186467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23901270103286544884124311 35851905154929817326186467)
                ·
                  refine ⟨53777857732394725989279701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35851905154929817326186467 53777857732394725989279701)
                  ·
                    refine ⟨1260418540603001390373743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53777857732394725989279701 1260418540603001390373743)
                    ·
                      rfl

theorem cell23_7363969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_7363969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363969 prefixEnd_7363969 := by exact prefixLift 7363969
  have htrace : WordTrace (prefixWord ++ tailWord_7363969) baseStart_7363969 baseEnd_7363969 := by
    simpa [prefixWord, tailWord_7363969, baseEnd_7363969] using wordTrace_append hprefix tailTrace_7363969
  have hstable : (prefixWord ++ tailWord_7363969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363969).length < 2 ^ (prefixWord ++ tailWord_7363969).sum := by decide
  have hdescent : baseEnd_7363969 < baseStart_7363969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363989 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_7363989 : Nat := 118140960795 + 7363989 * 2 ^ 59
def prefixEnd_7363989 : Nat := 4983230072969 + 3 ^ 40 * 7363989 * 2
def baseEnd_7363989 : Nat := 3781265891422094092871137

theorem tailTrace_7363989 : CollatzResearch.WordTrace tailWord_7363989 prefixEnd_7363989 3781265891422094092871137 := by
  unfold tailWord_7363989
  simp only [CollatzResearch.WordTrace]
  refine ⟨268586744118532997038151021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179057829412355331358767347 268586744118532997038151021)
  ·
    refine ⟨100720029044449873889306633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268586744118532997038151021 100720029044449873889306633)
    ·
      refine ⟨75540021783337405416979975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100720029044449873889306633 75540021783337405416979975)
      ·
        refine ⟨113310032675006108125469963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75540021783337405416979975 113310032675006108125469963)
        ·
          refine ⟨169965049012509162188204945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113310032675006108125469963 169965049012509162188204945)
          ·
            refine ⟨127473786759381871641153709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169965049012509162188204945 127473786759381871641153709)
            ·
              refine ⟨47802670034768201865432641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127473786759381871641153709 47802670034768201865432641)
              ·
                refine ⟨35852002526076151399074481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47802670034768201865432641 35852002526076151399074481)
                ·
                  refine ⟨26889001894557113549305861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35852002526076151399074481 26889001894557113549305861)
                  ·
                    refine ⟨5041687855229458790494849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26889001894557113549305861 5041687855229458790494849)
                    ·
                      refine ⟨3781265891422094092871137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041687855229458790494849 3781265891422094092871137)
                      ·
                        rfl

theorem cell23_7363989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_7363989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363989 prefixEnd_7363989 := by exact prefixLift 7363989
  have htrace : WordTrace (prefixWord ++ tailWord_7363989) baseStart_7363989 baseEnd_7363989 := by
    simpa [prefixWord, tailWord_7363989, baseEnd_7363989] using wordTrace_append hprefix tailTrace_7363989
  have hstable : (prefixWord ++ tailWord_7363989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363989).length < 2 ^ (prefixWord ++ tailWord_7363989).sum := by decide
  have hdescent : baseEnd_7363989 < baseStart_7363989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363995 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 14]
def baseStart_7363995 : Nat := 118140960795 + 7363995 * 2 ^ 59
def prefixEnd_7363995 : Nat := 4983230072969 + 3 ^ 40 * 7363995 * 2
def baseEnd_7363995 : Nat := 420140996922891229932901

theorem tailTrace_7363995 : CollatzResearch.WordTrace tailWord_7363995 prefixEnd_7363995 420140996922891229932901 := by
  unfold tailWord_7363995
  simp only [CollatzResearch.WordTrace]
  refine ⟨268586962956511260062869439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179057975304340840041912959 268586962956511260062869439)
  ·
    refine ⟨402880444434766890094304159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268586962956511260062869439 402880444434766890094304159)
    ·
      refine ⟨604320666652150335141456239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402880444434766890094304159 604320666652150335141456239)
      ·
        refine ⟨906480999978225502712184359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604320666652150335141456239 906480999978225502712184359)
        ·
          refine ⟨1359721499967338254068276539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906480999978225502712184359 1359721499967338254068276539)
          ·
            refine ⟨2039582249951007381102414809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359721499967338254068276539 2039582249951007381102414809)
            ·
              refine ⟨1529686687463255535826811107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039582249951007381102414809 1529686687463255535826811107)
              ·
                refine ⟨2294530031194883303740216661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529686687463255535826811107 2294530031194883303740216661)
                ·
                  refine ⟨420140996922891229932901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 2294530031194883303740216661 420140996922891229932901)
                  ·
                    rfl

theorem cell23_7363995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_7363995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363995 prefixEnd_7363995 := by exact prefixLift 7363995
  have htrace : WordTrace (prefixWord ++ tailWord_7363995) baseStart_7363995 baseEnd_7363995 := by
    simpa [prefixWord, tailWord_7363995, baseEnd_7363995] using wordTrace_append hprefix tailTrace_7363995
  have hstable : (prefixWord ++ tailWord_7363995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363995).length < 2 ^ (prefixWord ++ tailWord_7363995).sum := by decide
  have hdescent : baseEnd_7363995 < baseStart_7363995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7363999 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 3, 4]
def baseStart_7363999 : Nat := 118140960795 + 7363999 * 2 ^ 59
def prefixEnd_7363999 : Nat := 4983230072969 + 3 ^ 40 * 7363999 * 2
def baseEnd_7363999 : Nat := 1260423675409546351248697

theorem tailTrace_7363999 : CollatzResearch.WordTrace tailWord_7363999 prefixEnd_7363999 1260423675409546351248697 := by
  unfold tailWord_7363999
  simp only [CollatzResearch.WordTrace]
  refine ⟨268587108848496768746015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179058072565664512497343367 268587108848496768746015051)
  ·
    refine ⟨402880663272745153119022577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268587108848496768746015051 402880663272745153119022577)
    ·
      refine ⟨302160497454558864839266933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402880663272745153119022577 302160497454558864839266933)
      ·
        refine ⟨28327546636364893578681275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302160497454558864839266933 28327546636364893578681275)
        ·
          refine ⟨42491319954547340368021913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28327546636364893578681275 42491319954547340368021913)
          ·
            refine ⟨31868489965910505276016435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42491319954547340368021913 31868489965910505276016435)
            ·
              refine ⟨47802734948865757914024653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31868489965910505276016435 47802734948865757914024653)
              ·
                refine ⟨17926025605824659217759245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47802734948865757914024653 17926025605824659217759245)
                ·
                  refine ⟨6722259602184247206659717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17926025605824659217759245 6722259602184247206659717)
                  ·
                    refine ⟨1260423675409546351248697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722259602184247206659717 1260423675409546351248697)
                    ·
                      rfl

theorem cell23_7363999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_7363999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7363999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7363999 prefixEnd_7363999 := by exact prefixLift 7363999
  have htrace : WordTrace (prefixWord ++ tailWord_7363999) baseStart_7363999 baseEnd_7363999 := by
    simpa [prefixWord, tailWord_7363999, baseEnd_7363999] using wordTrace_append hprefix tailTrace_7363999
  have hstable : (prefixWord ++ tailWord_7363999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7363999).length < 2 ^ (prefixWord ++ tailWord_7363999).sum := by decide
  have hdescent : baseEnd_7363999 < baseStart_7363999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7363999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364012 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 6]
def baseStart_7364012 : Nat := 118140960795 + 7364012 * 2 ^ 59
def prefixEnd_7364012 : Nat := 4983230072969 + 3 ^ 40 * 7364012 * 2
def baseEnd_7364012 : Nat := 420141966830794166987059

theorem tailTrace_7364012 : CollatzResearch.WordTrace tailWord_7364012 prefixEnd_7364012 420141966830794166987059 := by
  unfold tailWord_7364012
  simp only [CollatzResearch.WordTrace]
  refine ⟨134293791498724835983119145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179058388664966447977492193 134293791498724835983119145)
  ·
    refine ⟨100720343624043626987339359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134293791498724835983119145 100720343624043626987339359)
    ·
      refine ⟨151080515436065440481009039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100720343624043626987339359 151080515436065440481009039)
      ·
        refine ⟨226620773154098160721513559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151080515436065440481009039 226620773154098160721513559)
        ·
          refine ⟨339931159731147241082270339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226620773154098160721513559 339931159731147241082270339)
          ·
            refine ⟨509896739596720861623405509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339931159731147241082270339 509896739596720861623405509)
            ·
              refine ⟨95605638674385161554388533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509896739596720861623405509 95605638674385161554388533)
              ·
                refine ⟨8963028625723608895723925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95605638674385161554388533 8963028625723608895723925)
                ·
                  refine ⟨420141966830794166987059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8963028625723608895723925 420141966830794166987059)
                  ·
                    rfl

theorem cell23_7364012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_7364012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364012 prefixEnd_7364012 := by exact prefixLift 7364012
  have htrace : WordTrace (prefixWord ++ tailWord_7364012) baseStart_7364012 baseEnd_7364012 := by
    simpa [prefixWord, tailWord_7364012, baseEnd_7364012] using wordTrace_append hprefix tailTrace_7364012
  have hstable : (prefixWord ++ tailWord_7364012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364012).length < 2 ^ (prefixWord ++ tailWord_7364012).sum := by decide
  have hdescent : baseEnd_7364012 < baseStart_7364012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364056 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_7364056 : Nat := 118140960795 + 7364056 * 2 ^ 59
def prefixEnd_7364056 : Nat := 4983230072969 + 3 ^ 40 * 7364056 * 2
def baseEnd_7364056 : Nat := 3781300294625945330733329

theorem tailTrace_7364056 : CollatzResearch.WordTrace tailWord_7364056 prefixEnd_7364056 3781300294625945330733329 := by
  unfold tailWord_7364056
  simp only [CollatzResearch.WordTrace]
  refine ⟨134294593904645133740420011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179059458539526844987226681 134294593904645133740420011)
  ·
    refine ⟨201441890856967700610630017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134294593904645133740420011 201441890856967700610630017)
    ·
      refine ⟨151081418142725775457972513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201441890856967700610630017 151081418142725775457972513)
      ·
        refine ⟨113311063607044331593479385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151081418142725775457972513 113311063607044331593479385)
        ·
          refine ⟨84983297705283248695109539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113311063607044331593479385 84983297705283248695109539)
          ·
            refine ⟨127474946557924873042664309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84983297705283248695109539 127474946557924873042664309)
            ·
              refine ⟨11950776239805456847749779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127474946557924873042664309 11950776239805456847749779)
              ·
                refine ⟨17926164359708185271624669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11950776239805456847749779 17926164359708185271624669)
                ·
                  refine ⟨6722311634890569476859251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17926164359708185271624669 6722311634890569476859251)
                  ·
                    refine ⟨10083467452335854215288877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722311634890569476859251 10083467452335854215288877)
                    ·
                      refine ⟨3781300294625945330733329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083467452335854215288877 3781300294625945330733329)
                      ·
                        rfl

theorem cell23_7364056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_7364056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364056 prefixEnd_7364056 := by exact prefixLift 7364056
  have htrace : WordTrace (prefixWord ++ tailWord_7364056) baseStart_7364056 baseEnd_7364056 := by
    simpa [prefixWord, tailWord_7364056, baseEnd_7364056] using wordTrace_append hprefix tailTrace_7364056
  have hstable : (prefixWord ++ tailWord_7364056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364056).length < 2 ^ (prefixWord ++ tailWord_7364056).sum := by decide
  have hdescent : baseEnd_7364056 < baseStart_7364056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364079 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 6, 2]
def baseStart_7364079 : Nat := 118140960795 + 7364079 * 2 ^ 59
def prefixEnd_7364079 : Nat := 4983230072969 + 3 ^ 40 * 7364079 * 2
def baseEnd_7364079 : Nat := 3781312104680998740745723

theorem tailTrace_7364079 : CollatzResearch.WordTrace tailWord_7364079 prefixEnd_7364079 3781312104680998740745723 := by
  unfold tailWord_7364079
  simp only [CollatzResearch.WordTrace]
  refine ⟨268590026688206942408927291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179060017792137961605951527 268590026688206942408927291)
  ·
    refine ⟨402885040032310413613390937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268590026688206942408927291 402885040032310413613390937)
    ·
      refine ⟨302163780024232810210043203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402885040032310413613390937 302163780024232810210043203)
      ·
        refine ⟨453245670036349215315064805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302163780024232810210043203 453245670036349215315064805)
        ·
          refine ⟨84983563131815477871574651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453245670036349215315064805 84983563131815477871574651)
          ·
            refine ⟨127475344697723216807361977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84983563131815477871574651 127475344697723216807361977)
            ·
              refine ⟨95606508523292412605521483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127475344697723216807361977 95606508523292412605521483)
              ·
                refine ⟨143409762784938618908282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95606508523292412605521483 143409762784938618908282225)
                ·
                  refine ⟨107557322088703964181211669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143409762784938618908282225 107557322088703964181211669)
                  ·
                    refine ⟨5041749472907998320994297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107557322088703964181211669 5041749472907998320994297)
                    ·
                      refine ⟨3781312104680998740745723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041749472907998320994297 3781312104680998740745723)
                      ·
                        rfl

theorem cell23_7364079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 6, 2].length) (baseStart_7364079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364079 prefixEnd_7364079 := by exact prefixLift 7364079
  have htrace : WordTrace (prefixWord ++ tailWord_7364079) baseStart_7364079 baseEnd_7364079 := by
    simpa [prefixWord, tailWord_7364079, baseEnd_7364079] using wordTrace_append hprefix tailTrace_7364079
  have hstable : (prefixWord ++ tailWord_7364079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364079).length < 2 ^ (prefixWord ++ tailWord_7364079).sum := by decide
  have hdescent : baseEnd_7364079 < baseStart_7364079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364106 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_7364106 : Nat := 118140960795 + 7364106 * 2 ^ 59
def prefixEnd_7364106 : Nat := 4983230072969 + 3 ^ 40 * 7364106 * 2
def baseEnd_7364106 : Nat := 1260441989552890045036033

theorem tailTrace_7364106 : CollatzResearch.WordTrace tailWord_7364106 prefixEnd_7364106 1260441989552890045036033 := by
  unfold tailWord_7364106
  simp only [CollatzResearch.WordTrace]
  refine ⟨67147752864777281505040043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179060674306072750680106781 67147752864777281505040043)
  ·
    refine ⟨100721629297165922257560065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67147752864777281505040043 100721629297165922257560065)
    ·
      refine ⟨75541221972874441693170049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100721629297165922257560065 75541221972874441693170049)
      ·
        refine ⟨56655916479655831269877537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75541221972874441693170049 56655916479655831269877537)
        ·
          refine ⟨42491937359741873452408153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56655916479655831269877537 42491937359741873452408153)
          ·
            refine ⟨31868953019806405089306115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42491937359741873452408153 31868953019806405089306115)
            ·
              refine ⟨47803429529709607633959173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31868953019806405089306115 47803429529709607633959173)
              ·
                refine ⟨8963143036820551431367345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47803429529709607633959173 8963143036820551431367345)
                ·
                  refine ⟨6722357277615413573525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8963143036820551431367345 6722357277615413573525509)
                  ·
                    refine ⟨1260441989552890045036033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722357277615413573525509 1260441989552890045036033)
                    ·
                      rfl

theorem cell23_7364106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_7364106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364106 prefixEnd_7364106 := by exact prefixLift 7364106
  have htrace : WordTrace (prefixWord ++ tailWord_7364106) baseStart_7364106 baseEnd_7364106 := by
    simpa [prefixWord, tailWord_7364106, baseEnd_7364106] using wordTrace_append hprefix tailTrace_7364106
  have hstable : (prefixWord ++ tailWord_7364106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364106).length < 2 ^ (prefixWord ++ tailWord_7364106).sum := by decide
  have hdescent : baseEnd_7364106 < baseStart_7364106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364107 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 1, 1, 3]
def baseStart_7364107 : Nat := 118140960795 + 7364107 * 2 ^ 59
def prefixEnd_7364107 : Nat := 4983230072969 + 3 ^ 40 * 7364107 * 2
def baseEnd_7364107 : Nat := 3781326482139324631195595

theorem tailTrace_7364107 : CollatzResearch.WordTrace tailWord_7364107 prefixEnd_7364107 3781326482139324631195595 := by
  unfold tailWord_7364107
  simp only [CollatzResearch.WordTrace]
  refine ⟨268591047932105503190946575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179060698621403668793964383 268591047932105503190946575)
  ·
    refine ⟨402886571898158254786419863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268591047932105503190946575 402886571898158254786419863)
    ·
      refine ⟨604329857847237382179629795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402886571898158254786419863 604329857847237382179629795)
      ·
        refine ⟨906494786770856073269444693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604329857847237382179629795 906494786770856073269444693)
        ·
          refine ⟨10622985782470969608626305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 906494786770856073269444693 10622985782470969608626305)
          ·
            refine ⟨7967239336853227206469729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622985782470969608626305 7967239336853227206469729)
            ·
              refine ⟨5975429502639920404852297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967239336853227206469729 5975429502639920404852297)
              ·
                refine ⟨4481572126979940303639223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5975429502639920404852297 4481572126979940303639223)
                ·
                  refine ⟨6722358190469910455458835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481572126979940303639223 6722358190469910455458835)
                  ·
                    refine ⟨10083537285704865683188253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722358190469910455458835 10083537285704865683188253)
                    ·
                      refine ⟨3781326482139324631195595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083537285704865683188253 3781326482139324631195595)
                      ·
                        rfl

theorem cell23_7364107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 1, 3].length) (baseStart_7364107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364107 prefixEnd_7364107 := by exact prefixLift 7364107
  have htrace : WordTrace (prefixWord ++ tailWord_7364107) baseStart_7364107 baseEnd_7364107 := by
    simpa [prefixWord, tailWord_7364107, baseEnd_7364107] using wordTrace_append hprefix tailTrace_7364107
  have hstable : (prefixWord ++ tailWord_7364107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364107).length < 2 ^ (prefixWord ++ tailWord_7364107).sum := by decide
  have hdescent : baseEnd_7364107 < baseStart_7364107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364146 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_7364146 : Nat := 118140960795 + 7364146 * 2 ^ 59
def prefixEnd_7364146 : Nat := 4983230072969 + 3 ^ 40 * 7364146 * 2
def baseEnd_7364146 : Nat := 3781346507884849978607915

theorem tailTrace_7364146 : CollatzResearch.WordTrace tailWord_7364146 prefixEnd_7364146 3781346507884849978607915 := by
  unfold tailWord_7364146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67148117594741053212904073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179061646919309475234410861 67148117594741053212904073)
  ·
    refine ⟨50361088196055789909678055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67148117594741053212904073 50361088196055789909678055)
    ·
      refine ⟨75541632294083684864517083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50361088196055789909678055 75541632294083684864517083)
      ·
        refine ⟨113312448441125527296775625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75541632294083684864517083 113312448441125527296775625)
        ·
          refine ⟨84984336330844145472581719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113312448441125527296775625 84984336330844145472581719)
          ·
            refine ⟨127476504496266218208872579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84984336330844145472581719 127476504496266218208872579)
            ·
              refine ⟨191214756744399327313308869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127476504496266218208872579 191214756744399327313308869)
              ·
                refine ⟨35852766889574873871245413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191214756744399327313308869 35852766889574873871245413)
                ·
                  refine ⟨6722393791795288850858515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35852766889574873871245413 6722393791795288850858515)
                  ·
                    refine ⟨10083590687692933276287773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722393791795288850858515 10083590687692933276287773)
                    ·
                      refine ⟨3781346507884849978607915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083590687692933276287773 3781346507884849978607915)
                      ·
                        rfl

theorem cell23_7364146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_7364146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364146 prefixEnd_7364146 := by exact prefixLift 7364146
  have htrace : WordTrace (prefixWord ++ tailWord_7364146) baseStart_7364146 baseEnd_7364146 := by
    simpa [prefixWord, tailWord_7364146, baseEnd_7364146] using wordTrace_append hprefix tailTrace_7364146
  have hstable : (prefixWord ++ tailWord_7364146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364146).length < 2 ^ (prefixWord ++ tailWord_7364146).sum := by decide
  have hdescent : baseEnd_7364146 < baseStart_7364146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364150 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7364150 : Nat := 118140960795 + 7364150 * 2 ^ 59
def prefixEnd_7364150 : Nat := 4983230072969 + 3 ^ 40 * 7364150 * 2
def baseEnd_7364150 : Nat := 3781348561807467962957897

theorem tailTrace_7364150 : CollatzResearch.WordTrace tailWord_7364150 prefixEnd_7364150 3781348561807467962957897 := by
  unfold tailWord_7364150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787038516934357595922619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179061744180633147689841269 16787038516934357595922619)
  ·
    refine ⟨25180557775401536393883929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16787038516934357595922619 25180557775401536393883929)
    ·
      refine ⟨18885418331551152295412947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25180557775401536393883929 18885418331551152295412947)
      ·
        refine ⟨28328127497326728443119421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18885418331551152295412947 28328127497326728443119421)
        ·
          refine ⟨10623047811497523166169783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28328127497326728443119421 10623047811497523166169783)
          ·
            refine ⟨15934571717246284749254675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623047811497523166169783 15934571717246284749254675)
            ·
              refine ⟨23901857575869427123882013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934571717246284749254675 23901857575869427123882013)
              ·
                refine ⟨8963196590951035171455755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23901857575869427123882013 8963196590951035171455755)
                ·
                  refine ⟨13444794886426552757183633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963196590951035171455755 13444794886426552757183633)
                  ·
                    refine ⟨10083596164819914567887725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13444794886426552757183633 10083596164819914567887725)
                    ·
                      refine ⟨3781348561807467962957897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083596164819914567887725 3781348561807467962957897)
                      ·
                        rfl

theorem cell23_7364150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7364150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364150 prefixEnd_7364150 := by exact prefixLift 7364150
  have htrace : WordTrace (prefixWord ++ tailWord_7364150) baseStart_7364150 baseEnd_7364150 := by
    simpa [prefixWord, tailWord_7364150, baseEnd_7364150] using wordTrace_append hprefix tailTrace_7364150
  have hstable : (prefixWord ++ tailWord_7364150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364150).length < 2 ^ (prefixWord ++ tailWord_7364150).sum := by decide
  have hdescent : baseEnd_7364150 < baseStart_7364150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364180 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_7364180 : Nat := 118140960795 + 7364180 * 2 ^ 59
def prefixEnd_7364180 : Nat := 4983230072969 + 3 ^ 40 * 7364180 * 2
def baseEnd_7364180 : Nat := 3781363966227102845582759

theorem tailTrace_7364180 : CollatzResearch.WordTrace tailWord_7364180 prefixEnd_7364180 3781363966227102845582759 := by
  unfold tailWord_7364180
  simp only [CollatzResearch.WordTrace]
  refine ⟨134296855230420518329176997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179062473640560691105569329 134296855230420518329176997)
  ·
    refine ⟨25180660355703847186720687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134296855230420518329176997 25180660355703847186720687)
    ·
      refine ⟨37770990533555770780081031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25180660355703847186720687 37770990533555770780081031)
      ·
        refine ⟨56656485800333656170121547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37770990533555770780081031 56656485800333656170121547)
        ·
          refine ⟨84984728700500484255182321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56656485800333656170121547 84984728700500484255182321)
          ·
            refine ⟨63738546525375363191386741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84984728700500484255182321 63738546525375363191386741)
            ·
              refine ⟨5975488736753940299192507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63738546525375363191386741 5975488736753940299192507)
              ·
                refine ⟨8963233105130910448788761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975488736753940299192507 8963233105130910448788761)
                ·
                  refine ⟨6722424828848182836591571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8963233105130910448788761 6722424828848182836591571)
                  ·
                    refine ⟨10083637243272274254887357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722424828848182836591571 10083637243272274254887357)
                    ·
                      refine ⟨3781363966227102845582759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083637243272274254887357 3781363966227102845582759)
                      ·
                        rfl

theorem cell23_7364180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_7364180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364180 prefixEnd_7364180 := by exact prefixLift 7364180
  have htrace : WordTrace (prefixWord ++ tailWord_7364180) baseStart_7364180 baseEnd_7364180 := by
    simpa [prefixWord, tailWord_7364180, baseEnd_7364180] using wordTrace_append hprefix tailTrace_7364180
  have hstable : (prefixWord ++ tailWord_7364180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364180).length < 2 ^ (prefixWord ++ tailWord_7364180).sum := by decide
  have hdescent : baseEnd_7364180 < baseStart_7364180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364199 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7364199 : Nat := 118140960795 + 7364199 * 2 ^ 59
def prefixEnd_7364199 : Nat := 4983230072969 + 3 ^ 40 * 7364199 * 2
def baseEnd_7364199 : Nat := 3781373722359538271245171

theorem tailTrace_7364199 : CollatzResearch.WordTrace tailWord_7364199 prefixEnd_7364199 3781373722359538271245171 := by
  unfold tailWord_7364199
  simp only [CollatzResearch.WordTrace]
  refine ⟨268594403447772202903295651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179062935631848135268863767 268594403447772202903295651)
  ·
    refine ⟨402891605171658304354943477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268594403447772202903295651 402891605171658304354943477)
    ·
      refine ⟨37771087984842966033275951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402891605171658304354943477 37771087984842966033275951)
      ·
        refine ⟨56656631977264449049913927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37771087984842966033275951 56656631977264449049913927)
        ·
          refine ⟨84984947965896673574870891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56656631977264449049913927 84984947965896673574870891)
          ·
            refine ⟨127477421948845010362306337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84984947965896673574870891 127477421948845010362306337)
            ·
              refine ⟨95608066461633757771729753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127477421948845010362306337 95608066461633757771729753)
              ·
                refine ⟨71706049846225318328797315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95608066461633757771729753 71706049846225318328797315)
                ·
                  refine ⟨107559074769337977493195973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71706049846225318328797315 107559074769337977493195973)
                  ·
                    refine ⟨20167326519250870779974245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107559074769337977493195973 20167326519250870779974245)
                    ·
                      refine ⟨3781373722359538271245171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20167326519250870779974245 3781373722359538271245171)
                      ·
                        rfl

theorem cell23_7364199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7364199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364199 prefixEnd_7364199 := by exact prefixLift 7364199
  have htrace : WordTrace (prefixWord ++ tailWord_7364199) baseStart_7364199 baseEnd_7364199 := by
    simpa [prefixWord, tailWord_7364199, baseEnd_7364199] using wordTrace_append hprefix tailTrace_7364199
  have hstable : (prefixWord ++ tailWord_7364199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364199).length < 2 ^ (prefixWord ++ tailWord_7364199).sum := by decide
  have hdescent : baseEnd_7364199 < baseStart_7364199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364256 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_7364256 : Nat := 118140960795 + 7364256 * 2 ^ 59
def prefixEnd_7364256 : Nat := 4983230072969 + 3 ^ 40 * 7364256 * 2
def baseEnd_7364256 : Nat := 1260467663585614849410803

theorem tailTrace_7364256 : CollatzResearch.WordTrace tailWord_7364256 prefixEnd_7364256 1260467663585614849410803 := by
  unfold tailWord_7364256
  simp only [CollatzResearch.WordTrace]
  refine ⟨134298241204282850819060311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179064321605710467758747081 134298241204282850819060311)
  ·
    refine ⟨201447361806424276228590467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134298241204282850819060311 201447361806424276228590467)
    ·
      refine ⟨302171042709636414342885701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201447361806424276228590467 302171042709636414342885701)
      ·
        refine ⟨56657070508056827689291069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302171042709636414342885701 56657070508056827689291069)
        ·
          refine ⟨21246401440521310383484151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56657070508056827689291069 21246401440521310383484151)
          ·
            refine ⟨31869602160781965575226227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21246401440521310383484151 31869602160781965575226227)
            ·
              refine ⟨47804403241172948362839341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31869602160781965575226227 47804403241172948362839341)
              ·
                refine ⟨17926651215439855636064753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47804403241172948362839341 17926651215439855636064753)
                ·
                  refine ⟨13444988411579891727048565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17926651215439855636064753 13444988411579891727048565)
                  ·
                    refine ⟨1260467663585614849410803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13444988411579891727048565 1260467663585614849410803)
                    ·
                      rfl

theorem cell23_7364256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_7364256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364256 prefixEnd_7364256 := by exact prefixLift 7364256
  have htrace : WordTrace (prefixWord ++ tailWord_7364256) baseStart_7364256 baseEnd_7364256 := by
    simpa [prefixWord, tailWord_7364256, baseEnd_7364256] using wordTrace_append hprefix tailTrace_7364256
  have hstable : (prefixWord ++ tailWord_7364256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364256).length < 2 ^ (prefixWord ++ tailWord_7364256).sum := by decide
  have hdescent : baseEnd_7364256 < baseStart_7364256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364277 : List Nat := [1, 3, 3, 3, 2, 2, 2, 2, 5]
def baseStart_7364277 : Nat := 118140960795 + 7364277 * 2 ^ 59
def prefixEnd_7364277 : Nat := 4983230072969 + 3 ^ 40 * 7364277 * 2
def baseEnd_7364277 : Nat := 420157085983398774007757

theorem tailTrace_7364277 : CollatzResearch.WordTrace tailWord_7364277 prefixEnd_7364277 420157085983398774007757 := by
  unfold tailWord_7364277
  simp only [CollatzResearch.WordTrace]
  refine ⟨268597248341489622224635085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179064832227659748149756723 268597248341489622224635085)
  ·
    refine ⟨100723968128058608334238157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268597248341489622224635085 100723968128058608334238157)
    ·
      refine ⟨37771488048021978125339309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100723968128058608334238157 37771488048021978125339309)
      ·
        refine ⟨14164308018008241797002241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37771488048021978125339309 14164308018008241797002241)
        ·
          refine ⟨10623231013506181347751681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14164308018008241797002241 10623231013506181347751681)
          ·
            refine ⟨7967423260129636010813761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10623231013506181347751681 7967423260129636010813761)
            ·
              refine ⟨5975567445097227008110321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967423260129636010813761 5975567445097227008110321)
              ·
                refine ⟨4481675583822920256082741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5975567445097227008110321 4481675583822920256082741)
                ·
                  refine ⟨420157085983398774007757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4481675583822920256082741 420157085983398774007757)
                  ·
                    rfl

theorem cell23_7364277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_7364277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364277 prefixEnd_7364277 := by exact prefixLift 7364277
  have htrace : WordTrace (prefixWord ++ tailWord_7364277) baseStart_7364277 baseEnd_7364277 := by
    simpa [prefixWord, tailWord_7364277, baseEnd_7364277] using wordTrace_append hprefix tailTrace_7364277
  have hstable : (prefixWord ++ tailWord_7364277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364277).length < 2 ^ (prefixWord ++ tailWord_7364277).sum := by decide
  have hdescent : baseEnd_7364277 < baseStart_7364277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364296 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_7364296 : Nat := 118140960795 + 7364296 * 2 ^ 59
def prefixEnd_7364296 : Nat := 4983230072969 + 3 ^ 40 * 7364296 * 2
def baseEnd_7364296 : Nat := 3781423529983024391732225

theorem tailTrace_7364296 : CollatzResearch.WordTrace tailWord_7364296 prefixEnd_7364296 3781423529983024391732225 := by
  unfold tailWord_7364296
  simp only [CollatzResearch.WordTrace]
  refine ⟨134298970664210394234788371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179065294218947192313051161 134298970664210394234788371)
  ·
    refine ⟨201448455996315591352182557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134298970664210394234788371 201448455996315591352182557)
    ·
      refine ⟨75543170998618346757068459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201448455996315591352182557 75543170998618346757068459)
      ·
        refine ⟨113314756497927520135602689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75543170998618346757068459 113314756497927520135602689)
        ·
          refine ⟨84986067373445640101702017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113314756497927520135602689 84986067373445640101702017)
          ·
            refine ⟨63739550530084230076276513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84986067373445640101702017 63739550530084230076276513)
            ·
              refine ⟨47804662897563172557207385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63739550530084230076276513 47804662897563172557207385)
              ·
                refine ⟨35853497173172379417905539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47804662897563172557207385 35853497173172379417905539)
                ·
                  refine ⟨53780245759758569126858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35853497173172379417905539 53780245759758569126858309)
                  ·
                    refine ⟨10083796079954731711285933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53780245759758569126858309 10083796079954731711285933)
                    ·
                      refine ⟨3781423529983024391732225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083796079954731711285933 3781423529983024391732225)
                      ·
                        rfl

theorem cell23_7364296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_7364296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364296 prefixEnd_7364296 := by exact prefixLift 7364296
  have htrace : WordTrace (prefixWord ++ tailWord_7364296) baseStart_7364296 baseEnd_7364296 := by
    simpa [prefixWord, tailWord_7364296, baseEnd_7364296] using wordTrace_append hprefix tailTrace_7364296
  have hstable : (prefixWord ++ tailWord_7364296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364296).length < 2 ^ (prefixWord ++ tailWord_7364296).sum := by decide
  have hdescent : baseEnd_7364296 < baseStart_7364296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364313 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_7364313 : Nat := 118140960795 + 7364313 * 2 ^ 59
def prefixEnd_7364313 : Nat := 4983230072969 + 3 ^ 40 * 7364313 * 2
def baseEnd_7364313 : Nat := 3781432259154150825219647

theorem tailTrace_7364313 : CollatzResearch.WordTrace tailWord_7364313 prefixEnd_7364313 3781432259154150825219647 := by
  unfold tailWord_7364313
  simp only [CollatzResearch.WordTrace]
  refine ⟨268598561369359200372945593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179065707579572800248630395 268598561369359200372945593)
  ·
    refine ⟨201448921027019400279709195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268598561369359200372945593 201448921027019400279709195)
    ·
      refine ⟨302173381540529100419563793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201448921027019400279709195 302173381540529100419563793)
      ·
        refine ⟨226630036155396825314672845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302173381540529100419563793 226630036155396825314672845)
        ·
          refine ⟨84986263558273809493002317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226630036155396825314672845 84986263558273809493002317)
          ·
            refine ⟨31869848834352678559875869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84986263558273809493002317 31869848834352678559875869)
            ·
              refine ⟨11951193312882254459953451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31869848834352678559875869 11951193312882254459953451)
              ·
                refine ⟨17926789969323381689930177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11951193312882254459953451 17926789969323381689930177)
                ·
                  refine ⟨13445092476992536267447633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17926789969323381689930177 13445092476992536267447633)
                  ·
                    refine ⟨10083819357744402200585725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13445092476992536267447633 10083819357744402200585725)
                    ·
                      refine ⟨3781432259154150825219647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083819357744402200585725 3781432259154150825219647)
                      ·
                        rfl

theorem cell23_7364313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_7364313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364313 prefixEnd_7364313 := by exact prefixLift 7364313
  have htrace : WordTrace (prefixWord ++ tailWord_7364313) baseStart_7364313 baseEnd_7364313 := by
    simpa [prefixWord, tailWord_7364313, baseEnd_7364313] using wordTrace_append hprefix tailTrace_7364313
  have hstable : (prefixWord ++ tailWord_7364313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364313).length < 2 ^ (prefixWord ++ tailWord_7364313).sum := by decide
  have hdescent : baseEnd_7364313 < baseStart_7364313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364333 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 6]
def baseStart_7364333 : Nat := 118140960795 + 7364333 * 2 ^ 59
def prefixEnd_7364333 : Nat := 4983230072969 + 3 ^ 40 * 7364333 * 2
def baseEnd_7364333 : Nat := 420160280974137860774395

theorem tailTrace_7364333 : CollatzResearch.WordTrace tailWord_7364333 prefixEnd_7364333 420160280974137860774395 := by
  unfold tailWord_7364333
  simp only [CollatzResearch.WordTrace]
  refine ⟨268599290829286743788673653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179066193886191162525782435 268599290829286743788673653)
  ·
    refine ⟨25181183515245632230188155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268599290829286743788673653 25181183515245632230188155)
    ·
      refine ⟨37771775272868448345282233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25181183515245632230188155 37771775272868448345282233)
      ·
        refine ⟨28328831454651336258961675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37771775272868448345282233 28328831454651336258961675)
        ·
          refine ⟨42493247181977004388442513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28328831454651336258961675 42493247181977004388442513)
          ·
            refine ⟨31869935386482753291331885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42493247181977004388442513 31869935386482753291331885)
            ·
              refine ⟨11951225769931032484249457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31869935386482753291331885 11951225769931032484249457)
              ·
                refine ⟨8963419327448274363187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11951225769931032484249457 8963419327448274363187093)
                ·
                  refine ⟨420160280974137860774395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8963419327448274363187093 420160280974137860774395)
                  ·
                    rfl

theorem cell23_7364333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_7364333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364333 prefixEnd_7364333 := by exact prefixLift 7364333
  have htrace : WordTrace (prefixWord ++ tailWord_7364333) baseStart_7364333 baseEnd_7364333 := by
    simpa [prefixWord, tailWord_7364333, baseEnd_7364333] using wordTrace_append hprefix tailTrace_7364333
  have hstable : (prefixWord ++ tailWord_7364333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364333).length < 2 ^ (prefixWord ++ tailWord_7364333).sum := by decide
  have hdescent : baseEnd_7364333 < baseStart_7364333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364343 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_7364343 : Nat := 118140960795 + 7364343 * 2 ^ 59
def prefixEnd_7364343 : Nat := 4983230072969 + 3 ^ 40 * 7364343 * 2
def baseEnd_7364343 : Nat := 3781447663573785707844509

theorem tailTrace_7364343 : CollatzResearch.WordTrace tailWord_7364343 prefixEnd_7364343 3781447663573785707844509 := by
  unfold tailWord_7364343
  simp only [CollatzResearch.WordTrace]
  refine ⟨268599655559250515496537683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179066437039500343664358455 268599655559250515496537683)
  ·
    refine ⟨402899483338875773244806525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268599655559250515496537683 402899483338875773244806525)
    ·
      refine ⟨151087306252078414966802447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402899483338875773244806525 151087306252078414966802447)
      ·
        refine ⟨226630959378117622450203671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151087306252078414966802447 226630959378117622450203671)
        ·
          refine ⟨339946439067176433675305507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226630959378117622450203671 339946439067176433675305507)
          ·
            refine ⟨509919658600764650512958261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339946439067176433675305507 509919658600764650512958261)
            ·
              refine ⟨47804967993821685985589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509919658600764650512958261 47804967993821685985589837)
              ·
                refine ⟨17926862997683132244596189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47804967993821685985589837 17926862997683132244596189)
                ·
                  refine ⟨6722573624131174591723571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17926862997683132244596189 6722573624131174591723571)
                  ·
                    refine ⟨10083860436196761887585357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722573624131174591723571 10083860436196761887585357)
                    ·
                      refine ⟨3781447663573785707844509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083860436196761887585357 3781447663573785707844509)
                      ·
                        rfl

theorem cell23_7364343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_7364343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364343 prefixEnd_7364343 := by exact prefixLift 7364343
  have htrace : WordTrace (prefixWord ++ tailWord_7364343) baseStart_7364343 baseEnd_7364343 := by
    simpa [prefixWord, tailWord_7364343, baseEnd_7364343] using wordTrace_append hprefix tailTrace_7364343
  have hstable : (prefixWord ++ tailWord_7364343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364343).length < 2 ^ (prefixWord ++ tailWord_7364343).sum := by decide
  have hdescent : baseEnd_7364343 < baseStart_7364343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364353 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_7364353 : Nat := 118140960795 + 7364353 * 2 ^ 59
def prefixEnd_7364353 : Nat := 4983230072969 + 3 ^ 40 * 7364353 * 2
def baseEnd_7364353 : Nat := 3781452798380330668719463

theorem tailTrace_7364353 : CollatzResearch.WordTrace tailWord_7364353 prefixEnd_7364353 3781452798380330668719463 := by
  unfold tailWord_7364353
  simp only [CollatzResearch.WordTrace]
  refine ⟨268600020289214287204401713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179066680192809524802934475 268600020289214287204401713)
  ·
    refine ⟨201450015216910715403301285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268600020289214287204401713 201450015216910715403301285)
    ·
      refine ⟨37771877853170759138118991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201450015216910715403301285 37771877853170759138118991)
      ·
        refine ⟨56657816779756138707178487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37771877853170759138118991 56657816779756138707178487)
        ·
          refine ⟨84986725169634208060767731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56657816779756138707178487 84986725169634208060767731)
          ·
            refine ⟨127480087754451312091151597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84986725169634208060767731 127480087754451312091151597)
            ·
              refine ⟨47805032907919242034181849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127480087754451312091151597 47805032907919242034181849)
              ·
                refine ⟨35853774680939431525636387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47805032907919242034181849 35853774680939431525636387)
                ·
                  refine ⟨53780662021409147288454581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35853774680939431525636387 53780662021409147288454581)
                  ·
                    refine ⟨5041937064507107558292617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53780662021409147288454581 5041937064507107558292617)
                    ·
                      refine ⟨3781452798380330668719463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5041937064507107558292617 3781452798380330668719463)
                      ·
                        rfl

theorem cell23_7364353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_7364353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364353 prefixEnd_7364353 := by exact prefixLift 7364353
  have htrace : WordTrace (prefixWord ++ tailWord_7364353) baseStart_7364353 baseEnd_7364353 := by
    simpa [prefixWord, tailWord_7364353, baseEnd_7364353] using wordTrace_append hprefix tailTrace_7364353
  have hstable : (prefixWord ++ tailWord_7364353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364353).length < 2 ^ (prefixWord ++ tailWord_7364353).sum := by decide
  have hdescent : baseEnd_7364353 < baseStart_7364353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364376 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_7364376 : Nat := 118140960795 + 7364376 * 2 ^ 59
def prefixEnd_7364376 : Nat := 4983230072969 + 3 ^ 40 * 7364376 * 2
def baseEnd_7364376 : Nat := 1260488202811794692910619

theorem tailTrace_7364376 : CollatzResearch.WordTrace tailWord_7364376 prefixEnd_7364376 1260488202811794692910619 := by
  unfold tailWord_7364376
  simp only [CollatzResearch.WordTrace]
  refine ⟨134300429584065481066244491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179067239445420641421659321 134300429584065481066244491)
  ·
    refine ⟨201450644376098221599366737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134300429584065481066244491 201450644376098221599366737)
    ·
      refine ⟨151087983282073666199525053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201450644376098221599366737 151087983282073666199525053)
      ·
        refine ⟨56657993730777624824821895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151087983282073666199525053 56657993730777624824821895)
        ·
          refine ⟨84986990596166437237232843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56657993730777624824821895 84986990596166437237232843)
          ·
            refine ⟨127480485894249655855849265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84986990596166437237232843 127480485894249655855849265)
            ·
              refine ⟨95610364420687241891886949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127480485894249655855849265 95610364420687241891886949)
              ·
                refine ⟨17926943328878857854728803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95610364420687241891886949 17926943328878857854728803)
                ·
                  refine ⟨26890414993318286782093205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17926943328878857854728803 26890414993318286782093205)
                  ·
                    refine ⟨1260488202811794692910619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26890414993318286782093205 1260488202811794692910619)
                    ·
                      rfl

theorem cell23_7364376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_7364376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364376 prefixEnd_7364376 := by exact prefixLift 7364376
  have htrace : WordTrace (prefixWord ++ tailWord_7364376) baseStart_7364376 baseEnd_7364376 := by
    simpa [prefixWord, tailWord_7364376, baseEnd_7364376] using wordTrace_append hprefix tailTrace_7364376
  have hstable : (prefixWord ++ tailWord_7364376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364376).length < 2 ^ (prefixWord ++ tailWord_7364376).sum := by decide
  have hdescent : baseEnd_7364376 < baseStart_7364376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364383 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_7364383 : Nat := 118140960795 + 7364383 * 2 ^ 59
def prefixEnd_7364383 : Nat := 4983230072969 + 3 ^ 40 * 7364383 * 2
def baseEnd_7364383 : Nat := 3781468202799965551344325

theorem tailTrace_7364383 : CollatzResearch.WordTrace tailWord_7364383 prefixEnd_7364383 3781468202799965551344325 := by
  unfold tailWord_7364383
  simp only [CollatzResearch.WordTrace]
  refine ⟨268601114479105602327993803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179067409652737068218662535 268601114479105602327993803)
  ·
    refine ⟨402901671718658403491990705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268601114479105602327993803 402901671718658403491990705)
    ·
      refine ⟨302176253788993802618993029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402901671718658403491990705 302176253788993802618993029)
      ·
        refine ⟨56658047585436337991061193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302176253788993802618993029 56658047585436337991061193)
        ·
          refine ⟨42493535689077253493295895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56658047585436337991061193 42493535689077253493295895)
          ·
            refine ⟨63740303533615880239943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42493535689077253493295895 63740303533615880239943843)
            ·
              refine ⟨95610455300423820359915765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63740303533615880239943843 95610455300423820359915765)
              ·
                refine ⟨8963480184414733158742103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95610455300423820359915765 8963480184414733158742103)
                ·
                  refine ⟨13445220276622099738113155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963480184414733158742103 13445220276622099738113155)
                  ·
                    refine ⟨20167830414933149607169733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13445220276622099738113155 20167830414933149607169733)
                    ·
                      refine ⟨3781468202799965551344325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20167830414933149607169733 3781468202799965551344325)
                      ·
                        rfl

theorem cell23_7364383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_7364383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364383 prefixEnd_7364383 := by exact prefixLift 7364383
  have htrace : WordTrace (prefixWord ++ tailWord_7364383) baseStart_7364383 baseEnd_7364383 := by
    simpa [prefixWord, tailWord_7364383, baseEnd_7364383] using wordTrace_append hprefix tailTrace_7364383
  have hstable : (prefixWord ++ tailWord_7364383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364383).length < 2 ^ (prefixWord ++ tailWord_7364383).sum := by decide
  have hdescent : baseEnd_7364383 < baseStart_7364383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364396 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_7364396 : Nat := 118140960795 + 7364396 * 2 ^ 59
def prefixEnd_7364396 : Nat := 4983230072969 + 3 ^ 40 * 7364396 * 2
def baseEnd_7364396 : Nat := 3781474878048474000481765

theorem tailTrace_7364396 : CollatzResearch.WordTrace tailWord_7364396 prefixEnd_7364396 3781474878048474000481765 := by
  unfold tailWord_7364396
  simp only [CollatzResearch.WordTrace]
  refine ⟨134300794314029252774108521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179067725752039003698811361 134300794314029252774108521)
  ·
    refine ⟨100725595735521939580581391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134300794314029252774108521 100725595735521939580581391)
    ·
      refine ⟨151088393603282909370872087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100725595735521939580581391 151088393603282909370872087)
      ·
        refine ⟨226632590404924364056308131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151088393603282909370872087 226632590404924364056308131)
        ·
          refine ⟨339948885607386546084462197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226632590404924364056308131 339948885607386546084462197)
          ·
            refine ⟨31870208025692488695418331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339948885607386546084462197 31870208025692488695418331)
            ·
              refine ⟨47805312038538733043127497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31870208025692488695418331 47805312038538733043127497)
              ·
                refine ⟨35853984028904049782345623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47805312038538733043127497 35853984028904049782345623)
                ·
                  refine ⟨53780976043356074673518435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35853984028904049782345623 53780976043356074673518435)
                  ·
                    refine ⟨80671464065034112010277653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53780976043356074673518435 80671464065034112010277653)
                    ·
                      refine ⟨3781474878048474000481765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80671464065034112010277653 3781474878048474000481765)
                      ·
                        rfl

theorem cell23_7364396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_7364396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364396 prefixEnd_7364396 := by exact prefixLift 7364396
  have htrace : WordTrace (prefixWord ++ tailWord_7364396) baseStart_7364396 baseEnd_7364396 := by
    simpa [prefixWord, tailWord_7364396, baseEnd_7364396] using wordTrace_append hprefix tailTrace_7364396
  have hstable : (prefixWord ++ tailWord_7364396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364396).length < 2 ^ (prefixWord ++ tailWord_7364396).sum := by decide
  have hdescent : baseEnd_7364396 < baseStart_7364396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364410 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_7364410 : Nat := 118140960795 + 7364410 * 2 ^ 59
def prefixEnd_7364410 : Nat := 4983230072969 + 3 ^ 40 * 7364410 * 2
def baseEnd_7364410 : Nat := 1260494022259212315235567

theorem tailTrace_7364410 : CollatzResearch.WordTrace tailWord_7364410 prefixEnd_7364410 1260494022259212315235567 := by
  unfold tailWord_7364410
  simp only [CollatzResearch.WordTrace]
  refine ⟨67150524812501946484806671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179068066166671857292817789 67150524812501946484806671)
  ·
    refine ⟨100725787218752919727210007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67150524812501946484806671 100725787218752919727210007)
    ·
      refine ⟨151088680828129379590815011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100725787218752919727210007 151088680828129379590815011)
      ·
        refine ⟨226633021242194069386222517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151088680828129379590815011 226633021242194069386222517)
        ·
          refine ⟨21246845741455694004958361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226633021242194069386222517 21246845741455694004958361)
          ·
            refine ⟨15935134306091770503718771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21246845741455694004958361 15935134306091770503718771)
            ·
              refine ⟨23902701459137655755578157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15935134306091770503718771 23902701459137655755578157)
              ·
                refine ⟨8963513047176620908341809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23902701459137655755578157 8963513047176620908341809)
                ·
                  refine ⟨6722634785382465681256357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8963513047176620908341809 6722634785382465681256357)
                  ·
                    refine ⟨1260494022259212315235567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6722634785382465681256357 1260494022259212315235567)
                    ·
                      rfl

theorem cell23_7364410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_7364410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364410 prefixEnd_7364410 := by exact prefixLift 7364410
  have htrace : WordTrace (prefixWord ++ tailWord_7364410) baseStart_7364410 baseEnd_7364410 := by
    simpa [prefixWord, tailWord_7364410, baseEnd_7364410] using wordTrace_append hprefix tailTrace_7364410
  have hstable : (prefixWord ++ tailWord_7364410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364410).length < 2 ^ (prefixWord ++ tailWord_7364410).sum := by decide
  have hdescent : baseEnd_7364410 < baseStart_7364410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364413 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7364413 : Nat := 118140960795 + 7364413 * 2 ^ 59
def prefixEnd_7364413 : Nat := 4983230072969 + 3 ^ 40 * 7364413 * 2
def baseEnd_7364413 : Nat := 3781483607219600433969187

theorem tailTrace_7364413 : CollatzResearch.WordTrace tailWord_7364413 prefixEnd_7364413 3781483607219600433969187 := by
  unfold tailWord_7364413
  simp only [CollatzResearch.WordTrace]
  refine ⟨268602208668996917451585893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179068139112664611634390595 268602208668996917451585893)
  ·
    refine ⟨50362914125436922022172355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268602208668996917451585893 50362914125436922022172355)
    ·
      refine ⟨75544371188155383033258533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50362914125436922022172355 75544371188155383033258533)
      ·
        refine ⟨14164569597779134318735975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75544371188155383033258533 14164569597779134318735975)
        ·
          refine ⟨21246854396668701478103963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14164569597779134318735975 21246854396668701478103963)
          ·
            refine ⟨31870281595003052217155945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21246854396668701478103963 31870281595003052217155945)
            ·
              refine ⟨23902711196252289162866959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31870281595003052217155945 23902711196252289162866959)
              ·
                refine ⟨35854066794378433744300439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23902711196252289162866959 35854066794378433744300439)
                ·
                  refine ⟨53781100191567650616450659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35854066794378433744300439 53781100191567650616450659)
                  ·
                    refine ⟨80671650287351475924675989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53781100191567650616450659 80671650287351475924675989)
                    ·
                      refine ⟨3781483607219600433969187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80671650287351475924675989 3781483607219600433969187)
                      ·
                        rfl

theorem cell23_7364413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7364413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364413 prefixEnd_7364413 := by exact prefixLift 7364413
  have htrace : WordTrace (prefixWord ++ tailWord_7364413) baseStart_7364413 baseEnd_7364413 := by
    simpa [prefixWord, tailWord_7364413, baseEnd_7364413] using wordTrace_append hprefix tailTrace_7364413
  have hstable : (prefixWord ++ tailWord_7364413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364413).length < 2 ^ (prefixWord ++ tailWord_7364413).sum := by decide
  have hdescent : baseEnd_7364413 < baseStart_7364413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364433 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_7364433 : Nat := 118140960795 + 7364433 * 2 ^ 59
def prefixEnd_7364433 : Nat := 4983230072969 + 3 ^ 40 * 7364433 * 2
def baseEnd_7364433 : Nat := 3781493876832690355719095

theorem tailTrace_7364433 : CollatzResearch.WordTrace tailWord_7364433 prefixEnd_7364433 3781493876832690355719095 := by
  unfold tailWord_7364433
  simp only [CollatzResearch.WordTrace]
  refine ⟨268602938128924460867313953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179068625419282973911542635 268602938128924460867313953)
  ·
    refine ⟨201452203596693345650485465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268602938128924460867313953 201452203596693345650485465)
    ·
      refine ⟨151089152697520009237864099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201452203596693345650485465 151089152697520009237864099)
      ·
        refine ⟨226633729046280013856796149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151089152697520009237864099 226633729046280013856796149)
        ·
          refine ⟨21246912098088751299074639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226633729046280013856796149 21246912098088751299074639)
          ·
            refine ⟨31870368147133126948611959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21246912098088751299074639 31870368147133126948611959)
            ·
              refine ⟨47805552220699690422917939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31870368147133126948611959 47805552220699690422917939)
              ·
                refine ⟨71708328331049535634376909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47805552220699690422917939 71708328331049535634376909)
                ·
                  refine ⟨26890623124143575862891341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71708328331049535634376909 26890623124143575862891341)
                  ·
                    refine ⟨10083983671553840948584253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26890623124143575862891341 10083983671553840948584253)
                    ·
                      refine ⟨3781493876832690355719095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083983671553840948584253 3781493876832690355719095)
                      ·
                        rfl

theorem cell23_7364433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_7364433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364433 prefixEnd_7364433 := by exact prefixLift 7364433
  have htrace : WordTrace (prefixWord ++ tailWord_7364433) baseStart_7364433 baseEnd_7364433 := by
    simpa [prefixWord, tailWord_7364433, baseEnd_7364433] using wordTrace_append hprefix tailTrace_7364433
  have hstable : (prefixWord ++ tailWord_7364433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364433).length < 2 ^ (prefixWord ++ tailWord_7364433).sum := by decide
  have hdescent : baseEnd_7364433 < baseStart_7364433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364437 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7364437 : Nat := 118140960795 + 7364437 * 2 ^ 59
def prefixEnd_7364437 : Nat := 4983230072969 + 3 ^ 40 * 7364437 * 2
def baseEnd_7364437 : Nat := 3781495930755308340069077

theorem tailTrace_7364437 : CollatzResearch.WordTrace tailWord_7364437 prefixEnd_7364437 3781495930755308340069077 := by
  unfold tailWord_7364437
  simp only [CollatzResearch.WordTrace]
  refine ⟨268603084020909969550459565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179068722680606646366973043 268603084020909969550459565)
  ·
    refine ⟨100726156507841238581422337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268603084020909969550459565 100726156507841238581422337)
    ·
      refine ⟨75544617380880928936066753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100726156507841238581422337 75544617380880928936066753)
      ·
        refine ⟨56658463035660696702050065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75544617380880928936066753 56658463035660696702050065)
        ·
          refine ⟨42493847276745522526537549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56658463035660696702050065 42493847276745522526537549)
          ·
            refine ⟨15935192728779570947451581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42493847276745522526537549 15935192728779570947451581)
            ·
              refine ⟨5975697273292339105294343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15935192728779570947451581 5975697273292339105294343)
              ·
                refine ⟨8963545909938508657941515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975697273292339105294343 8963545909938508657941515)
                ·
                  refine ⟨13445318864907762986912273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963545909938508657941515 13445318864907762986912273)
                  ·
                    refine ⟨10083989148680822240184205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13445318864907762986912273 10083989148680822240184205)
                    ·
                      refine ⟨3781495930755308340069077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10083989148680822240184205 3781495930755308340069077)
                      ·
                        rfl

theorem cell23_7364437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7364437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364437 prefixEnd_7364437 := by exact prefixLift 7364437
  have htrace : WordTrace (prefixWord ++ tailWord_7364437) baseStart_7364437 baseEnd_7364437 := by
    simpa [prefixWord, tailWord_7364437, baseEnd_7364437] using wordTrace_append hprefix tailTrace_7364437
  have hstable : (prefixWord ++ tailWord_7364437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364437).length < 2 ^ (prefixWord ++ tailWord_7364437).sum := by decide
  have hdescent : baseEnd_7364437 < baseStart_7364437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364460 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_7364460 : Nat := 118140960795 + 7364460 * 2 ^ 59
def prefixEnd_7364460 : Nat := 4983230072969 + 3 ^ 40 * 7364460 * 2
def baseEnd_7364460 : Nat := 3781507740810361750081471

theorem tailTrace_7364460 : CollatzResearch.WordTrace tailWord_7364460 prefixEnd_7364460 3781507740810361750081471 := by
  unfold tailWord_7364460
  simp only [CollatzResearch.WordTrace]
  refine ⟨134301961449913322239273417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179069281933217762985697889 134301961449913322239273417)
  ·
    refine ⟨100726471087434991679455063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134301961449913322239273417 100726471087434991679455063)
    ·
      refine ⟨151089706631152487519182595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100726471087434991679455063 151089706631152487519182595)
      ·
        refine ⟨226634559946728731278773893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151089706631152487519182595 226634559946728731278773893)
        ·
          refine ⟨42493979990011637114770105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226634559946728731278773893 42493979990011637114770105)
          ·
            refine ⟨31870484992508727836077579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42493979990011637114770105 31870484992508727836077579)
            ·
              refine ⟨47805727488763091754116369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31870484992508727836077579 47805727488763091754116369)
              ·
                refine ⟨35854295616572318815587277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47805727488763091754116369 35854295616572318815587277)
                ·
                  refine ⟨13445360856214619555845229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35854295616572318815587277 13445360856214619555845229)
                  ·
                    refine ⟨5042010321080482333441961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13445360856214619555845229 5042010321080482333441961)
                    ·
                      refine ⟨3781507740810361750081471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042010321080482333441961 3781507740810361750081471)
                      ·
                        rfl

theorem cell23_7364460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_7364460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364460 prefixEnd_7364460 := by exact prefixLift 7364460
  have htrace : WordTrace (prefixWord ++ tailWord_7364460) baseStart_7364460 baseEnd_7364460 := by
    simpa [prefixWord, tailWord_7364460, baseEnd_7364460] using wordTrace_append hprefix tailTrace_7364460
  have hstable : (prefixWord ++ tailWord_7364460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364460).length < 2 ^ (prefixWord ++ tailWord_7364460).sum := by decide
  have hdescent : baseEnd_7364460 < baseStart_7364460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364503 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_7364503 : Nat := 118140960795 + 7364503 * 2 ^ 59
def prefixEnd_7364503 : Nat := 4983230072969 + 3 ^ 40 * 7364503 * 2
def baseEnd_7364503 : Nat := 3781529820478505081843773

theorem tailTrace_7364503 : CollatzResearch.WordTrace tailWord_7364503 prefixEnd_7364503 3781529820478505081843773 := by
  unfold tailWord_7364503
  simp only [CollatzResearch.WordTrace]
  refine ⟨268605491238670862822362163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179070327492447241881574775 268605491238670862822362163)
  ·
    refine ⟨402908236858006294233543245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268605491238670862822362163 402908236858006294233543245)
    ·
      refine ⟨151090588821752360337578717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402908236858006294233543245 151090588821752360337578717)
      ·
        refine ⟨56658970808157135126592019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151090588821752360337578717 56658970808157135126592019)
        ·
          refine ⟨84988456212235702689888029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56658970808157135126592019 84988456212235702689888029)
          ·
            refine ⟨31870671079588388508708011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84988456212235702689888029 31870671079588388508708011)
            ·
              refine ⟨47806006619382582763062017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31870671079588388508708011 47806006619382582763062017)
              ·
                refine ⟨35854504964536937072296513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47806006619382582763062017 35854504964536937072296513)
                ·
                  refine ⟨26890878723402702804222385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35854504964536937072296513 26890878723402702804222385)
                  ·
                    refine ⟨20168159042552027103166789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26890878723402702804222385 20168159042552027103166789)
                    ·
                      refine ⟨3781529820478505081843773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20168159042552027103166789 3781529820478505081843773)
                      ·
                        rfl

theorem cell23_7364503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_7364503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364503 prefixEnd_7364503 := by exact prefixLift 7364503
  have htrace : WordTrace (prefixWord ++ tailWord_7364503) baseStart_7364503 baseEnd_7364503 := by
    simpa [prefixWord, tailWord_7364503, baseEnd_7364503] using wordTrace_append hprefix tailTrace_7364503
  have hstable : (prefixWord ++ tailWord_7364503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364503).length < 2 ^ (prefixWord ++ tailWord_7364503).sum := by decide
  have hdescent : baseEnd_7364503 < baseStart_7364503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364543 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 2, 5]
def baseStart_7364543 : Nat := 118140960795 + 7364543 * 2 ^ 59
def prefixEnd_7364543 : Nat := 4983230072969 + 3 ^ 40 * 7364543 * 2
def baseEnd_7364543 : Nat := 1260516786568228308447863

theorem tailTrace_7364543 : CollatzResearch.WordTrace tailWord_7364543 prefixEnd_7364543 1260516786568228308447863 := by
  unfold tailWord_7364543
  simp only [CollatzResearch.WordTrace]
  refine ⟨268606950158525949653818283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179071300105683966435878855 268606950158525949653818283)
  ·
    refine ⟨402910425237788924480727425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268606950158525949653818283 402910425237788924480727425)
    ·
      refine ⟨302182818928341693360545569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402910425237788924480727425 302182818928341693360545569)
      ·
        refine ⟨226637114196256270020409177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302182818928341693360545569 226637114196256270020409177)
        ·
          refine ⟨169977835647192202515306883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226637114196256270020409177 169977835647192202515306883)
          ·
            refine ⟨254966753470788303772960325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169977835647192202515306883 254966753470788303772960325)
            ·
              refine ⟨47806266275772806957430061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254966753470788303772960325 47806266275772806957430061)
              ·
                refine ⟨17927349853414802609036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47806266275772806957430061 17927349853414802609036273)
                ·
                  refine ⟨13445512390061101956777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17927349853414802609036273 13445512390061101956777205)
                  ·
                    refine ⟨1260516786568228308447863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13445512390061101956777205 1260516786568228308447863)
                    ·
                      rfl

theorem cell23_7364543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_7364543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364543 prefixEnd_7364543 := by exact prefixLift 7364543
  have htrace : WordTrace (prefixWord ++ tailWord_7364543) baseStart_7364543 baseEnd_7364543 := by
    simpa [prefixWord, tailWord_7364543, baseEnd_7364543] using wordTrace_append hprefix tailTrace_7364543
  have hstable : (prefixWord ++ tailWord_7364543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364543).length < 2 ^ (prefixWord ++ tailWord_7364543).sum := by decide
  have hdescent : baseEnd_7364543 < baseStart_7364543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364570 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_7364570 : Nat := 118140960795 + 7364570 * 2 ^ 59
def prefixEnd_7364570 : Nat := 4983230072969 + 3 ^ 40 * 7364570 * 2
def baseEnd_7364570 : Nat := 3781564223682356319705965

theorem tailTrace_7364570 : CollatzResearch.WordTrace tailWord_7364570 prefixEnd_7364570 3781564223682356319705965 := by
  unfold tailWord_7364570
  simp only [CollatzResearch.WordTrace]
  refine ⟨67151983732357033316262791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179071956619618755510034109 67151983732357033316262791)
  ·
    refine ⟨100727975598535549974394187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67151983732357033316262791 100727975598535549974394187)
    ·
      refine ⟨151091963397803324961591281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100727975598535549974394187 151091963397803324961591281)
      ·
        refine ⟨113318972548352493721193461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151091963397803324961591281 113318972548352493721193461)
        ·
          refine ⟨10623653676408046286361887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113318972548352493721193461 10623653676408046286361887)
          ·
            refine ⟨15935480514612069429542831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623653676408046286361887 15935480514612069429542831)
            ·
              refine ⟨23903220771918104144314247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15935480514612069429542831 23903220771918104144314247)
              ·
                refine ⟨35854831157877156216471371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23903220771918104144314247 35854831157877156216471371)
                ·
                  refine ⟨53782246736815734324707057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35854831157877156216471371 53782246736815734324707057)
                  ·
                    refine ⟨40336685052611800743530293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53782246736815734324707057 40336685052611800743530293)
                    ·
                      refine ⟨3781564223682356319705965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40336685052611800743530293 3781564223682356319705965)
                      ·
                        rfl

theorem cell23_7364570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_7364570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364570 prefixEnd_7364570 := by exact prefixLift 7364570
  have htrace : WordTrace (prefixWord ++ tailWord_7364570) baseStart_7364570 baseEnd_7364570 := by
    simpa [prefixWord, tailWord_7364570, baseEnd_7364570] using wordTrace_append hprefix tailTrace_7364570
  have hstable : (prefixWord ++ tailWord_7364570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364570).length < 2 ^ (prefixWord ++ tailWord_7364570).sum := by decide
  have hdescent : baseEnd_7364570 < baseStart_7364570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364580 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_7364580 : Nat := 118140960795 + 7364580 * 2 ^ 59
def prefixEnd_7364580 : Nat := 4983230072969 + 3 ^ 40 * 7364580 * 2
def baseEnd_7364580 : Nat := 3781569358488901280580919

theorem tailTrace_7364580 : CollatzResearch.WordTrace tailWord_7364580 prefixEnd_7364580 3781569358488901280580919 := by
  unfold tailWord_7364580
  simp only [CollatzResearch.WordTrace]
  refine ⟨134304149829695952486457597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179072199772927936648610129 134304149829695952486457597)
  ·
    refine ⟨50364056186135982182421599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134304149829695952486457597 50364056186135982182421599)
    ·
      refine ⟨75546084279203973273632399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50364056186135982182421599 75546084279203973273632399)
      ·
        refine ⟨113319126418805959910448599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75546084279203973273632399 113319126418805959910448599)
        ·
          refine ⟨169978689628208939865672899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113319126418805959910448599 169978689628208939865672899)
          ·
            refine ⟨254968034442313409798509349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169978689628208939865672899 254968034442313409798509349)
            ·
              refine ⟨47806506457933764337220503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254968034442313409798509349 47806506457933764337220503)
              ·
                refine ⟨71709759686900646505830755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47806506457933764337220503 71709759686900646505830755)
                ·
                  refine ⟨107564639530350969758746133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71709759686900646505830755 107564639530350969758746133)
                  ·
                    refine ⟨5042092477985201707441225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107564639530350969758746133 5042092477985201707441225)
                    ·
                      refine ⟨3781569358488901280580919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042092477985201707441225 3781569358488901280580919)
                      ·
                        rfl

theorem cell23_7364580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_7364580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364580 prefixEnd_7364580 := by exact prefixLift 7364580
  have htrace : WordTrace (prefixWord ++ tailWord_7364580) baseStart_7364580 baseEnd_7364580 := by
    simpa [prefixWord, tailWord_7364580, baseEnd_7364580] using wordTrace_append hprefix tailTrace_7364580
  have hstable : (prefixWord ++ tailWord_7364580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364580).length < 2 ^ (prefixWord ++ tailWord_7364580).sum := by decide
  have hdescent : baseEnd_7364580 < baseStart_7364580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364600 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_7364600 : Nat := 118140960795 + 7364600 * 2 ^ 59
def prefixEnd_7364600 : Nat := 4983230072969 + 3 ^ 40 * 7364600 * 2
def baseEnd_7364600 : Nat := 3781579628101991202330827

theorem tailTrace_7364600 : CollatzResearch.WordTrace tailWord_7364600 prefixEnd_7364600 3781579628101991202330827 := by
  unfold tailWord_7364600
  simp only [CollatzResearch.WordTrace]
  refine ⟨134304514559659724194321627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179072686079546298925762169 134304514559659724194321627)
  ·
    refine ⟨201456771839489586291482441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134304514559659724194321627 201456771839489586291482441)
    ·
      refine ⟨151092578879617189718611831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201456771839489586291482441 151092578879617189718611831)
      ·
        refine ⟨226638868319425784577917747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151092578879617189718611831 226638868319425784577917747)
        ·
          refine ⟨339958302479138676866876621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226638868319425784577917747 339958302479138676866876621)
          ·
            refine ⟨127484363429677003825078733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339958302479138676866876621 127484363429677003825078733)
            ·
              refine ⟨47806636286128876434404525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127484363429677003825078733 47806636286128876434404525)
              ·
                refine ⟨17927488607298328662901697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47806636286128876434404525 17927488607298328662901697)
                ·
                  refine ⟨13445616455473746497176273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17927488607298328662901697 13445616455473746497176273)
                  ·
                    refine ⟨10084212341605309872882205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13445616455473746497176273 10084212341605309872882205)
                    ·
                      refine ⟨3781579628101991202330827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10084212341605309872882205 3781579628101991202330827)
                      ·
                        rfl

theorem cell23_7364600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_7364600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364600 prefixEnd_7364600 := by exact prefixLift 7364600
  have htrace : WordTrace (prefixWord ++ tailWord_7364600) baseStart_7364600 baseEnd_7364600 := by
    simpa [prefixWord, tailWord_7364600, baseEnd_7364600] using wordTrace_append hprefix tailTrace_7364600
  have hstable : (prefixWord ++ tailWord_7364600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364600).length < 2 ^ (prefixWord ++ tailWord_7364600).sum := by decide
  have hdescent : baseEnd_7364600 < baseStart_7364600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364620 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 6]
def baseStart_7364620 : Nat := 118140960795 + 7364620 * 2 ^ 59
def prefixEnd_7364620 : Nat := 4983230072969 + 3 ^ 40 * 7364620 * 2
def baseEnd_7364620 : Nat := 420176655301675680453415

theorem tailTrace_7364620 : CollatzResearch.WordTrace tailWord_7364620 prefixEnd_7364620 420176655301675680453415 := by
  unfold tailWord_7364620
  simp only [CollatzResearch.WordTrace]
  refine ⟨134304879289623495902185657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179073172386164661202914209 134304879289623495902185657)
  ·
    refine ⟨100728659467217621926639243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134304879289623495902185657 100728659467217621926639243)
    ·
      refine ⟨151092989200826432889958865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100728659467217621926639243 151092989200826432889958865)
      ·
        refine ⟨113319741900619824667469149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151092989200826432889958865 113319741900619824667469149)
        ·
          refine ⟨42494903212732434250300931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113319741900619824667469149 42494903212732434250300931)
          ·
            refine ⟨63742354819098651375451397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42494903212732434250300931 63742354819098651375451397)
            ·
              refine ⟨11951691528580997132897137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63742354819098651375451397 11951691528580997132897137)
              ·
                refine ⟨8963768646435747849672853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11951691528580997132897137 8963768646435747849672853)
                ·
                  refine ⟨420176655301675680453415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8963768646435747849672853 420176655301675680453415)
                  ·
                    rfl

theorem cell23_7364620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_7364620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364620 prefixEnd_7364620 := by exact prefixLift 7364620
  have htrace : WordTrace (prefixWord ++ tailWord_7364620) baseStart_7364620 baseEnd_7364620 := by
    simpa [prefixWord, tailWord_7364620, baseEnd_7364620] using wordTrace_append hprefix tailTrace_7364620
  have hstable : (prefixWord ++ tailWord_7364620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364620).length < 2 ^ (prefixWord ++ tailWord_7364620).sum := by decide
  have hdescent : baseEnd_7364620 < baseStart_7364620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364643 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_7364643 : Nat := 118140960795 + 7364643 * 2 ^ 59
def prefixEnd_7364643 : Nat := 4983230072969 + 3 ^ 40 * 7364643 * 2
def baseEnd_7364643 : Nat := 3781601707770134534093129

theorem tailTrace_7364643 : CollatzResearch.WordTrace tailWord_7364643 prefixEnd_7364643 3781601707770134534093129 := by
  unfold tailWord_7364643
  simp only [CollatzResearch.WordTrace]
  refine ⟨268610597458163666732458583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179073731638775777821639055 268610597458163666732458583)
  ·
    refine ⟨402915896187245500098687875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268610597458163666732458583 402915896187245500098687875)
    ·
      refine ⟨604373844280868250148031813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402915896187245500098687875 604373844280868250148031813)
      ·
        refine ⟨113320095802662796902755965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604373844280868250148031813 113320095802662796902755965)
        ·
          refine ⟨42495035925998548838533487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113320095802662796902755965 42495035925998548838533487)
          ·
            refine ⟨63742553888997823257800231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42495035925998548838533487 63742553888997823257800231)
            ·
              refine ⟨95613830833496734886700347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63742553888997823257800231 95613830833496734886700347)
              ·
                refine ⟨143420746250245102330050521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95613830833496734886700347 143420746250245102330050521)
                ·
                  refine ⟨107565559687683826747537891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143420746250245102330050521 107565559687683826747537891)
                  ·
                    refine ⟨161348339531525740121306837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107565559687683826747537891 161348339531525740121306837)
                    ·
                      refine ⟨3781601707770134534093129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161348339531525740121306837 3781601707770134534093129)
                      ·
                        rfl

theorem cell23_7364643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_7364643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364643 prefixEnd_7364643 := by exact prefixLift 7364643
  have htrace : WordTrace (prefixWord ++ tailWord_7364643) baseStart_7364643 baseEnd_7364643 := by
    simpa [prefixWord, tailWord_7364643, baseEnd_7364643] using wordTrace_append hprefix tailTrace_7364643
  have hstable : (prefixWord ++ tailWord_7364643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364643).length < 2 ^ (prefixWord ++ tailWord_7364643).sum := by decide
  have hdescent : baseEnd_7364643 < baseStart_7364643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364657 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 5, 2]
def baseStart_7364657 : Nat := 118140960795 + 7364657 * 2 ^ 59
def prefixEnd_7364657 : Nat := 4983230072969 + 3 ^ 40 * 7364657 * 2
def baseEnd_7364657 : Nat := 3781608896499297479318065

theorem tailTrace_7364657 : CollatzResearch.WordTrace tailWord_7364657 prefixEnd_7364657 3781608896499297479318065 := by
  unfold tailWord_7364657
  simp only [CollatzResearch.WordTrace]
  refine ⟨268611108080112947123468225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179074072053408631415645483 268611108080112947123468225)
  ·
    refine ⟨201458331060084710342601169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268611108080112947123468225 201458331060084710342601169)
    ·
      refine ⟨151093748295063532756950877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201458331060084710342601169 151093748295063532756950877)
      ·
        refine ⟨56660155610648824783856579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151093748295063532756950877 56660155610648824783856579)
        ·
          refine ⟨84990233415973237175784869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56660155610648824783856579 84990233415973237175784869)
          ·
            refine ⟨15935668765494981970459663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84990233415973237175784869 15935668765494981970459663)
            ·
              refine ⟨23903503148242472955689495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15935668765494981970459663 23903503148242472955689495)
              ·
                refine ⟨35855254722363709433534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23903503148242472955689495 35855254722363709433534243)
                ·
                  refine ⟨53782882083545564150301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35855254722363709433534243 53782882083545564150301365)
                  ·
                    refine ⟨5042145195332396639090753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53782882083545564150301365 5042145195332396639090753)
                    ·
                      refine ⟨3781608896499297479318065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042145195332396639090753 3781608896499297479318065)
                      ·
                        rfl

theorem cell23_7364657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_7364657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364657 prefixEnd_7364657 := by exact prefixLift 7364657
  have htrace : WordTrace (prefixWord ++ tailWord_7364657) baseStart_7364657 baseEnd_7364657 := by
    simpa [prefixWord, tailWord_7364657, baseEnd_7364657] using wordTrace_append hprefix tailTrace_7364657
  have hstable : (prefixWord ++ tailWord_7364657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364657).length < 2 ^ (prefixWord ++ tailWord_7364657).sum := by decide
  have hdescent : baseEnd_7364657 < baseStart_7364657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364683 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_7364683 : Nat := 118140960795 + 7364683 * 2 ^ 59
def prefixEnd_7364683 : Nat := 4983230072969 + 3 ^ 40 * 7364683 * 2
def baseEnd_7364683 : Nat := 3781622246996314377592945

theorem tailTrace_7364683 : CollatzResearch.WordTrace tailWord_7364683 prefixEnd_7364683 3781622246996314377592945 := by
  unfold tailWord_7364683
  simp only [CollatzResearch.WordTrace]
  refine ⟨268612056378018753563914703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179074704252012502375943135 268612056378018753563914703)
  ·
    refine ⟨402918084567028130345872055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268612056378018753563914703 402918084567028130345872055)
    ·
      refine ⟨604377126850542195518808083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402918084567028130345872055 604377126850542195518808083)
      ·
        refine ⟨906565690275813293278212125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604377126850542195518808083 906565690275813293278212125)
        ·
          refine ⟨339962133853429984979329547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 906565690275813293278212125 339962133853429984979329547)
          ·
            refine ⟨509943200780144977468994321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339962133853429984979329547 509943200780144977468994321)
            ·
              refine ⟨382457400585108733101745741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509943200780144977468994321 382457400585108733101745741)
              ·
                refine ⟨143421525219415774913154653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382457400585108733101745741 143421525219415774913154653)
                ·
                  refine ⟨53783071957280915592432995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143421525219415774913154653 53783071957280915592432995)
                  ·
                    refine ⟨80674607935921373388649493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53783071957280915592432995 80674607935921373388649493)
                    ·
                      refine ⟨3781622246996314377592945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80674607935921373388649493 3781622246996314377592945)
                      ·
                        rfl

theorem cell23_7364683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_7364683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364683 prefixEnd_7364683 := by exact prefixLift 7364683
  have htrace : WordTrace (prefixWord ++ tailWord_7364683) baseStart_7364683 baseEnd_7364683 := by
    simpa [prefixWord, tailWord_7364683, baseEnd_7364683] using wordTrace_append hprefix tailTrace_7364683
  have hstable : (prefixWord ++ tailWord_7364683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364683).length < 2 ^ (prefixWord ++ tailWord_7364683).sum := by decide
  have hdescent : baseEnd_7364683 < baseStart_7364683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 7, 2, 2]
def baseStart_7364687 : Nat := 118140960795 + 7364687 * 2 ^ 59
def prefixEnd_7364687 : Nat := 4983230072969 + 3 ^ 40 * 7364687 * 2
def baseEnd_7364687 : Nat := 3781624300918932361942927

theorem tailTrace_7364687 : CollatzResearch.WordTrace tailWord_7364687 prefixEnd_7364687 3781624300918932361942927 := by
  unfold tailWord_7364687
  simp only [CollatzResearch.WordTrace]
  refine ⟨268612202270004262247060315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179074801513336174831373543 268612202270004262247060315)
  ·
    refine ⟨402918303405006393370590473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268612202270004262247060315 402918303405006393370590473)
    ·
      refine ⟨302188727553754795027942855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402918303405006393370590473 302188727553754795027942855)
      ·
        refine ⟨453283091330632192541914283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302188727553754795027942855 453283091330632192541914283)
        ·
          refine ⟨679924636995948288812871425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453283091330632192541914283 679924636995948288812871425)
          ·
            refine ⟨509943477746961216609653569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679924636995948288812871425 509943477746961216609653569)
            ·
              refine ⟨382457608310220912457240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509943477746961216609653569 382457608310220912457240177)
              ·
                refine ⟨286843206232665684342930133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382457608310220912457240177 286843206232665684342930133)
                ·
                  refine ⟨6722887646078101976787425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 286843206232665684342930133 6722887646078101976787425)
                  ·
                    refine ⟨5042165734558576482590569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6722887646078101976787425 5042165734558576482590569)
                    ·
                      refine ⟨3781624300918932361942927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042165734558576482590569 3781624300918932361942927)
                      ·
                        rfl

theorem cell23_7364687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2, 2].length) (baseStart_7364687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364687 prefixEnd_7364687 := by exact prefixLift 7364687
  have htrace : WordTrace (prefixWord ++ tailWord_7364687) baseStart_7364687 baseEnd_7364687 := by
    simpa [prefixWord, tailWord_7364687, baseEnd_7364687] using wordTrace_append hprefix tailTrace_7364687
  have hstable : (prefixWord ++ tailWord_7364687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364687).length < 2 ^ (prefixWord ++ tailWord_7364687).sum := by decide
  have hdescent : baseEnd_7364687 < baseStart_7364687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364704 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2]
def baseStart_7364704 : Nat := 118140960795 + 7364704 * 2 ^ 59
def prefixEnd_7364704 : Nat := 4983230072969 + 3 ^ 40 * 7364704 * 2
def baseEnd_7364704 : Nat := 3781633030090058795430349

theorem tailTrace_7364704 : CollatzResearch.WordTrace tailWord_7364704 prefixEnd_7364704 3781633030090058795430349 := by
  unfold tailWord_7364704
  simp only [CollatzResearch.WordTrace]
  refine ⟨134306411155471337075214583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179075214873961782766952777 134306411155471337075214583)
  ·
    refine ⟨201459616733207005612821875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134306411155471337075214583 201459616733207005612821875)
    ·
      refine ⟨302189425099810508419232813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201459616733207005612821875 302189425099810508419232813)
      ·
        refine ⟨113321034412428940657212305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302189425099810508419232813 113321034412428940657212305)
        ·
          refine ⟨84990775809321705492909229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113321034412428940657212305 84990775809321705492909229)
          ·
            refine ⟨31871540928495639559840961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84990775809321705492909229 31871540928495639559840961)
            ·
              refine ⟨23903655696371729669880721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31871540928495639559840961 23903655696371729669880721)
              ·
                refine ⟨17927741772278797252410541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23903655696371729669880721 17927741772278797252410541)
                ·
                  refine ⟨6722903164604548969653953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17927741772278797252410541 6722903164604548969653953)
                  ·
                    refine ⟨5042177373453411727240465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6722903164604548969653953 5042177373453411727240465)
                    ·
                      refine ⟨3781633030090058795430349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042177373453411727240465 3781633030090058795430349)
                      ·
                        rfl

theorem cell23_7364704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_7364704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364704 prefixEnd_7364704 := by exact prefixLift 7364704
  have htrace : WordTrace (prefixWord ++ tailWord_7364704) baseStart_7364704 baseEnd_7364704 := by
    simpa [prefixWord, tailWord_7364704, baseEnd_7364704] using wordTrace_append hprefix tailTrace_7364704
  have hstable : (prefixWord ++ tailWord_7364704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364704).length < 2 ^ (prefixWord ++ tailWord_7364704).sum := by decide
  have hdescent : baseEnd_7364704 < baseStart_7364704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364707 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 3]
def baseStart_7364707 : Nat := 118140960795 + 7364707 * 2 ^ 59
def prefixEnd_7364707 : Nat := 4983230072969 + 3 ^ 40 * 7364707 * 2
def baseEnd_7364707 : Nat := 3781634570532022283692835

theorem tailTrace_7364707 : CollatzResearch.WordTrace tailWord_7364707 prefixEnd_7364707 3781634570532022283692835 := by
  unfold tailWord_7364707
  simp only [CollatzResearch.WordTrace]
  refine ⟨268612931729931805662788375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179075287819954537108525583 268612931729931805662788375)
  ·
    refine ⟨402919397594897708494182563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268612931729931805662788375 402919397594897708494182563)
    ·
      refine ⟨604379096392346562741273845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402919397594897708494182563 604379096392346562741273845)
      ·
        refine ⟨56660540286782490256994423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 604379096392346562741273845 56660540286782490256994423)
        ·
          refine ⟨84990810430173735385491635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56660540286782490256994423 84990810430173735385491635)
          ·
            refine ⟨127486215645260603078237453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84990810430173735385491635 127486215645260603078237453)
            ·
              refine ⟨47807330866972726154339045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127486215645260603078237453 47807330866972726154339045)
              ·
                refine ⟨8963874537557386153938571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47807330866972726154339045 8963874537557386153938571)
                ·
                  refine ⟨13445811806336079230907857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963874537557386153938571 13445811806336079230907857)
                  ·
                    refine ⟨10084358854752059423180893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13445811806336079230907857 10084358854752059423180893)
                    ·
                      refine ⟨3781634570532022283692835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10084358854752059423180893 3781634570532022283692835)
                      ·
                        rfl

theorem cell23_7364707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_7364707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364707 prefixEnd_7364707 := by exact prefixLift 7364707
  have htrace : WordTrace (prefixWord ++ tailWord_7364707) baseStart_7364707 baseEnd_7364707 := by
    simpa [prefixWord, tailWord_7364707, baseEnd_7364707] using wordTrace_append hprefix tailTrace_7364707
  have hstable : (prefixWord ++ tailWord_7364707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364707).length < 2 ^ (prefixWord ++ tailWord_7364707).sum := by decide
  have hdescent : baseEnd_7364707 < baseStart_7364707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364740 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_7364740 : Nat := 118140960795 + 7364740 * 2 ^ 59
def prefixEnd_7364740 : Nat := 4983230072969 + 3 ^ 40 * 7364740 * 2
def baseEnd_7364740 : Nat := 1260550505131206884860061

theorem tailTrace_7364740 : CollatzResearch.WordTrace tailWord_7364740 prefixEnd_7364740 1260550505131206884860061 := by
  unfold tailWord_7364740
  simp only [CollatzResearch.WordTrace]
  refine ⟨134307067669406126149369837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179076090225874834865826449 134307067669406126149369837)
  ·
    refine ⟨50365150376027297306013689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134307067669406126149369837 50365150376027297306013689)
    ·
      refine ⟨37773862782020472979510267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50365150376027297306013689 37773862782020472979510267)
      ·
        refine ⟨56660794173030709469265401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37773862782020472979510267 56660794173030709469265401)
        ·
          refine ⟨42495595629773032101949051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56660794173030709469265401 42495595629773032101949051)
          ·
            refine ⟨63743393444659548152923577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42495595629773032101949051 63743393444659548152923577)
            ·
              refine ⟨47807545083494661114692683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63743393444659548152923577 47807545083494661114692683)
              ·
                refine ⟨71711317625241991672039025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47807545083494661114692683 71711317625241991672039025)
                ·
                  refine ⟨53783488218931493754029269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71711317625241991672039025 53783488218931493754029269)
                  ·
                    refine ⟨1260550505131206884860061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53783488218931493754029269 1260550505131206884860061)
                    ·
                      rfl

theorem cell23_7364740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_7364740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364740 prefixEnd_7364740 := by exact prefixLift 7364740
  have htrace : WordTrace (prefixWord ++ tailWord_7364740) baseStart_7364740 baseEnd_7364740 := by
    simpa [prefixWord, tailWord_7364740, baseEnd_7364740] using wordTrace_append hprefix tailTrace_7364740
  have hstable : (prefixWord ++ tailWord_7364740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364740).length < 2 ^ (prefixWord ++ tailWord_7364740).sum := by decide
  have hdescent : baseEnd_7364740 < baseStart_7364740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364764 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7364764 : Nat := 118140960795 + 7364764 * 2 ^ 59
def prefixEnd_7364764 : Nat := 4983230072969 + 3 ^ 40 * 7364764 * 2
def baseEnd_7364764 : Nat := 3781663838929328560680073

theorem tailTrace_7364764 : CollatzResearch.WordTrace tailWord_7364764 prefixEnd_7364764 3781663838929328560680073 := by
  unfold tailWord_7364764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134307505345362652198806673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179076673793816869598408897 134307505345362652198806673)
  ·
    refine ⟨100730629009021989149105005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134307505345362652198806673 100730629009021989149105005)
    ·
      refine ⟨37773985878383245930914377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100730629009021989149105005 37773985878383245930914377)
      ·
        refine ⟨28330489408787434448185783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37773985878383245930914377 28330489408787434448185783)
        ·
          refine ⟨42495734113181151672278675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28330489408787434448185783 42495734113181151672278675)
          ·
            refine ⟨63743601169771727508418013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42495734113181151672278675 63743601169771727508418013)
            ·
              refine ⟨23903850438664397815656755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63743601169771727508418013 23903850438664397815656755)
              ·
                refine ⟨35855775657996596723485133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23903850438664397815656755 35855775657996596723485133)
                ·
                  refine ⟨13445915871748723771306925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35855775657996596723485133 13445915871748723771306925)
                  ·
                    refine ⟨5042218451905771414240097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13445915871748723771306925 5042218451905771414240097)
                    ·
                      refine ⟨3781663838929328560680073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042218451905771414240097 3781663838929328560680073)
                      ·
                        rfl

theorem cell23_7364764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7364764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364764 prefixEnd_7364764 := by exact prefixLift 7364764
  have htrace : WordTrace (prefixWord ++ tailWord_7364764) baseStart_7364764 baseEnd_7364764 := by
    simpa [prefixWord, tailWord_7364764, baseEnd_7364764] using wordTrace_append hprefix tailTrace_7364764
  have hstable : (prefixWord ++ tailWord_7364764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364764).length < 2 ^ (prefixWord ++ tailWord_7364764).sum := by decide
  have hdescent : baseEnd_7364764 < baseStart_7364764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364789 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7364789 : Nat := 118140960795 + 7364789 * 2 ^ 59
def prefixEnd_7364789 : Nat := 4983230072969 + 3 ^ 40 * 7364789 * 2
def baseEnd_7364789 : Nat := 3781676675945690962867459

theorem tailTrace_7364789 : CollatzResearch.WordTrace tailWord_7364789 prefixEnd_7364789 3781676675945690962867459 := by
  unfold tailWord_7364789
  simp only [CollatzResearch.WordTrace]
  refine ⟨268615922515634733667273421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179077281677089822444848947 268615922515634733667273421)
  ·
    refine ⟨100730970943363025125227533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268615922515634733667273421 100730970943363025125227533)
    ·
      refine ⟨37774114103761134421960325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100730970943363025125227533 37774114103761134421960325)
      ·
        refine ⟨7082646394455212704117561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37774114103761134421960325 7082646394455212704117561)
        ·
          refine ⟨5311984795841409528088171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7082646394455212704117561 5311984795841409528088171)
          ·
            refine ⟨7967977193762114292132257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311984795841409528088171 7967977193762114292132257)
            ·
              refine ⟨5975982895321585719099193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967977193762114292132257 5975982895321585719099193)
              ·
                refine ⟨4481987171491189289324395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5975982895321585719099193 4481987171491189289324395)
                ·
                  refine ⟨6722980757236783933986593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481987171491189289324395 6722980757236783933986593)
                  ·
                    refine ⟨5042235567927587950489945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6722980757236783933986593 5042235567927587950489945)
                    ·
                      refine ⟨3781676675945690962867459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042235567927587950489945 3781676675945690962867459)
                      ·
                        rfl

theorem cell23_7364789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7364789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364789 prefixEnd_7364789 := by exact prefixLift 7364789
  have htrace : WordTrace (prefixWord ++ tailWord_7364789) baseStart_7364789 baseEnd_7364789 := by
    simpa [prefixWord, tailWord_7364789, baseEnd_7364789] using wordTrace_append hprefix tailTrace_7364789
  have hstable : (prefixWord ++ tailWord_7364789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364789).length < 2 ^ (prefixWord ++ tailWord_7364789).sum := by decide
  have hdescent : baseEnd_7364789 < baseStart_7364789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364794 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_7364794 : Nat := 118140960795 + 7364794 * 2 ^ 59
def prefixEnd_7364794 : Nat := 4983230072969 + 3 ^ 40 * 7364794 * 2
def baseEnd_7364794 : Nat := 3781679243348963443304935

theorem tailTrace_7364794 : CollatzResearch.WordTrace tailWord_7364794 prefixEnd_7364794 3781679243348963443304935 := by
  unfold tailWord_7364794
  simp only [CollatzResearch.WordTrace]
  refine ⟨67154026220154154880301359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179077403253744413014136957 67154026220154154880301359)
  ·
    refine ⟨100731039330231232320452039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67154026220154154880301359 100731039330231232320452039)
    ·
      refine ⟨151096558995346848480678059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100731039330231232320452039 151096558995346848480678059)
      ·
        refine ⟨226644838493020272721017089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151096558995346848480678059 226644838493020272721017089)
        ·
          refine ⟨169983628869765204540762817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226644838493020272721017089 169983628869765204540762817)
          ·
            refine ⟨127487721652323903405572113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169983628869765204540762817 127487721652323903405572113)
            ·
              refine ⟨95615791239242927554179085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127487721652323903405572113 95615791239242927554179085)
              ·
                refine ⟨35855921714716097832817157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95615791239242927554179085 35855921714716097832817157)
                ·
                  refine ⟨6722985321509268343653217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35855921714716097832817157 6722985321509268343653217)
                  ·
                    refine ⟨5042238991131951257739913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6722985321509268343653217 5042238991131951257739913)
                    ·
                      refine ⟨3781679243348963443304935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042238991131951257739913 3781679243348963443304935)
                      ·
                        rfl

theorem cell23_7364794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_7364794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364794 prefixEnd_7364794 := by exact prefixLift 7364794
  have htrace : WordTrace (prefixWord ++ tailWord_7364794) baseStart_7364794 baseEnd_7364794 := by
    simpa [prefixWord, tailWord_7364794, baseEnd_7364794] using wordTrace_append hprefix tailTrace_7364794
  have hstable : (prefixWord ++ tailWord_7364794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364794).length < 2 ^ (prefixWord ++ tailWord_7364794).sum := by decide
  have hdescent : baseEnd_7364794 < baseStart_7364794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364845 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7364845 : Nat := 118140960795 + 7364845 * 2 ^ 59
def prefixEnd_7364845 : Nat := 4983230072969 + 3 ^ 40 * 7364845 * 2
def baseEnd_7364845 : Nat := 3781705430862342743767201

theorem tailTrace_7364845 : CollatzResearch.WordTrace tailWord_7364845 prefixEnd_7364845 3781705430862342743767201 := by
  unfold tailWord_7364845
  simp only [CollatzResearch.WordTrace]
  refine ⟨268617965003431855231311989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179078643335621236820874659 268617965003431855231311989)
  ·
    refine ⟨25182934219071736427935499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268617965003431855231311989 25182934219071736427935499)
    ·
      refine ⟨37774401328607604641903249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25182934219071736427935499 37774401328607604641903249)
      ·
        refine ⟨28330800996455703481427437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37774401328607604641903249 28330800996455703481427437)
        ·
          refine ⟨10624050373670888805535289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28330800996455703481427437 10624050373670888805535289)
          ·
            refine ⟨7968037780253166604151467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10624050373670888805535289 7968037780253166604151467)
            ·
              refine ⟨11952056670379749906227201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968037780253166604151467 11952056670379749906227201)
              ·
                refine ⟨8964042502784812429670401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952056670379749906227201 8964042502784812429670401)
                ·
                  refine ⟨6723031877088609322252801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8964042502784812429670401 6723031877088609322252801)
                  ·
                    refine ⟨5042273907816456991689601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6723031877088609322252801 5042273907816456991689601)
                    ·
                      refine ⟨3781705430862342743767201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042273907816456991689601 3781705430862342743767201)
                      ·
                        rfl

theorem cell23_7364845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7364845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364845 prefixEnd_7364845 := by exact prefixLift 7364845
  have htrace : WordTrace (prefixWord ++ tailWord_7364845) baseStart_7364845 baseEnd_7364845 := by
    simpa [prefixWord, tailWord_7364845, baseEnd_7364845] using wordTrace_append hprefix tailTrace_7364845
  have hstable : (prefixWord ++ tailWord_7364845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364845).length < 2 ^ (prefixWord ++ tailWord_7364845).sum := by decide
  have hdescent : baseEnd_7364845 < baseStart_7364845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364854 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7364854 : Nat := 118140960795 + 7364854 * 2 ^ 59
def prefixEnd_7364854 : Nat := 4983230072969 + 3 ^ 40 * 7364854 * 2
def baseEnd_7364854 : Nat := 3781710052188233208554659

theorem tailTrace_7364854 : CollatzResearch.WordTrace tailWord_7364854 prefixEnd_7364854 3781710052188233208554659 := by
  unfold tailWord_7364854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788643328774953110524351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179078862173599499845593077 16788643328774953110524351)
  ·
    refine ⟨25182964993162429665786527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16788643328774953110524351 25182964993162429665786527)
    ·
      refine ⟨37774447489743644498679791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25182964993162429665786527 37774447489743644498679791)
      ·
        refine ⟨56661671234615466748019687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37774447489743644498679791 56661671234615466748019687)
        ·
          refine ⟨84992506851923200122029531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56661671234615466748019687 84992506851923200122029531)
          ·
            refine ⟨127488760277884800183044297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84992506851923200122029531 127488760277884800183044297)
            ·
              refine ⟨95616570208413600137283223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127488760277884800183044297 95616570208413600137283223)
              ·
                refine ⟨143424855312620400205924835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95616570208413600137283223 143424855312620400205924835)
                ·
                  refine ⟨215137282968930600308887253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143424855312620400205924835 215137282968930600308887253)
                  ·
                    refine ⟨5042280069584310944739545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215137282968930600308887253 5042280069584310944739545)
                    ·
                      refine ⟨3781710052188233208554659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042280069584310944739545 3781710052188233208554659)
                      ·
                        rfl

theorem cell23_7364854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7364854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364854 prefixEnd_7364854 := by exact prefixLift 7364854
  have htrace : WordTrace (prefixWord ++ tailWord_7364854) baseStart_7364854 baseEnd_7364854 := by
    simpa [prefixWord, tailWord_7364854, baseEnd_7364854] using wordTrace_append hprefix tailTrace_7364854
  have hstable : (prefixWord ++ tailWord_7364854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364854).length < 2 ^ (prefixWord ++ tailWord_7364854).sum := by decide
  have hdescent : baseEnd_7364854 < baseStart_7364854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364977 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7364977 : Nat := 118140960795 + 7364977 * 2 ^ 59
def prefixEnd_7364977 : Nat := 4983230072969 + 3 ^ 40 * 7364977 * 2
def baseEnd_7364977 : Nat := 3781773210308736227316593

theorem tailTrace_7364977 : CollatzResearch.WordTrace tailWord_7364977 prefixEnd_7364977 3781773210308736227316593 := by
  unfold tailWord_7364977
  simp only [CollatzResearch.WordTrace]
  refine ⟨268622779438953641775117185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179081852959302427850078123 268622779438953641775117185)
  ·
    refine ⟨201467084579215231331337889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268622779438953641775117185 201467084579215231331337889)
    ·
      refine ⟨151100313434411423498503417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201467084579215231331337889 151100313434411423498503417)
      ·
        refine ⟨113325235075808567623877563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151100313434411423498503417 113325235075808567623877563)
        ·
          refine ⟨169987852613712851435816345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113325235075808567623877563 169987852613712851435816345)
          ·
            refine ⟨127490889460284638576862259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169987852613712851435816345 127490889460284638576862259)
            ·
              refine ⟨191236334190426957865293389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127490889460284638576862259 191236334190426957865293389)
              ·
                refine ⟨71713625321410109199485021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191236334190426957865293389 71713625321410109199485021)
                ·
                  refine ⟨26892609495528790949806883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71713625321410109199485021 26892609495528790949806883)
                  ·
                    refine ⟨40338914243293186424710325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26892609495528790949806883 40338914243293186424710325)
                    ·
                      refine ⟨3781773210308736227316593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40338914243293186424710325 3781773210308736227316593)
                      ·
                        rfl

theorem cell23_7364977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7364977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364977 prefixEnd_7364977 := by exact prefixLift 7364977
  have htrace : WordTrace (prefixWord ++ tailWord_7364977) baseStart_7364977 baseEnd_7364977 := by
    simpa [prefixWord, tailWord_7364977, baseEnd_7364977] using wordTrace_append hprefix tailTrace_7364977
  have hstable : (prefixWord ++ tailWord_7364977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364977).length < 2 ^ (prefixWord ++ tailWord_7364977).sum := by decide
  have hdescent : baseEnd_7364977 < baseStart_7364977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364991 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 3, 2, 2]
def baseStart_7364991 : Nat := 118140960795 + 7364991 * 2 ^ 59
def prefixEnd_7364991 : Nat := 4983230072969 + 3 ^ 40 * 7364991 * 2
def baseEnd_7364991 : Nat := 3781780399037899172541529

theorem tailTrace_7364991 : CollatzResearch.WordTrace tailWord_7364991 prefixEnd_7364991 3781780399037899172541529 := by
  unfold tailWord_7364991
  simp only [CollatzResearch.WordTrace]
  refine ⟨268623290060902922166126827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179082193373935281444084551 268623290060902922166126827)
  ·
    refine ⟨402934935091354383249190241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268623290060902922166126827 402934935091354383249190241)
    ·
      refine ⟨302201201318515787436892681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402934935091354383249190241 302201201318515787436892681)
      ·
        refine ⟨226650900988886840577669511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302201201318515787436892681 226650900988886840577669511)
        ·
          refine ⟨339976351483330260866504267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226650900988886840577669511 339976351483330260866504267)
          ·
            refine ⟨509964527224995391299756401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339976351483330260866504267 509964527224995391299756401)
            ·
              refine ⟨382473395418746543474817301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509964527224995391299756401 382473395418746543474817301)
              ·
                refine ⟨17928440410253744225382061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 382473395418746543474817301 17928440410253744225382061)
                ·
                  refine ⟨6723165153845154084518273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17928440410253744225382061 6723165153845154084518273)
                  ·
                    refine ⟨5042373865383865563388705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6723165153845154084518273 5042373865383865563388705)
                    ·
                      refine ⟨3781780399037899172541529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042373865383865563388705 3781780399037899172541529)
                      ·
                        rfl

theorem cell23_7364991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_7364991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364991 prefixEnd_7364991 := by exact prefixLift 7364991
  have htrace : WordTrace (prefixWord ++ tailWord_7364991) baseStart_7364991 baseEnd_7364991 := by
    simpa [prefixWord, tailWord_7364991, baseEnd_7364991] using wordTrace_append hprefix tailTrace_7364991
  have hstable : (prefixWord ++ tailWord_7364991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364991).length < 2 ^ (prefixWord ++ tailWord_7364991).sum := by decide
  have hdescent : baseEnd_7364991 < baseStart_7364991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7364995 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 2, 3, 2]
def baseStart_7364995 : Nat := 118140960795 + 7364995 * 2 ^ 59
def prefixEnd_7364995 : Nat := 4983230072969 + 3 ^ 40 * 7364995 * 2
def baseEnd_7364995 : Nat := 3781782452960517156891511

theorem tailTrace_7364995 : CollatzResearch.WordTrace tailWord_7364995 prefixEnd_7364995 3781782452960517156891511 := by
  unfold tailWord_7364995
  simp only [CollatzResearch.WordTrace]
  refine ⟨268623435952888430849272439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179082290635258953899514959 268623435952888430849272439)
  ·
    refine ⟨402935153929332646273908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268623435952888430849272439 402935153929332646273908659)
    ·
      refine ⟨604402730893998969410862989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402935153929332646273908659 604402730893998969410862989)
      ·
        refine ⟨226651024085249613529073621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604402730893998969410862989 226651024085249613529073621)
        ·
          refine ⟨5312133376998037817087663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226651024085249613529073621 5312133376998037817087663)
          ·
            refine ⟨7968200065497056725631495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312133376998037817087663 7968200065497056725631495)
            ·
              refine ⟨11952300098245585088447243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968200065497056725631495 11952300098245585088447243)
              ·
                refine ⟨17928450147368377632670865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11952300098245585088447243 17928450147368377632670865)
                ·
                  refine ⟨13446337610526283224503149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17928450147368377632670865 13446337610526283224503149)
                  ·
                    refine ⟨5042376603947356209188681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13446337610526283224503149 5042376603947356209188681)
                    ·
                      refine ⟨3781782452960517156891511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042376603947356209188681 3781782452960517156891511)
                      ·
                        rfl

theorem cell23_7364995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_7364995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7364995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7364995 prefixEnd_7364995 := by exact prefixLift 7364995
  have htrace : WordTrace (prefixWord ++ tailWord_7364995) baseStart_7364995 baseEnd_7364995 := by
    simpa [prefixWord, tailWord_7364995, baseEnd_7364995] using wordTrace_append hprefix tailTrace_7364995
  have hstable : (prefixWord ++ tailWord_7364995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7364995).length < 2 ^ (prefixWord ++ tailWord_7364995).sum := by decide
  have hdescent : baseEnd_7364995 < baseStart_7364995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7364995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365002 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7365002 : Nat := 118140960795 + 7365002 * 2 ^ 59
def prefixEnd_7365002 : Nat := 4983230072969 + 3 ^ 40 * 7365002 * 2
def baseEnd_7365002 : Nat := 3781786047325098629503979

theorem tailTrace_7365002 : CollatzResearch.WordTrace tailWord_7365002 prefixEnd_7365002 3781786047325098629503979 := by
  unfold tailWord_7365002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67155922815965767761194315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179082460842575380696518173 67155922815965767761194315)
  ·
    refine ⟨100733884223948651641791473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67155922815965767761194315 100733884223948651641791473)
    ·
      refine ⟨75550413167961488731343605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100733884223948651641791473 75550413167961488731343605)
      ·
        refine ⟨7082851234496389568563463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75550413167961488731343605 7082851234496389568563463)
        ·
          refine ⟨10624276851744584352845195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082851234496389568563463 10624276851744584352845195)
          ·
            refine ⟨15936415277616876529267793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10624276851744584352845195 15936415277616876529267793)
            ·
              refine ⟨11952311458212657396950845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15936415277616876529267793 11952311458212657396950845)
              ·
                refine ⟨4482116796829746523856567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11952311458212657396950845 4482116796829746523856567)
                ·
                  refine ⟨6723175195244619785784851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482116796829746523856567 6723175195244619785784851)
                  ·
                    refine ⟨10084762792866929678677277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723175195244619785784851 10084762792866929678677277)
                    ·
                      refine ⟨3781786047325098629503979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10084762792866929678677277 3781786047325098629503979)
                      ·
                        rfl

theorem cell23_7365002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7365002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365002 prefixEnd_7365002 := by exact prefixLift 7365002
  have htrace : WordTrace (prefixWord ++ tailWord_7365002) baseStart_7365002 baseEnd_7365002 := by
    simpa [prefixWord, tailWord_7365002, baseEnd_7365002] using wordTrace_append hprefix tailTrace_7365002
  have hstable : (prefixWord ++ tailWord_7365002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365002).length < 2 ^ (prefixWord ++ tailWord_7365002).sum := by decide
  have hdescent : baseEnd_7365002 < baseStart_7365002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365004 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7365004 : Nat := 118140960795 + 7365004 * 2 ^ 59
def prefixEnd_7365004 : Nat := 4983230072969 + 3 ^ 40 * 7365004 * 2
def baseEnd_7365004 : Nat := 3781787074286407621678969

theorem tailTrace_7365004 : CollatzResearch.WordTrace tailWord_7365004 prefixEnd_7365004 3781787074286407621678969 := by
  unfold tailWord_7365004
  simp only [CollatzResearch.WordTrace]
  refine ⟨134311882104927912693175033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179082509473237216924233377 134311882104927912693175033)
  ·
    refine ⟨100733911578695934519881275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134311882104927912693175033 100733911578695934519881275)
    ·
      refine ⟨151100867368043901779821913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100733911578695934519881275 151100867368043901779821913)
      ·
        refine ⟨113325650526032926334866435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151100867368043901779821913 113325650526032926334866435)
        ·
          refine ⟨169988475789049389502299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113325650526032926334866435 169988475789049389502299653)
          ·
            refine ⟨31872839210446760531681185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169988475789049389502299653 31872839210446760531681185)
            ·
              refine ⟨23904629407835070398760889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31872839210446760531681185 23904629407835070398760889)
              ·
                refine ⟨17928472055876302799070667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23904629407835070398760889 17928472055876302799070667)
                ·
                  refine ⟨26892708083814454198606001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17928472055876302799070667 26892708083814454198606001)
                  ·
                    refine ⟨20169531062860840648954501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26892708083814454198606001 20169531062860840648954501)
                    ·
                      refine ⟨3781787074286407621678969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20169531062860840648954501 3781787074286407621678969)
                      ·
                        rfl

theorem cell23_7365004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7365004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365004 prefixEnd_7365004 := by exact prefixLift 7365004
  have htrace : WordTrace (prefixWord ++ tailWord_7365004) baseStart_7365004 baseEnd_7365004 := by
    simpa [prefixWord, tailWord_7365004, baseEnd_7365004] using wordTrace_append hprefix tailTrace_7365004
  have hstable : (prefixWord ++ tailWord_7365004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365004).length < 2 ^ (prefixWord ++ tailWord_7365004).sum := by decide
  have hdescent : baseEnd_7365004 < baseStart_7365004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365018 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_7365018 : Nat := 118140960795 + 7365018 * 2 ^ 59
def prefixEnd_7365018 : Nat := 4983230072969 + 3 ^ 40 * 7365018 * 2
def baseEnd_7365018 : Nat := 1260598087671856855634635

theorem tailTrace_7365018 : CollatzResearch.WordTrace tailWord_7365018 prefixEnd_7365018 1260598087671856855634635 := by
  unfold tailWord_7365018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67156068707951276444339927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179082849887870070518239805 67156068707951276444339927)
  ·
    refine ⟨100734103061926914666509891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67156068707951276444339927 100734103061926914666509891)
    ·
      refine ⟨151101154592890371999764837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100734103061926914666509891 151101154592890371999764837)
      ·
        refine ⟨28331466486166944749955907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151101154592890371999764837 28331466486166944749955907)
        ·
          refine ⟨42497199729250417124933861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28331466486166944749955907 42497199729250417124933861)
          ·
            refine ⟨7968224949234453210925099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42497199729250417124933861 7968224949234453210925099)
            ·
              refine ⟨11952337423851679816387649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968224949234453210925099 11952337423851679816387649)
              ·
                refine ⟨8964253067888759862290737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952337423851679816387649 8964253067888759862290737)
                ·
                  refine ⟨6723189800916569896718053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8964253067888759862290737 6723189800916569896718053)
                  ·
                    refine ⟨1260598087671856855634635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6723189800916569896718053 1260598087671856855634635)
                    ·
                      rfl

theorem cell23_7365018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_7365018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365018 prefixEnd_7365018 := by exact prefixLift 7365018
  have htrace : WordTrace (prefixWord ++ tailWord_7365018) baseStart_7365018 baseEnd_7365018 := by
    simpa [prefixWord, tailWord_7365018, baseEnd_7365018] using wordTrace_append hprefix tailTrace_7365018
  have hstable : (prefixWord ++ tailWord_7365018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365018).length < 2 ^ (prefixWord ++ tailWord_7365018).sum := by decide
  have hdescent : baseEnd_7365018 < baseStart_7365018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365041 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_7365041 : Nat := 118140960795 + 7365041 * 2 ^ 59
def prefixEnd_7365041 : Nat := 4983230072969 + 3 ^ 40 * 7365041 * 2
def baseEnd_7365041 : Nat := 3781806073070623976916299

theorem tailTrace_7365041 : CollatzResearch.WordTrace tailWord_7365041 prefixEnd_7365041 3781806073070623976916299 := by
  unfold tailWord_7365041
  simp only [CollatzResearch.WordTrace]
  refine ⟨268625113710721780705446977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179083409140481187136964651 268625113710721780705446977)
  ·
    refine ⟨201468835283041335529085233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268625113710721780705446977 201468835283041335529085233)
    ·
      refine ⟨151101626462281001646813925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201468835283041335529085233 151101626462281001646813925)
      ·
        refine ⟨28331554961677687808777611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151101626462281001646813925 28331554961677687808777611)
        ·
          refine ⟨42497332442516531713166417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28331554961677687808777611 42497332442516531713166417)
          ·
            refine ⟨31872999331887398784874813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42497332442516531713166417 31872999331887398784874813)
            ·
              refine ⟨11952374749457774544328055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31872999331887398784874813 11952374749457774544328055)
              ·
                refine ⟨17928562124186661816492083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11952374749457774544328055 17928562124186661816492083)
                ·
                  refine ⟨26892843186279992724738125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17928562124186661816492083 26892843186279992724738125)
                  ·
                    refine ⟨10084816194854997271776797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26892843186279992724738125 10084816194854997271776797)
                    ·
                      refine ⟨3781806073070623976916299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10084816194854997271776797 3781806073070623976916299)
                      ·
                        rfl

theorem cell23_7365041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_7365041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365041 prefixEnd_7365041 := by exact prefixLift 7365041
  have htrace : WordTrace (prefixWord ++ tailWord_7365041) baseStart_7365041 baseEnd_7365041 := by
    simpa [prefixWord, tailWord_7365041, baseEnd_7365041] using wordTrace_append hprefix tailTrace_7365041
  have hstable : (prefixWord ++ tailWord_7365041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365041).length < 2 ^ (prefixWord ++ tailWord_7365041).sum := by decide
  have hdescent : baseEnd_7365041 < baseStart_7365041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365054 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_7365054 : Nat := 118140960795 + 7365054 * 2 ^ 59
def prefixEnd_7365054 : Nat := 4983230072969 + 3 ^ 40 * 7365054 * 2
def baseEnd_7365054 : Nat := 3781812748319132426053739

theorem tailTrace_7365054 : CollatzResearch.WordTrace tailWord_7365054 prefixEnd_7365054 3781812748319132426053739 := by
  unfold tailWord_7365054
  simp only [CollatzResearch.WordTrace]
  refine ⟨33578198482459335490708777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179083725239783122617113477 33578198482459335490708777)
  ·
    refine ⟨25183648861844501618031583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33578198482459335490708777 25183648861844501618031583)
    ·
      refine ⟨37775473292766752427047375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183648861844501618031583 37775473292766752427047375)
      ·
        refine ⟨56663209939150128640571063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37775473292766752427047375 56663209939150128640571063)
        ·
          refine ⟨84994814908725192960856595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56663209939150128640571063 84994814908725192960856595)
          ·
            refine ⟨127492222363087789441284893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84994814908725192960856595 127492222363087789441284893)
            ·
              refine ⟨47809583386157921040481835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127492222363087789441284893 47809583386157921040481835)
              ·
                refine ⟨71714375079236881560722753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47809583386157921040481835 71714375079236881560722753)
                ·
                  refine ⟨53785781309427661170542065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71714375079236881560722753 53785781309427661170542065)
                  ·
                    refine ⟨40339335982070745877906549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53785781309427661170542065 40339335982070745877906549)
                    ·
                      refine ⟨3781812748319132426053739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40339335982070745877906549 3781812748319132426053739)
                      ·
                        rfl

theorem cell23_7365054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_7365054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365054 prefixEnd_7365054 := by exact prefixLift 7365054
  have htrace : WordTrace (prefixWord ++ tailWord_7365054) baseStart_7365054 baseEnd_7365054 := by
    simpa [prefixWord, tailWord_7365054, baseEnd_7365054] using wordTrace_append hprefix tailTrace_7365054
  have hstable : (prefixWord ++ tailWord_7365054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365054).length < 2 ^ (prefixWord ++ tailWord_7365054).sum := by decide
  have hdescent : baseEnd_7365054 < baseStart_7365054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365101 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7365101 : Nat := 118140960795 + 7365101 * 2 ^ 59
def prefixEnd_7365101 : Nat := 4983230072969 + 3 ^ 40 * 7365101 * 2
def baseEnd_7365101 : Nat := 3781836881909893742166023

theorem tailTrace_7365101 : CollatzResearch.WordTrace tailWord_7365101 prefixEnd_7365101 3781836881909893742166023 := by
  unfold tailWord_7365101
  simp only [CollatzResearch.WordTrace]
  refine ⟨268627302090504410952631157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179084868060336273968420771 268627302090504410952631157)
  ·
    refine ⟨25183809570984788526809171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268627302090504410952631157 25183809570984788526809171)
    ·
      refine ⟨37775714356477182790213757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183809570984788526809171 37775714356477182790213757)
      ·
        refine ⟨14165892883678943546330159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37775714356477182790213757 14165892883678943546330159)
        ·
          refine ⟨21248839325518415319495239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14165892883678943546330159 21248839325518415319495239)
          ·
            refine ⟨31873258988277622979242859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21248839325518415319495239 31873258988277622979242859)
            ·
              refine ⟨47809888482416434468864289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31873258988277622979242859 47809888482416434468864289)
              ·
                refine ⟨35857416361812325851648217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47809888482416434468864289 35857416361812325851648217)
                ·
                  refine ⟨26893062271359244388736163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35857416361812325851648217 26893062271359244388736163)
                  ·
                    refine ⟨40339593407038866583104245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26893062271359244388736163 40339593407038866583104245)
                    ·
                      refine ⟨3781836881909893742166023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40339593407038866583104245 3781836881909893742166023)
                      ·
                        rfl

theorem cell23_7365101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7365101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365101 prefixEnd_7365101 := by exact prefixLift 7365101
  have htrace : WordTrace (prefixWord ++ tailWord_7365101) baseStart_7365101 baseEnd_7365101 := by
    simpa [prefixWord, tailWord_7365101, baseEnd_7365101] using wordTrace_append hprefix tailTrace_7365101
  have hstable : (prefixWord ++ tailWord_7365101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365101).length < 2 ^ (prefixWord ++ tailWord_7365101).sum := by decide
  have hdescent : baseEnd_7365101 < baseStart_7365101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365114 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_7365114 : Nat := 118140960795 + 7365114 * 2 ^ 59
def prefixEnd_7365114 : Nat := 4983230072969 + 3 ^ 40 * 7365114 * 2
def baseEnd_7365114 : Nat := 3781843557158402191303463

theorem tailTrace_7365114 : CollatzResearch.WordTrace tailWord_7365114 prefixEnd_7365114 3781843557158402191303463 := by
  unfold tailWord_7365114
  simp only [CollatzResearch.WordTrace]
  refine ⟨67156944059864328543213599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179085184159638209448569597 67156944059864328543213599)
  ·
    refine ⟨100735416089796492814820399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67156944059864328543213599 100735416089796492814820399)
    ·
      refine ⟨151103124134694739222230599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100735416089796492814820399 151103124134694739222230599)
      ·
        refine ⟨226654686202042108833345899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151103124134694739222230599 226654686202042108833345899)
        ·
          refine ⟨339982029303063163250018849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226654686202042108833345899 339982029303063163250018849)
          ·
            refine ⟨254986521977297372437514137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339982029303063163250018849 254986521977297372437514137)
            ·
              refine ⟨191239891482973029328135603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254986521977297372437514137 191239891482973029328135603)
              ·
                refine ⟨286859837224459543992203405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191239891482973029328135603 286859837224459543992203405)
                ·
                  refine ⟨107572438959172328997076277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286859837224459543992203405 107572438959172328997076277)
                  ·
                    refine ⟨10084916152422405843475901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107572438959172328997076277 10084916152422405843475901)
                    ·
                      refine ⟨3781843557158402191303463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10084916152422405843475901 3781843557158402191303463)
                      ·
                        rfl

theorem cell23_7365114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_7365114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365114 prefixEnd_7365114 := by exact prefixLift 7365114
  have htrace : WordTrace (prefixWord ++ tailWord_7365114) baseStart_7365114 baseEnd_7365114 := by
    simpa [prefixWord, tailWord_7365114, baseEnd_7365114] using wordTrace_append hprefix tailTrace_7365114
  have hstable : (prefixWord ++ tailWord_7365114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365114).length < 2 ^ (prefixWord ++ tailWord_7365114).sum := by decide
  have hdescent : baseEnd_7365114 < baseStart_7365114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365141 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_7365141 : Nat := 118140960795 + 7365141 * 2 ^ 59
def prefixEnd_7365141 : Nat := 4983230072969 + 3 ^ 40 * 7365141 * 2
def baseEnd_7365141 : Nat := 3781857421136073585665839

theorem tailTrace_7365141 : CollatzResearch.WordTrace tailWord_7365141 prefixEnd_7365141 3781857421136073585665839 := by
  unfold tailWord_7365141
  simp only [CollatzResearch.WordTrace]
  refine ⟨268628761010359497784087277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179085840673572998522724851 268628761010359497784087277)
  ·
    refine ⟨100735785378884811669032729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268628761010359497784087277 100735785378884811669032729)
    ·
      refine ⟨75551839034163608751774547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100735785378884811669032729 75551839034163608751774547)
      ·
        refine ⟨113327758551245413127661821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75551839034163608751774547 113327758551245413127661821)
        ·
          refine ⟨42497909456717029922873183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113327758551245413127661821 42497909456717029922873183)
          ·
            refine ⟨63746864185075544884309775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42497909456717029922873183 63746864185075544884309775)
            ·
              refine ⟨95620296277613317326464663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63746864185075544884309775 95620296277613317326464663)
              ·
                refine ⟨143430444416419975989696995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95620296277613317326464663 143430444416419975989696995)
                ·
                  refine ⟨215145666624629963984545493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143430444416419975989696995 215145666624629963984545493)
                  ·
                    refine ⟨5042476561514764780887785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215145666624629963984545493 5042476561514764780887785)
                    ·
                      refine ⟨3781857421136073585665839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042476561514764780887785 3781857421136073585665839)
                      ·
                        rfl

theorem cell23_7365141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_7365141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365141 prefixEnd_7365141 := by exact prefixLift 7365141
  have htrace : WordTrace (prefixWord ++ tailWord_7365141) baseStart_7365141 baseEnd_7365141 := by
    simpa [prefixWord, tailWord_7365141, baseEnd_7365141] using wordTrace_append hprefix tailTrace_7365141
  have hstable : (prefixWord ++ tailWord_7365141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365141).length < 2 ^ (prefixWord ++ tailWord_7365141).sum := by decide
  have hdescent : baseEnd_7365141 < baseStart_7365141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365171 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 6, 2]
def baseStart_7365171 : Nat := 118140960795 + 7365171 * 2 ^ 59
def prefixEnd_7365171 : Nat := 4983230072969 + 3 ^ 40 * 7365171 * 2
def baseEnd_7365171 : Nat := 3781872825555708468290701

theorem tailTrace_7365171 : CollatzResearch.WordTrace tailWord_7365171 prefixEnd_7365171 3781872825555708468290701 := by
  unfold tailWord_7365171
  simp only [CollatzResearch.WordTrace]
  refine ⟨268629855200250812907679367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179086570133500541938452911 268629855200250812907679367)
  ·
    refine ⟨402944782800376219361519051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268629855200250812907679367 402944782800376219361519051)
    ·
      refine ⟨604417174200564329042278577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402944782800376219361519051 604417174200564329042278577)
      ·
        refine ⟨453312880650423246781708933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604417174200564329042278577 453312880650423246781708933)
        ·
          refine ⟨84996165121954358771570425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453312880650423246781708933 84996165121954358771570425)
          ·
            refine ⟨63747123841465769078677819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84996165121954358771570425 63747123841465769078677819)
            ·
              refine ⟨95620685762198653618016729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63747123841465769078677819 95620685762198653618016729)
              ·
                refine ⟨71715514321648990213512547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95620685762198653618016729 71715514321648990213512547)
                ·
                  refine ⟨107573271482473485320268821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71715514321648990213512547 107573271482473485320268821)
                  ·
                    refine ⟨5042497100740944624387601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107573271482473485320268821 5042497100740944624387601)
                    ·
                      refine ⟨3781872825555708468290701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042497100740944624387601 3781872825555708468290701)
                      ·
                        rfl

theorem cell23_7365171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6, 2].length) (baseStart_7365171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365171 prefixEnd_7365171 := by exact prefixLift 7365171
  have htrace : WordTrace (prefixWord ++ tailWord_7365171) baseStart_7365171 baseEnd_7365171 := by
    simpa [prefixWord, tailWord_7365171, baseEnd_7365171] using wordTrace_append hprefix tailTrace_7365171
  have hstable : (prefixWord ++ tailWord_7365171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365171).length < 2 ^ (prefixWord ++ tailWord_7365171).sum := by decide
  have hdescent : baseEnd_7365171 < baseStart_7365171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365172 : List Nat := [2, 5, 1, 3, 1, 1, 2, 3, 5]
def baseStart_7365172 : Nat := 118140960795 + 7365172 * 2 ^ 59
def prefixEnd_7365172 : Nat := 4983230072969 + 3 ^ 40 * 7365172 * 2
def baseEnd_7365172 : Nat := 420208148781818107153133

theorem tailTrace_7365172 : CollatzResearch.WordTrace tailWord_7365172 prefixEnd_7365172 420208148781818107153133 := by
  unfold tailWord_7365172
  simp only [CollatzResearch.WordTrace]
  refine ⟨134314945836623595039232885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179086594448831460052310513 134314945836623595039232885)
  ·
    refine ⟨12592026172183462034928083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134314945836623595039232885 12592026172183462034928083)
    ·
      refine ⟨18888039258275193052392125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12592026172183462034928083 18888039258275193052392125)
      ·
        refine ⟨7083014721853197394647047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18888039258275193052392125 7083014721853197394647047)
        ·
          refine ⟨10624522082779796091970571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083014721853197394647047 10624522082779796091970571)
          ·
            refine ⟨15936783124169694137955857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10624522082779796091970571 15936783124169694137955857)
            ·
              refine ⟨11952587343127270603466893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15936783124169694137955857 11952587343127270603466893)
              ·
                refine ⟨4482220253672726476300085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11952587343127270603466893 4482220253672726476300085)
                ·
                  refine ⟨420208148781818107153133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482220253672726476300085 420208148781818107153133)
                  ·
                    rfl

theorem cell23_7365172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_7365172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365172 prefixEnd_7365172 := by exact prefixLift 7365172
  have htrace : WordTrace (prefixWord ++ tailWord_7365172) baseStart_7365172 baseEnd_7365172 := by
    simpa [prefixWord, tailWord_7365172, baseEnd_7365172] using wordTrace_append hprefix tailTrace_7365172
  have hstable : (prefixWord ++ tailWord_7365172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365172).length < 2 ^ (prefixWord ++ tailWord_7365172).sum := by decide
  have hdescent : baseEnd_7365172 < baseStart_7365172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365184 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_7365184 : Nat := 118140960795 + 7365184 * 2 ^ 59
def prefixEnd_7365184 : Nat := 4983230072969 + 3 ^ 40 * 7365184 * 2
def baseEnd_7365184 : Nat := 3781879500804216917428141

theorem tailTrace_7365184 : CollatzResearch.WordTrace tailWord_7365184 prefixEnd_7365184 3781879500804216917428141 := by
  unfold tailWord_7365184
  simp only [CollatzResearch.WordTrace]
  refine ⟨134315164674601858063951303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179086886232802477418601737 134315164674601858063951303)
  ·
    refine ⟨201472747011902787095926955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134315164674601858063951303 201472747011902787095926955)
    ·
      refine ⟨302209120517854180643890433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201472747011902787095926955 302209120517854180643890433)
      ·
        refine ⟨226656840388390635482917825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302209120517854180643890433 226656840388390635482917825)
        ·
          refine ⟨169992630291292976612188369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226656840388390635482917825 169992630291292976612188369)
          ·
            refine ⟨127494472718469732459141277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169992630291292976612188369 127494472718469732459141277)
            ·
              refine ⟨47810427269426149672177979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127494472718469732459141277 47810427269426149672177979)
              ·
                refine ⟨71715640904139224508266969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47810427269426149672177979 71715640904139224508266969)
                ·
                  refine ⟨53786730678104418381200227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71715640904139224508266969 53786730678104418381200227)
                  ·
                    refine ⟨80680096017156627571800341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53786730678104418381200227 80680096017156627571800341)
                    ·
                      refine ⟨3781879500804216917428141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80680096017156627571800341 3781879500804216917428141)
                      ·
                        rfl

theorem cell23_7365184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_7365184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365184 prefixEnd_7365184 := by exact prefixLift 7365184
  have htrace : WordTrace (prefixWord ++ tailWord_7365184) baseStart_7365184 baseEnd_7365184 := by
    simpa [prefixWord, tailWord_7365184, baseEnd_7365184] using wordTrace_append hprefix tailTrace_7365184
  have hstable : (prefixWord ++ tailWord_7365184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365184).length < 2 ^ (prefixWord ++ tailWord_7365184).sum := by decide
  have hdescent : baseEnd_7365184 < baseStart_7365184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365232 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 1, 4]
def baseStart_7365232 : Nat := 118140960795 + 7365232 * 2 ^ 59
def prefixEnd_7365232 : Nat := 4983230072969 + 3 ^ 40 * 7365232 * 2
def baseEnd_7365232 : Nat := 1260634715958544243209307

theorem tailTrace_7365232 : CollatzResearch.WordTrace tailWord_7365232 prefixEnd_7365232 1260634715958544243209307 := by
  unfold tailWord_7365232
  simp only [CollatzResearch.WordTrace]
  refine ⟨134316040026514910162824975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179088053368686546883766633 134316040026514910162824975)
  ·
    refine ⟨201474060039772365244237463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134316040026514910162824975 201474060039772365244237463)
    ·
      refine ⟨302211090059658547866356195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201474060039772365244237463 302211090059658547866356195)
      ·
        refine ⟨453316635089487821799534293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302211090059658547866356195 453316635089487821799534293)
        ·
          refine ⟨10624608634909870823426585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 453316635089487821799534293 10624608634909870823426585)
          ·
            refine ⟨7968456476182403117569939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10624608634909870823426585 7968456476182403117569939)
            ·
              refine ⟨11952684714273604676354909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968456476182403117569939 11952684714273604676354909)
              ·
                refine ⟨4482256767852601753633091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11952684714273604676354909 4482256767852601753633091)
                ·
                  refine ⟨6723385151778902630449637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482256767852601753633091 6723385151778902630449637)
                  ·
                    refine ⟨1260634715958544243209307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6723385151778902630449637 1260634715958544243209307)
                    ·
                      rfl

theorem cell23_7365232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_7365232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365232 prefixEnd_7365232 := by exact prefixLift 7365232
  have htrace : WordTrace (prefixWord ++ tailWord_7365232) baseStart_7365232 baseEnd_7365232 := by
    simpa [prefixWord, tailWord_7365232, baseEnd_7365232] using wordTrace_append hprefix tailTrace_7365232
  have hstable : (prefixWord ++ tailWord_7365232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365232).length < 2 ^ (prefixWord ++ tailWord_7365232).sum := by decide
  have hdescent : baseEnd_7365232 < baseStart_7365232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365248 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2]
def baseStart_7365248 : Nat := 118140960795 + 7365248 * 2 ^ 59
def prefixEnd_7365248 : Nat := 4983230072969 + 3 ^ 40 * 7365248 * 2
def baseEnd_7365248 : Nat := 3781912363566104667027847

theorem tailTrace_7365248 : CollatzResearch.WordTrace tailWord_7365248 prefixEnd_7365248 3781912363566104667027847 := by
  unfold tailWord_7365248
  simp only [CollatzResearch.WordTrace]
  refine ⟨134316331810485927529116199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179088442413981236705488265 134316331810485927529116199)
  ·
    refine ⟨201474497715728891293674299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134316331810485927529116199 201474497715728891293674299)
    ·
      refine ⟨302211746573593336940511449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201474497715728891293674299 302211746573593336940511449)
      ·
        refine ⟨226658809930195002705383587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302211746573593336940511449 226658809930195002705383587)
        ·
          refine ⟨339988214895292504058075381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226658809930195002705383587 339988214895292504058075381)
          ·
            refine ⟨31873895146433672255444567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339988214895292504058075381 31873895146433672255444567)
            ·
              refine ⟨47810842719650508383166851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31873895146433672255444567 47810842719650508383166851)
              ·
                refine ⟨71716264079475762574750277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47810842719650508383166851 71716264079475762574750277)
                ·
                  refine ⟨13446799514901705482765677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71716264079475762574750277 13446799514901705482765677)
                  ·
                    refine ⟨5042549818088139556037129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13446799514901705482765677 5042549818088139556037129)
                    ·
                      refine ⟨3781912363566104667027847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042549818088139556037129 3781912363566104667027847)
                      ·
                        rfl

theorem cell23_7365248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_7365248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365248 prefixEnd_7365248 := by exact prefixLift 7365248
  have htrace : WordTrace (prefixWord ++ tailWord_7365248) baseStart_7365248 baseEnd_7365248 := by
    simpa [prefixWord, tailWord_7365248, baseEnd_7365248] using wordTrace_append hprefix tailTrace_7365248
  have hstable : (prefixWord ++ tailWord_7365248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365248).length < 2 ^ (prefixWord ++ tailWord_7365248).sum := by decide
  have hdescent : baseEnd_7365248 < baseStart_7365248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365271 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 6]
def baseStart_7365271 : Nat := 118140960795 + 7365271 * 2 ^ 59
def prefixEnd_7365271 : Nat := 4983230072969 + 3 ^ 40 * 7365271 * 2
def baseEnd_7365271 : Nat := 1260641391207052692346747

theorem tailTrace_7365271 : CollatzResearch.WordTrace tailWord_7365271 prefixEnd_7365271 1260641391207052692346747 := by
  unfold tailWord_7365271
  simp only [CollatzResearch.WordTrace]
  refine ⟨268633502499888529986319667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179089001666592353324213111 268633502499888529986319667)
  ·
    refine ⟨402950253749832794979479501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268633502499888529986319667 402950253749832794979479501)
    ·
      refine ⟨151106345156187298117304813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402950253749832794979479501 151106345156187298117304813)
      ·
        refine ⟨56664879433570236793989305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151106345156187298117304813 56664879433570236793989305)
        ·
          refine ⟨42498659575177677595491979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56664879433570236793989305 42498659575177677595491979)
          ·
            refine ⟨63747989362766516393237969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42498659575177677595491979 63747989362766516393237969)
            ·
              refine ⟨47810992022074887294928477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63747989362766516393237969 47810992022074887294928477)
              ·
                refine ⟨17929122008278082735598179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47810992022074887294928477 17929122008278082735598179)
                ·
                  refine ⟨26893683012417124103397269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17929122008278082735598179 26893683012417124103397269)
                  ·
                    refine ⟨1260641391207052692346747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26893683012417124103397269 1260641391207052692346747)
                    ·
                      rfl

theorem cell23_7365271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_7365271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365271 prefixEnd_7365271 := by exact prefixLift 7365271
  have htrace : WordTrace (prefixWord ++ tailWord_7365271) baseStart_7365271 baseEnd_7365271 := by
    simpa [prefixWord, tailWord_7365271, baseEnd_7365271] using wordTrace_append hprefix tailTrace_7365271
  have hstable : (prefixWord ++ tailWord_7365271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365271).length < 2 ^ (prefixWord ++ tailWord_7365271).sum := by decide
  have hdescent : baseEnd_7365271 < baseStart_7365271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365295 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 1, 1, 4]
def baseStart_7365295 : Nat := 118140960795 + 7365295 * 2 ^ 59
def prefixEnd_7365295 : Nat := 4983230072969 + 3 ^ 40 * 7365295 * 2
def baseEnd_7365295 : Nat := 3781936497156865983140131

theorem tailTrace_7365295 : CollatzResearch.WordTrace tailWord_7365295 prefixEnd_7365295 3781936497156865983140131 := by
  unfold tailWord_7365295
  simp only [CollatzResearch.WordTrace]
  refine ⟨268634377851801582085193339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179089585234534388056795559 268634377851801582085193339)
  ·
    refine ⟨402951566777702373127790009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268634377851801582085193339 402951566777702373127790009)
    ·
      refine ⟨302213675083276779845842507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402951566777702373127790009 302213675083276779845842507)
      ·
        refine ⟨453320512624915169768763761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302213675083276779845842507 453320512624915169768763761)
        ·
          refine ⟨339990384468686377326572821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453320512624915169768763761 339990384468686377326572821)
          ·
            refine ⟨15937049271969673937183101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339990384468686377326572821 15937049271969673937183101)
            ·
              refine ⟨5976393476988627726443663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15937049271969673937183101 5976393476988627726443663)
              ·
                refine ⟨8964590215482941589665495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976393476988627726443663 8964590215482941589665495)
                ·
                  refine ⟨13446885323224412384498243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8964590215482941589665495 13446885323224412384498243)
                  ·
                    refine ⟨20170327984836618576747365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13446885323224412384498243 20170327984836618576747365)
                    ·
                      refine ⟨3781936497156865983140131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20170327984836618576747365 3781936497156865983140131)
                      ·
                        rfl

theorem cell23_7365295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 1, 4].length) (baseStart_7365295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365295 prefixEnd_7365295 := by exact prefixLift 7365295
  have htrace : WordTrace (prefixWord ++ tailWord_7365295) baseStart_7365295 baseEnd_7365295 := by
    simpa [prefixWord, tailWord_7365295, baseEnd_7365295] using wordTrace_append hprefix tailTrace_7365295
  have hstable : (prefixWord ++ tailWord_7365295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365295).length < 2 ^ (prefixWord ++ tailWord_7365295).sum := by decide
  have hdescent : baseEnd_7365295 < baseStart_7365295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365301 : List Nat := [1, 3, 3, 3, 1, 12]
def baseStart_7365301 : Nat := 118140960795 + 7365301 * 2 ^ 59
def prefixEnd_7365301 : Nat := 4983230072969 + 3 ^ 40 * 7365301 * 2
def baseEnd_7365301 : Nat := 15563537358192563620021

theorem tailTrace_7365301 : CollatzResearch.WordTrace tailWord_7365301 prefixEnd_7365301 15563537358192563620021 := by
  unfold tailWord_7365301
  simp only [CollatzResearch.WordTrace]
  refine ⟨268634596689779845109911757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179089731126519896739941171 268634596689779845109911757)
  ·
    refine ⟨100737973758667441916216909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268634596689779845109911757 100737973758667441916216909)
    ·
      refine ⟨37776740159500290718581341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100737973758667441916216909 37776740159500290718581341)
      ·
        refine ⟨14166277559812609019468003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37776740159500290718581341 14166277559812609019468003)
        ·
          refine ⟨21249416339718913529202005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166277559812609019468003 21249416339718913529202005)
          ·
            refine ⟨15563537358192563620021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21249416339718913529202005 15563537358192563620021)
            ·
              rfl

theorem cell23_7365301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 12].length) (baseStart_7365301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365301 prefixEnd_7365301 := by exact prefixLift 7365301
  have htrace : WordTrace (prefixWord ++ tailWord_7365301) baseStart_7365301 baseEnd_7365301 := by
    simpa [prefixWord, tailWord_7365301, baseEnd_7365301] using wordTrace_append hprefix tailTrace_7365301
  have hstable : (prefixWord ++ tailWord_7365301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365301).length < 2 ^ (prefixWord ++ tailWord_7365301).sum := by decide
  have hdescent : baseEnd_7365301 < baseStart_7365301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365361 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_7365361 : Nat := 118140960795 + 7365361 * 2 ^ 59
def prefixEnd_7365361 : Nat := 4983230072969 + 3 ^ 40 * 7365361 * 2
def baseEnd_7365361 : Nat := 1260656795626687574971609

theorem tailTrace_7365361 : CollatzResearch.WordTrace tailWord_7365361 prefixEnd_7365361 1260656795626687574971609 := by
  unfold tailWord_7365361
  simp only [CollatzResearch.WordTrace]
  refine ⟨268636785069562475357095937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179091190046374983571397291 268636785069562475357095937)
  ·
    refine ⟨201477588802171856517821953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268636785069562475357095937 201477588802171856517821953)
    ·
      refine ⟨151108191601628892388366465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201477588802171856517821953 151108191601628892388366465)
      ·
        refine ⟨113331143701221669291274849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151108191601628892388366465 113331143701221669291274849)
        ·
          refine ⟨84998357775916251968456137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113331143701221669291274849 84998357775916251968456137)
          ·
            refine ⟨63748768331937188976342103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84998357775916251968456137 63748768331937188976342103)
            ·
              refine ⟨95623152497905783464513155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63748768331937188976342103 95623152497905783464513155)
              ·
                refine ⟨143434728746858675196769733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95623152497905783464513155 143434728746858675196769733)
                ·
                  refine ⟨26894011640036001599394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143434728746858675196769733 26894011640036001599394325)
                  ·
                    refine ⟨1260656795626687574971609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26894011640036001599394325 1260656795626687574971609)
                    ·
                      rfl

theorem cell23_7365361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_7365361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365361 prefixEnd_7365361 := by exact prefixLift 7365361
  have htrace : WordTrace (prefixWord ++ tailWord_7365361) baseStart_7365361 baseEnd_7365361 := by
    simpa [prefixWord, tailWord_7365361, baseEnd_7365361] using wordTrace_append hprefix tailTrace_7365361
  have hstable : (prefixWord ++ tailWord_7365361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365361).length < 2 ^ (prefixWord ++ tailWord_7365361).sum := by decide
  have hdescent : baseEnd_7365361 < baseStart_7365361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365362 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_7365362 : Nat := 118140960795 + 7365362 * 2 ^ 59
def prefixEnd_7365362 : Nat := 4983230072969 + 3 ^ 40 * 7365362 * 2
def baseEnd_7365362 : Nat := 3781970900360717221002323

theorem tailTrace_7365362 : CollatzResearch.WordTrace tailWord_7365362 prefixEnd_7365362 3781970900360717221002323 := by
  unfold tailWord_7365362
  simp only [CollatzResearch.WordTrace]
  refine ⟨67159205385639713131970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179091214361705901685254893 67159205385639713131970585)
  ·
    refine ⟨50369404039229784848977939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67159205385639713131970585 50369404039229784848977939)
    ·
      refine ⟨75554106058844677273466909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50369404039229784848977939 75554106058844677273466909)
      ·
        refine ⟨28332789772066753977550091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75554106058844677273466909 28332789772066753977550091)
        ·
          refine ⟨42499184658100130966325137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28332789772066753977550091 42499184658100130966325137)
          ·
            refine ⟨31874388493575098224743853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42499184658100130966325137 31874388493575098224743853)
            ·
              refine ⟨11952895685090661834278945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31874388493575098224743853 11952895685090661834278945)
              ·
                refine ⟨8964671763817996375709209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952895685090661834278945 8964671763817996375709209)
                ·
                  refine ⟨6723503822863497281781907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8964671763817996375709209 6723503822863497281781907)
                  ·
                    refine ⟨10085255734295245922672861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723503822863497281781907 10085255734295245922672861)
                    ·
                      refine ⟨3781970900360717221002323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10085255734295245922672861 3781970900360717221002323)
                      ·
                        rfl

theorem cell23_7365362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_7365362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365362 prefixEnd_7365362 := by exact prefixLift 7365362
  have htrace : WordTrace (prefixWord ++ tailWord_7365362) baseStart_7365362 baseEnd_7365362 := by
    simpa [prefixWord, tailWord_7365362, baseEnd_7365362] using wordTrace_append hprefix tailTrace_7365362
  have hstable : (prefixWord ++ tailWord_7365362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365362).length < 2 ^ (prefixWord ++ tailWord_7365362).sum := by decide
  have hdescent : baseEnd_7365362 < baseStart_7365362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365385 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 4, 2]
def baseStart_7365385 : Nat := 118140960795 + 7365385 * 2 ^ 59
def prefixEnd_7365385 : Nat := 4983230072969 + 3 ^ 40 * 7365385 * 2
def baseEnd_7365385 : Nat := 3781982710415770631014717

theorem tailTrace_7365385 : CollatzResearch.WordTrace tailWord_7365385 prefixEnd_7365385 3781982710415770631014717 := by
  unfold tailWord_7365385
  simp only [CollatzResearch.WordTrace]
  refine ⟨268637660421475527455969609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179091773614317018303979739 268637660421475527455969609)
  ·
    refine ⟨201478245316106645591977207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268637660421475527455969609 201478245316106645591977207)
    ·
      refine ⟨302217367974159968387965811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201478245316106645591977207 302217367974159968387965811)
      ·
        refine ⟨453326051961239952581948717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302217367974159968387965811 453326051961239952581948717)
        ·
          refine ⟨169997269485464982218230769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453326051961239952581948717 169997269485464982218230769)
          ·
            refine ⟨127497952114098736663673077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169997269485464982218230769 127497952114098736663673077)
            ·
              refine ⟨11952933010696756562219351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127497952114098736663673077 11952933010696756562219351)
              ·
                refine ⟨17929399516045134843329027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11952933010696756562219351 17929399516045134843329027)
                ·
                  refine ⟨26894099274067702264993541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17929399516045134843329027 26894099274067702264993541)
                  ·
                    refine ⟨5042643613887694174686289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26894099274067702264993541 5042643613887694174686289)
                    ·
                      refine ⟨3781982710415770631014717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042643613887694174686289 3781982710415770631014717)
                      ·
                        rfl

theorem cell23_7365385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4, 2].length) (baseStart_7365385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365385 prefixEnd_7365385 := by exact prefixLift 7365385
  have htrace : WordTrace (prefixWord ++ tailWord_7365385) baseStart_7365385 baseEnd_7365385 := by
    simpa [prefixWord, tailWord_7365385, baseEnd_7365385] using wordTrace_append hprefix tailTrace_7365385
  have hstable : (prefixWord ++ tailWord_7365385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365385).length < 2 ^ (prefixWord ++ tailWord_7365385).sum := by decide
  have hdescent : baseEnd_7365385 < baseStart_7365385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365391 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 7]
def baseStart_7365391 : Nat := 118140960795 + 7365391 * 2 ^ 59
def prefixEnd_7365391 : Nat := 4983230072969 + 3 ^ 40 * 7365391 * 2
def baseEnd_7365391 : Nat := 420220643477744178615521

theorem tailTrace_7365391 : CollatzResearch.WordTrace tailWord_7365391 prefixEnd_7365391 420220643477744178615521 := by
  unfold tailWord_7365391
  simp only [CollatzResearch.WordTrace]
  refine ⟨268637879259453790480688027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179091919506302526987125351 268637879259453790480688027)
  ·
    refine ⟨402956818889180685721032041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268637879259453790480688027 402956818889180685721032041)
    ·
      refine ⟨302217614166885514290774031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402956818889180685721032041 302217614166885514290774031)
      ·
        refine ⟨453326421250328271436161047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302217614166885514290774031 453326421250328271436161047)
        ·
          refine ⟨679989631875492407154241571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453326421250328271436161047 679989631875492407154241571)
          ·
            refine ⟨1019984447813238610731362357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679989631875492407154241571 1019984447813238610731362357)
            ·
              refine ⟨95623541982491119756065221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1019984447813238610731362357 95623541982491119756065221)
              ·
                refine ⟨17929414121717084954262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95623541982491119756065221 17929414121717084954262229)
                ·
                  refine ⟨420220643477744178615521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17929414121717084954262229 420220643477744178615521)
                  ·
                    rfl

theorem cell23_7365391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 7].length) (baseStart_7365391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365391 prefixEnd_7365391 := by exact prefixLift 7365391
  have htrace : WordTrace (prefixWord ++ tailWord_7365391) baseStart_7365391 baseEnd_7365391 := by
    simpa [prefixWord, tailWord_7365391, baseEnd_7365391] using wordTrace_append hprefix tailTrace_7365391
  have hstable : (prefixWord ++ tailWord_7365391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365391).length < 2 ^ (prefixWord ++ tailWord_7365391).sum := by decide
  have hdescent : baseEnd_7365391 < baseStart_7365391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365475 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7365475 : Nat := 118140960795 + 7365475 * 2 ^ 59
def prefixEnd_7365475 : Nat := 4983230072969 + 3 ^ 40 * 7365475 * 2
def baseEnd_7365475 : Nat := 3782028923674675278889303

theorem tailTrace_7365475 : CollatzResearch.WordTrace tailWord_7365475 prefixEnd_7365475 3782028923674675278889303 := by
  unfold tailWord_7365475
  simp only [CollatzResearch.WordTrace]
  refine ⟨268640942991149472826745879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179093961994099648551163919 268640942991149472826745879)
  ·
    refine ⟨402961414486724209240118819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268640942991149472826745879 402961414486724209240118819)
    ·
      refine ⟨604442121730086313860178229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402961414486724209240118819 604442121730086313860178229)
      ·
        refine ⟨56666448912195591924391709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 604442121730086313860178229 56666448912195591924391709)
        ·
          refine ⟨21249918342073346971646891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56666448912195591924391709 21249918342073346971646891)
          ·
            refine ⟨31874877513110020457470337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21249918342073346971646891 31874877513110020457470337)
            ·
              refine ⟨23906158134832515343102753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31874877513110020457470337 23906158134832515343102753)
              ·
                refine ⟨17929618601124386507327065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23906158134832515343102753 17929618601124386507327065)
                ·
                  refine ⟨13447213950843289880495299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17929618601124386507327065 13447213950843289880495299)
                  ·
                    refine ⟨20170820926264934820742949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13447213950843289880495299 20170820926264934820742949)
                    ·
                      refine ⟨3782028923674675278889303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20170820926264934820742949 3782028923674675278889303)
                      ·
                        rfl

theorem cell23_7365475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7365475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365475 prefixEnd_7365475 := by exact prefixLift 7365475
  have htrace : WordTrace (prefixWord ++ tailWord_7365475) baseStart_7365475 baseEnd_7365475 := by
    simpa [prefixWord, tailWord_7365475, baseEnd_7365475] using wordTrace_append hprefix tailTrace_7365475
  have hstable : (prefixWord ++ tailWord_7365475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365475).length < 2 ^ (prefixWord ++ tailWord_7365475).sum := by decide
  have hdescent : baseEnd_7365475 < baseStart_7365475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365485 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_7365485 : Nat := 118140960795 + 7365485 * 2 ^ 59
def prefixEnd_7365485 : Nat := 4983230072969 + 3 ^ 40 * 7365485 * 2
def baseEnd_7365485 : Nat := 1260678019493740079921419

theorem tailTrace_7365485 : CollatzResearch.WordTrace tailWord_7365485 prefixEnd_7365485 1260678019493740079921419 := by
  unfold tailWord_7365485
  simp only [CollatzResearch.WordTrace]
  refine ⟨268641307721113244534609909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179094205147408829689739939 268641307721113244534609909)
  ·
    refine ⟨25185122598854366675119679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268641307721113244534609909 25185122598854366675119679)
    ·
      refine ⟨37777683898281550012679519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25185122598854366675119679 37777683898281550012679519)
      ·
        refine ⟨56666525847422325019019279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37777683898281550012679519 56666525847422325019019279)
        ·
          refine ⟨84999788771133487528528919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56666525847422325019019279 84999788771133487528528919)
          ·
            refine ⟨127499683156700231292793379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84999788771133487528528919 127499683156700231292793379)
            ·
              refine ⟨191249524735050346939190069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127499683156700231292793379 191249524735050346939190069)
              ·
                refine ⟨17929642943910970025549069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191249524735050346939190069 17929642943910970025549069)
                ·
                  refine ⟨6723616103966613759580901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17929642943910970025549069 6723616103966613759580901)
                  ·
                    refine ⟨1260678019493740079921419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6723616103966613759580901 1260678019493740079921419)
                    ·
                      rfl

theorem cell23_7365485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_7365485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365485 prefixEnd_7365485 := by exact prefixLift 7365485
  have htrace : WordTrace (prefixWord ++ tailWord_7365485) baseStart_7365485 baseEnd_7365485 := by
    simpa [prefixWord, tailWord_7365485, baseEnd_7365485] using wordTrace_append hprefix tailTrace_7365485
  have hstable : (prefixWord ++ tailWord_7365485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365485).length < 2 ^ (prefixWord ++ tailWord_7365485).sum := by decide
  have hdescent : baseEnd_7365485 < baseStart_7365485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365506 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7365506 : Nat := 118140960795 + 7365506 * 2 ^ 59
def prefixEnd_7365506 : Nat := 4983230072969 + 3 ^ 40 * 7365506 * 2
def baseEnd_7365506 : Nat := 1260681613858321552533887

theorem tailTrace_7365506 : CollatzResearch.WordTrace tailWord_7365506 prefixEnd_7365506 1260681613858321552533887 := by
  unfold tailWord_7365506
  simp only [CollatzResearch.WordTrace]
  refine ⟨67160518413509291280281093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179094715769358110080749581 67160518413509291280281093)
  ·
    refine ⟨12592597202532992115052705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67160518413509291280281093 12592597202532992115052705)
    ·
      refine ⟨9444447901899744086289529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12592597202532992115052705 9444447901899744086289529)
      ·
        refine ⟨7083335926424808064717147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9444447901899744086289529 7083335926424808064717147)
        ·
          refine ⟨10625003889637212097075721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083335926424808064717147 10625003889637212097075721)
          ·
            refine ⟨7968752917227909072806791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10625003889637212097075721 7968752917227909072806791)
            ·
              refine ⟨11953129375841863609210187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968752917227909072806791 11953129375841863609210187)
              ·
                refine ⟨17929694063762795413815281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953129375841863609210187 17929694063762795413815281)
                ·
                  refine ⟨13447270547822096560361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17929694063762795413815281 13447270547822096560361461)
                  ·
                    refine ⟨1260681613858321552533887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13447270547822096560361461 1260681613858321552533887)
                    ·
                      rfl

theorem cell23_7365506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7365506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365506 prefixEnd_7365506 := by exact prefixLift 7365506
  have htrace : WordTrace (prefixWord ++ tailWord_7365506) baseStart_7365506 baseEnd_7365506 := by
    simpa [prefixWord, tailWord_7365506, baseEnd_7365506] using wordTrace_append hprefix tailTrace_7365506
  have hstable : (prefixWord ++ tailWord_7365506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365506).length < 2 ^ (prefixWord ++ tailWord_7365506).sum := by decide
  have hdescent : baseEnd_7365506 < baseStart_7365506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365512 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_7365512 : Nat := 118140960795 + 7365512 * 2 ^ 59
def prefixEnd_7365512 : Nat := 4983230072969 + 3 ^ 40 * 7365512 * 2
def baseEnd_7365512 : Nat := 3782047922458891634126633

theorem tailTrace_7365512 : CollatzResearch.WordTrace tailWord_7365512 prefixEnd_7365512 3782047922458891634126633 := by
  unfold tailWord_7365512
  simp only [CollatzResearch.WordTrace]
  refine ⟨134321146246007714072921395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179094861661343618763895193 134321146246007714072921395)
  ·
    refine ⟨201481719369011571109382093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134321146246007714072921395 201481719369011571109382093)
    ·
      refine ⟨75555644763379339166018285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201481719369011571109382093 75555644763379339166018285)
      ·
        refine ⟨28333366786267252187256857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75555644763379339166018285 28333366786267252187256857)
        ·
          refine ⟨21250025089700439140442643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28333366786267252187256857 21250025089700439140442643)
          ·
            refine ⟨31875037634550658710663965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250025089700439140442643 31875037634550658710663965)
            ·
              refine ⟨11953139112956497016498987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31875037634550658710663965 11953139112956497016498987)
              ·
                refine ⟨17929708669434745524748481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953139112956497016498987 17929708669434745524748481)
                ·
                  refine ⟨13447281502076059143561361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17929708669434745524748481 13447281502076059143561361)
                  ·
                    refine ⟨10085461126557044357671021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13447281502076059143561361 10085461126557044357671021)
                    ·
                      refine ⟨3782047922458891634126633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10085461126557044357671021 3782047922458891634126633)
                      ·
                        rfl

theorem cell23_7365512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_7365512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365512 prefixEnd_7365512 := by exact prefixLift 7365512
  have htrace : WordTrace (prefixWord ++ tailWord_7365512) baseStart_7365512 baseEnd_7365512 := by
    simpa [prefixWord, tailWord_7365512, baseEnd_7365512] using wordTrace_append hprefix tailTrace_7365512
  have hstable : (prefixWord ++ tailWord_7365512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365512).length < 2 ^ (prefixWord ++ tailWord_7365512).sum := by decide
  have hdescent : baseEnd_7365512 < baseStart_7365512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365526 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7365526 : Nat := 118140960795 + 7365526 * 2 ^ 59
def prefixEnd_7365526 : Nat := 4983230072969 + 3 ^ 40 * 7365526 * 2
def baseEnd_7365526 : Nat := 3782055111188054579351569

theorem tailTrace_7365526 : CollatzResearch.WordTrace tailWord_7365526 prefixEnd_7365526 3782055111188054579351569 := by
  unfold tailWord_7365526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16790175194622794283553277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179095202075976472357901621 16790175194622794283553277)
  ·
    refine ⟨6296315697983547856332479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16790175194622794283553277 6296315697983547856332479)
    ·
      refine ⟨9444473546975321784498719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296315697983547856332479 9444473546975321784498719)
      ·
        refine ⟨14166710320462982676748079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444473546975321784498719 14166710320462982676748079)
        ·
          refine ⟨21250065480694474015122119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14166710320462982676748079 21250065480694474015122119)
          ·
            refine ⟨31875098221041711022683179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250065480694474015122119 31875098221041711022683179)
            ·
              refine ⟨47812647331562566534024769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31875098221041711022683179 47812647331562566534024769)
              ·
                refine ⟨35859485498671924900518577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47812647331562566534024769 35859485498671924900518577)
                ·
                  refine ⟨26894614124003943675388933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35859485498671924900518577 26894614124003943675388933)
                  ·
                    refine ⟨5042740148250739439135425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26894614124003943675388933 5042740148250739439135425)
                    ·
                      refine ⟨3782055111188054579351569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042740148250739439135425 3782055111188054579351569)
                      ·
                        rfl

theorem cell23_7365526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7365526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365526 prefixEnd_7365526 := by exact prefixLift 7365526
  have htrace : WordTrace (prefixWord ++ tailWord_7365526) baseStart_7365526 baseEnd_7365526 := by
    simpa [prefixWord, tailWord_7365526, baseEnd_7365526] using wordTrace_append hprefix tailTrace_7365526
  have hstable : (prefixWord ++ tailWord_7365526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365526).length < 2 ^ (prefixWord ++ tailWord_7365526).sum := by decide
  have hdescent : baseEnd_7365526 < baseStart_7365526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365575 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 4, 4]
def baseStart_7365575 : Nat := 118140960795 + 7365575 * 2 ^ 59
def prefixEnd_7365575 : Nat := 4983230072969 + 3 ^ 40 * 7365575 * 2
def baseEnd_7365575 : Nat := 1260693423913374962546281

theorem tailTrace_7365575 : CollatzResearch.WordTrace tailWord_7365575 prefixEnd_7365575 1260693423913374962546281 := by
  unfold tailWord_7365575
  simp only [CollatzResearch.WordTrace]
  refine ⟨268644590290787189905386179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179096393527191459936924119 268644590290787189905386179)
  ·
    refine ⟨402966885436180784858079269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268644590290787189905386179 402966885436180784858079269)
    ·
      refine ⟨75556291019283897160889863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402966885436180784858079269 75556291019283897160889863)
      ·
        refine ⟨113334436528925845741334795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75556291019283897160889863 113334436528925845741334795)
        ·
          refine ⟨170001654793388768612002193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113334436528925845741334795 170001654793388768612002193)
          ·
            refine ⟨127501241095041576459001645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170001654793388768612002193 127501241095041576459001645)
            ·
              refine ⟨47812965410640591172125617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127501241095041576459001645 47812965410640591172125617)
              ·
                refine ⟨35859724057980443379094213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47812965410640591172125617 35859724057980443379094213)
                ·
                  refine ⟨6723698260871333133580165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35859724057980443379094213 6723698260871333133580165)
                  ·
                    refine ⟨1260693423913374962546281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6723698260871333133580165 1260693423913374962546281)
                    ·
                      rfl

theorem cell23_7365575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_7365575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365575 prefixEnd_7365575 := by exact prefixLift 7365575
  have htrace : WordTrace (prefixWord ++ tailWord_7365575) baseStart_7365575 baseEnd_7365575 := by
    simpa [prefixWord, tailWord_7365575, baseEnd_7365575] using wordTrace_append hprefix tailTrace_7365575
  have hstable : (prefixWord ++ tailWord_7365575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365575).length < 2 ^ (prefixWord ++ tailWord_7365575).sum := by decide
  have hdescent : baseEnd_7365575 < baseStart_7365575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365582 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_7365582 : Nat := 118140960795 + 7365582 * 2 ^ 59
def prefixEnd_7365582 : Nat := 4983230072969 + 3 ^ 40 * 7365582 * 2
def baseEnd_7365582 : Nat := 3782083866104706360251311

theorem tailTrace_7365582 : CollatzResearch.WordTrace tailWord_7365582 prefixEnd_7365582 3782083866104706360251311 := by
  unfold tailWord_7365582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580605700220228762611375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179096563734507886733927333 33580605700220228762611375)
  ·
    refine ⟨50370908550330343143917063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33580605700220228762611375 50370908550330343143917063)
    ·
      refine ⟨75556362825495514715875595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50370908550330343143917063 75556362825495514715875595)
      ·
        refine ⟨113334544238243272073813393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75556362825495514715875595 113334544238243272073813393)
        ·
          refine ⟨85000908178682454055360045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113334544238243272073813393 85000908178682454055360045)
          ·
            refine ⟨31875340567005920270760017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85000908178682454055360045 31875340567005920270760017)
            ·
              refine ⟨23906505425254440203070013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31875340567005920270760017 23906505425254440203070013)
              ·
                refine ⟨8964939534470415076151255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23906505425254440203070013 8964939534470415076151255)
                ·
                  refine ⟨13447409301705622614226883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8964939534470415076151255 13447409301705622614226883)
                  ·
                    refine ⟨20171113952558433921340325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13447409301705622614226883 20171113952558433921340325)
                    ·
                      refine ⟨3782083866104706360251311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20171113952558433921340325 3782083866104706360251311)
                      ·
                        rfl

theorem cell23_7365582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_7365582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365582 prefixEnd_7365582 := by exact prefixLift 7365582
  have htrace : WordTrace (prefixWord ++ tailWord_7365582) baseStart_7365582 baseEnd_7365582 := by
    simpa [prefixWord, tailWord_7365582, baseEnd_7365582] using wordTrace_append hprefix tailTrace_7365582
  have hstable : (prefixWord ++ tailWord_7365582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365582).length < 2 ^ (prefixWord ++ tailWord_7365582).sum := by decide
  have hdescent : baseEnd_7365582 < baseStart_7365582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365585 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_7365585 : Nat := 118140960795 + 7365585 * 2 ^ 59
def prefixEnd_7365585 : Nat := 4983230072969 + 3 ^ 40 * 7365585 * 2
def baseEnd_7365585 : Nat := 3782085406546669848513797

theorem tailTrace_7365585 : CollatzResearch.WordTrace tailWord_7365585 prefixEnd_7365585 3782085406546669848513797 := by
  unfold tailWord_7365585
  simp only [CollatzResearch.WordTrace]
  refine ⟨268644955020750961613250209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179096636680500641075500139 268644955020750961613250209)
  ·
    refine ⟨201483716265563221209937657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268644955020750961613250209 201483716265563221209937657)
    ·
      refine ⟨151112787199172415907453243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201483716265563221209937657 151112787199172415907453243)
      ·
        refine ⟨226669180798758623861179865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151112787199172415907453243 226669180798758623861179865)
        ·
          refine ⟨170001885599068967895884899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226669180798758623861179865 170001885599068967895884899)
          ·
            refine ⟨255002828398603451843827349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170001885599068967895884899 255002828398603451843827349)
            ·
              refine ⟨11953257581184536805179407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255002828398603451843827349 11953257581184536805179407)
              ·
                refine ⟨17929886371776805207769111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953257581184536805179407 17929886371776805207769111)
                ·
                  refine ⟨26894829557665207811653667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17929886371776805207769111 26894829557665207811653667)
                  ·
                    refine ⟨40342244336497811717480501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26894829557665207811653667 40342244336497811717480501)
                    ·
                      refine ⟨3782085406546669848513797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40342244336497811717480501 3782085406546669848513797)
                      ·
                        rfl

theorem cell23_7365585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_7365585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365585 prefixEnd_7365585 := by exact prefixLift 7365585
  have htrace : WordTrace (prefixWord ++ tailWord_7365585) baseStart_7365585 baseEnd_7365585 := by
    simpa [prefixWord, tailWord_7365585, baseEnd_7365585] using wordTrace_append hprefix tailTrace_7365585
  have hstable : (prefixWord ++ tailWord_7365585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365585).length < 2 ^ (prefixWord ++ tailWord_7365585).sum := by decide
  have hdescent : baseEnd_7365585 < baseStart_7365585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365665 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_7365665 : Nat := 118140960795 + 7365665 * 2 ^ 59
def prefixEnd_7365665 : Nat := 4983230072969 + 3 ^ 40 * 7365665 * 2
def baseEnd_7365665 : Nat := 1260708828333009845171143

theorem tailTrace_7365665 : CollatzResearch.WordTrace tailWord_7365665 prefixEnd_7365665 1260708828333009845171143 := by
  unfold tailWord_7365665
  simp only [CollatzResearch.WordTrace]
  refine ⟨268647872860461135276162449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179098581906974090184108299 268647872860461135276162449)
  ·
    refine ⟨201485904645345851457121837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268647872860461135276162449 201485904645345851457121837)
    ·
      refine ⟨75557214242004694296420689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201485904645345851457121837 75557214242004694296420689)
      ·
        refine ⟨56667910681503520722315517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75557214242004694296420689 56667910681503520722315517)
        ·
          refine ⟨21250466505563820270868319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56667910681503520722315517 21250466505563820270868319)
          ·
            refine ⟨31875699758345730406302479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250466505563820270868319 31875699758345730406302479)
            ·
              refine ⟨47813549637518595609453719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31875699758345730406302479 47813549637518595609453719)
              ·
                refine ⟨71720324456277893414180579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47813549637518595609453719 71720324456277893414180579)
                ·
                  refine ⟨107580486684416840121270869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71720324456277893414180579 107580486684416840121270869)
                  ·
                    refine ⟨1260708828333009845171143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107580486684416840121270869 1260708828333009845171143)
                    ·
                      rfl

theorem cell23_7365665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_7365665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365665 prefixEnd_7365665 := by exact prefixLift 7365665
  have htrace : WordTrace (prefixWord ++ tailWord_7365665) baseStart_7365665 baseEnd_7365665 := by
    simpa [prefixWord, tailWord_7365665, baseEnd_7365665] using wordTrace_append hprefix tailTrace_7365665
  have hstable : (prefixWord ++ tailWord_7365665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365665).length < 2 ^ (prefixWord ++ tailWord_7365665).sum := by decide
  have hdescent : baseEnd_7365665 < baseStart_7365665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365675 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3]
def baseStart_7365675 : Nat := 118140960795 + 7365675 * 2 ^ 59
def prefixEnd_7365675 : Nat := 4983230072969 + 3 ^ 40 * 7365675 * 2
def baseEnd_7365675 : Nat := 3782131619805574496388383

theorem tailTrace_7365675 : CollatzResearch.WordTrace tailWord_7365675 prefixEnd_7365675 3782131619805574496388383 := by
  unfold tailWord_7365675
  simp only [CollatzResearch.WordTrace]
  refine ⟨268648237590424906984026479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179098825060283271322684319 268648237590424906984026479)
  ·
    refine ⟨402972356385637360476039719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268648237590424906984026479 402972356385637360476039719)
    ·
      refine ⟨604458534578456040714059579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402972356385637360476039719 604458534578456040714059579)
      ·
        refine ⟨906687801867684061071089369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604458534578456040714059579 906687801867684061071089369)
        ·
          refine ⟨680015851400763045803317027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906687801867684061071089369 680015851400763045803317027)
          ·
            refine ⟨1020023777101144568704975541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680015851400763045803317027 1020023777101144568704975541)
            ·
              refine ⟨95627229103232303316091457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1020023777101144568704975541 95627229103232303316091457)
              ·
                refine ⟨71720421827424227487068593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95627229103232303316091457 71720421827424227487068593)
                ·
                  refine ⟨53790316370568170615301445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71720421827424227487068593 53790316370568170615301445)
                  ·
                    refine ⟨10085684319481531990369021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53790316370568170615301445 10085684319481531990369021)
                    ·
                      refine ⟨3782131619805574496388383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10085684319481531990369021 3782131619805574496388383)
                      ·
                        rfl

theorem cell23_7365675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].length) (baseStart_7365675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365675 prefixEnd_7365675 := by exact prefixLift 7365675
  have htrace : WordTrace (prefixWord ++ tailWord_7365675) baseStart_7365675 baseEnd_7365675 := by
    simpa [prefixWord, tailWord_7365675, baseEnd_7365675] using wordTrace_append hprefix tailTrace_7365675
  have hstable : (prefixWord ++ tailWord_7365675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365675).length < 2 ^ (prefixWord ++ tailWord_7365675).sum := by decide
  have hdescent : baseEnd_7365675 < baseStart_7365675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365685 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7365685 : Nat := 118140960795 + 7365685 * 2 ^ 59
def prefixEnd_7365685 : Nat := 4983230072969 + 3 ^ 40 * 7365685 * 2
def baseEnd_7365685 : Nat := 3782136754612119457263337

theorem tailTrace_7365685 : CollatzResearch.WordTrace tailWord_7365685 prefixEnd_7365685 3782136754612119457263337 := by
  unfold tailWord_7365685
  simp only [CollatzResearch.WordTrace]
  refine ⟨268648602320388678691890509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179099068213592452461260339 268648602320388678691890509)
  ·
    refine ⟨100743225870145754509458941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268648602320388678691890509 100743225870145754509458941)
    ·
      refine ⟨37778709701304657941047103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100743225870145754509458941 37778709701304657941047103)
      ·
        refine ⟨56668064551956986911570655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37778709701304657941047103 56668064551956986911570655)
        ·
          refine ⟨85002096827935480367355983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56668064551956986911570655 85002096827935480367355983)
          ·
            refine ⟨127503145241903220551033975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85002096827935480367355983 127503145241903220551033975)
            ·
              refine ⟨191254717862854830826550963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127503145241903220551033975 191254717862854830826550963)
              ·
                refine ⟨286882076794282246239826445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191254717862854830826550963 286882076794282246239826445)
                ·
                  refine ⟨107580778797855842339934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286882076794282246239826445 107580778797855842339934917)
                  ·
                    refine ⟨20171396024597970438737797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107580778797855842339934917 20171396024597970438737797)
                    ·
                      refine ⟨3782136754612119457263337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20171396024597970438737797 3782136754612119457263337)
                      ·
                        rfl

theorem cell23_7365685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7365685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365685 prefixEnd_7365685 := by exact prefixLift 7365685
  have htrace : WordTrace (prefixWord ++ tailWord_7365685) baseStart_7365685 baseEnd_7365685 := by
    simpa [prefixWord, tailWord_7365685, baseEnd_7365685] using wordTrace_append hprefix tailTrace_7365685
  have hstable : (prefixWord ++ tailWord_7365685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365685).length < 2 ^ (prefixWord ++ tailWord_7365685).sum := by decide
  have hdescent : baseEnd_7365685 < baseStart_7365685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365689 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7365689 : Nat := 118140960795 + 7365689 * 2 ^ 59
def prefixEnd_7365689 : Nat := 4983230072969 + 3 ^ 40 * 7365689 * 2
def baseEnd_7365689 : Nat := 3782138808534737441613319

theorem tailTrace_7365689 : CollatzResearch.WordTrace tailWord_7365689 prefixEnd_7365689 3782138808534737441613319 := by
  unfold tailWord_7365689
  simp only [CollatzResearch.WordTrace]
  refine ⟨268648748212374187375036121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179099165474916124916690747 268648748212374187375036121)
  ·
    refine ⟨201486561159280640531277091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268648748212374187375036121 201486561159280640531277091)
    ·
      refine ⟨302229841738920960796915637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201486561159280640531277091 302229841738920960796915637)
      ·
        refine ⟨28334047663023840074710841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302229841738920960796915637 28334047663023840074710841)
        ·
          refine ⟨21250535747267880056033131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28334047663023840074710841 21250535747267880056033131)
          ·
            refine ⟨31875803620901820084049697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250535747267880056033131 31875803620901820084049697)
            ·
              refine ⟨23906852715676365063037273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31875803620901820084049697 23906852715676365063037273)
              ·
                refine ⟨17930139536757273797277955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23906852715676365063037273 17930139536757273797277955)
                ·
                  refine ⟨26895209305135910695916933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930139536757273797277955 26895209305135910695916933)
                  ·
                    refine ⟨5042851744712983255484425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26895209305135910695916933 5042851744712983255484425)
                    ·
                      refine ⟨3782138808534737441613319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042851744712983255484425 3782138808534737441613319)
                      ·
                        rfl

theorem cell23_7365689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7365689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365689 prefixEnd_7365689 := by exact prefixLift 7365689
  have htrace : WordTrace (prefixWord ++ tailWord_7365689) baseStart_7365689 baseEnd_7365689 := by
    simpa [prefixWord, tailWord_7365689, baseEnd_7365689] using wordTrace_append hprefix tailTrace_7365689
  have hstable : (prefixWord ++ tailWord_7365689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365689).length < 2 ^ (prefixWord ++ tailWord_7365689).sum := by decide
  have hdescent : baseEnd_7365689 < baseStart_7365689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365693 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7365693 : Nat := 118140960795 + 7365693 * 2 ^ 59
def prefixEnd_7365693 : Nat := 4983230072969 + 3 ^ 40 * 7365693 * 2
def baseEnd_7365693 : Nat := 3782140862457355425963301

theorem tailTrace_7365693 : CollatzResearch.WordTrace tailWord_7365693 prefixEnd_7365693 3782140862457355425963301 := by
  unfold tailWord_7365693
  simp only [CollatzResearch.WordTrace]
  refine ⟨268648894104359696058181733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179099262736239797372121155 268648894104359696058181733)
  ·
    refine ⟨50371667644567443010909075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268648894104359696058181733 50371667644567443010909075)
    ·
      refine ⟨75557501466851164516363613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50371667644567443010909075 75557501466851164516363613)
      ·
        refine ⟨28334063050069186693636355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75557501466851164516363613 28334063050069186693636355)
        ·
          refine ⟨42501094575103780040454533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28334063050069186693636355 42501094575103780040454533)
          ·
            refine ⟨7968955232831958757585225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42501094575103780040454533 7968955232831958757585225)
            ·
              refine ⟨5976716424623969068188919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968955232831958757585225 5976716424623969068188919)
              ·
                refine ⟨8965074636935953602283379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976716424623969068188919 8965074636935953602283379)
                ·
                  refine ⟨13447611955403930403425069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965074636935953602283379 13447611955403930403425069)
                  ·
                    refine ⟨5042854483276473901284401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13447611955403930403425069 5042854483276473901284401)
                    ·
                      refine ⟨3782140862457355425963301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042854483276473901284401 3782140862457355425963301)
                      ·
                        rfl

theorem cell23_7365693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7365693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365693 prefixEnd_7365693 := by exact prefixLift 7365693
  have htrace : WordTrace (prefixWord ++ tailWord_7365693) baseStart_7365693 baseEnd_7365693 := by
    simpa [prefixWord, tailWord_7365693, baseEnd_7365693] using wordTrace_append hprefix tailTrace_7365693
  have hstable : (prefixWord ++ tailWord_7365693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365693).length < 2 ^ (prefixWord ++ tailWord_7365693).sum := by decide
  have hdescent : baseEnd_7365693 < baseStart_7365693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365706 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_7365706 : Nat := 118140960795 + 7365706 * 2 ^ 59
def prefixEnd_7365706 : Nat := 4983230072969 + 3 ^ 40 * 7365706 * 2
def baseEnd_7365706 : Nat := 3782147537705863875100741

theorem tailTrace_7365706 : CollatzResearch.WordTrace tailWord_7365706 prefixEnd_7365706 3782147537705863875100741 := by
  unfold tailWord_7365706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67162342063328149819601243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179099578835541732852269981 67162342063328149819601243)
  ·
    refine ⟨100743513094992224729401865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67162342063328149819601243 100743513094992224729401865)
    ·
      refine ⟨75557634821244168547051399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100743513094992224729401865 75557634821244168547051399)
      ·
        refine ⟨113336452231866252820577099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75557634821244168547051399 113336452231866252820577099)
        ·
          refine ⟨170004678347799379230865649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113336452231866252820577099 170004678347799379230865649)
          ·
            refine ⟨127503508760849534423149237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170004678347799379230865649 127503508760849534423149237)
            ·
              refine ⟨11953453946329643852170241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127503508760849534423149237 11953453946329643852170241)
              ·
                refine ⟨8965090459747232889127681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11953453946329643852170241 8965090459747232889127681)
                ·
                  refine ⟨6723817844810424666845761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8965090459747232889127681 6723817844810424666845761)
                  ·
                    refine ⟨5042863383607818500134321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6723817844810424666845761 5042863383607818500134321)
                    ·
                      refine ⟨3782147537705863875100741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042863383607818500134321 3782147537705863875100741)
                      ·
                        rfl

theorem cell23_7365706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_7365706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365706 prefixEnd_7365706 := by exact prefixLift 7365706
  have htrace : WordTrace (prefixWord ++ tailWord_7365706) baseStart_7365706 baseEnd_7365706 := by
    simpa [prefixWord, tailWord_7365706, baseEnd_7365706] using wordTrace_append hprefix tailTrace_7365706
  have hstable : (prefixWord ++ tailWord_7365706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365706).length < 2 ^ (prefixWord ++ tailWord_7365706).sum := by decide
  have hdescent : baseEnd_7365706 < baseStart_7365706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365742 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7365742 : Nat := 118140960795 + 7365742 * 2 ^ 59
def prefixEnd_7365742 : Nat := 4983230072969 + 3 ^ 40 * 7365742 * 2
def baseEnd_7365742 : Nat := 1260722007669808578083525

theorem tailTrace_7365742 : CollatzResearch.WordTrace tailWord_7365742 prefixEnd_7365742 1260722007669808578083525 := by
  unfold tailWord_7365742
  simp only [CollatzResearch.WordTrace]
  refine ⟨33581335160147772178339435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179100454187454784951143653 33581335160147772178339435)
  ·
    refine ⟨50372002740221658267509153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33581335160147772178339435 50372002740221658267509153)
    ·
      refine ⟨37779002055166243700631865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50372002740221658267509153 37779002055166243700631865)
      ·
        refine ⟨28334251541374682775473899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37779002055166243700631865 28334251541374682775473899)
        ·
          refine ⟨42501377312062024163210849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28334251541374682775473899 42501377312062024163210849)
          ·
            refine ⟨31876032984046518122408137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42501377312062024163210849 31876032984046518122408137)
            ·
              refine ⟨23907024738034888591806103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31876032984046518122408137 23907024738034888591806103)
              ·
                refine ⟨35860537107052332887709155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23907024738034888591806103 35860537107052332887709155)
                ·
                  refine ⟨53790805660578499331563733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35860537107052332887709155 53790805660578499331563733)
                  ·
                    refine ⟨1260722007669808578083525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53790805660578499331563733 1260722007669808578083525)
                    ·
                      rfl

theorem cell23_7365742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7365742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365742 prefixEnd_7365742 := by exact prefixLift 7365742
  have htrace : WordTrace (prefixWord ++ tailWord_7365742) baseStart_7365742 baseEnd_7365742 := by
    simpa [prefixWord, tailWord_7365742, baseEnd_7365742] using wordTrace_append hprefix tailTrace_7365742
  have hstable : (prefixWord ++ tailWord_7365742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365742).length < 2 ^ (prefixWord ++ tailWord_7365742).sum := by decide
  have hdescent : baseEnd_7365742 < baseStart_7365742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365775 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_7365775 : Nat := 118140960795 + 7365775 * 2 ^ 59
def prefixEnd_7365775 : Nat := 4983230072969 + 3 ^ 40 * 7365775 * 2
def baseEnd_7365775 : Nat := 3782182967871024105137923

theorem tailTrace_7365775 : CollatzResearch.WordTrace tailWord_7365775 prefixEnd_7365775 3782182967871024105137923 := by
  unfold tailWord_7365775
  simp only [CollatzResearch.WordTrace]
  refine ⟨268651884890062624062666779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179101256593375082708444519 268651884890062624062666779)
  ·
    refine ⟨402977827335093936094000169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268651884890062624062666779 402977827335093936094000169)
    ·
      refine ⟨302233370501320452070500127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402977827335093936094000169 302233370501320452070500127)
      ·
        refine ⟨453350055751980678105750191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302233370501320452070500127 453350055751980678105750191)
        ·
          refine ⟨680025083627971017158625287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453350055751980678105750191 680025083627971017158625287)
          ·
            refine ⟨1020037625441956525737937931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680025083627971017158625287 1020037625441956525737937931)
            ·
              refine ⟨1530056438162934788606906897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020037625441956525737937931 1530056438162934788606906897)
              ·
                refine ⟨1147542328622201091455180173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530056438162934788606906897 1147542328622201091455180173)
                ·
                  refine ⟨430328373233325409295692565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147542328622201091455180173 430328373233325409295692565)
                  ·
                    refine ⟨20171642495312128560735589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 430328373233325409295692565 20171642495312128560735589)
                    ·
                      refine ⟨3782182967871024105137923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20171642495312128560735589 3782182967871024105137923)
                      ·
                        rfl

theorem cell23_7365775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_7365775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365775 prefixEnd_7365775 := by exact prefixLift 7365775
  have htrace : WordTrace (prefixWord ++ tailWord_7365775) baseStart_7365775 baseEnd_7365775 := by
    simpa [prefixWord, tailWord_7365775, baseEnd_7365775] using wordTrace_append hprefix tailTrace_7365775
  have hstable : (prefixWord ++ tailWord_7365775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365775).length < 2 ^ (prefixWord ++ tailWord_7365775).sum := by decide
  have hdescent : baseEnd_7365775 < baseStart_7365775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365829 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 3]
def baseStart_7365829 : Nat := 118140960795 + 7365829 * 2 ^ 59
def prefixEnd_7365829 : Nat := 4983230072969 + 3 ^ 40 * 7365829 * 2
def baseEnd_7365829 : Nat := 3782210695826366893862675

theorem tailTrace_7365829 : CollatzResearch.WordTrace tailWord_7365829 prefixEnd_7365829 3782210695826366893862675 := by
  unfold tailWord_7365829
  simp only [CollatzResearch.WordTrace]
  refine ⟨268653854431866991285132541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179102569621244660856755027 268653854431866991285132541)
  ·
    refine ⟨100745195411950121731924703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268653854431866991285132541 100745195411950121731924703)
    ·
      refine ⟨151117793117925182597887055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100745195411950121731924703 151117793117925182597887055)
      ·
        refine ⟨226676689676887773896830583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151117793117925182597887055 226676689676887773896830583)
        ·
          refine ⟨340015034515331660845245875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226676689676887773896830583 340015034515331660845245875)
          ·
            refine ⟨510022551772997491267868813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340015034515331660845245875 510022551772997491267868813)
            ·
              refine ⟨191258456914874059225450805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510022551772997491267868813 191258456914874059225450805)
              ·
                refine ⟨17930480335769443052386013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191258456914874059225450805 17930480335769443052386013)
                ·
                  refine ⟨6723930125913541144644755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17930480335769443052386013 6723930125913541144644755)
                  ·
                    refine ⟨10085895188870311716967133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723930125913541144644755 10085895188870311716967133)
                    ·
                      refine ⟨3782210695826366893862675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10085895188870311716967133 3782210695826366893862675)
                      ·
                        rfl

theorem cell23_7365829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_7365829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365829 prefixEnd_7365829 := by exact prefixLift 7365829
  have htrace : WordTrace (prefixWord ++ tailWord_7365829) baseStart_7365829 baseEnd_7365829 := by
    simpa [prefixWord, tailWord_7365829, baseEnd_7365829] using wordTrace_append hprefix tailTrace_7365829
  have hstable : (prefixWord ++ tailWord_7365829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365829).length < 2 ^ (prefixWord ++ tailWord_7365829).sum := by decide
  have hdescent : baseEnd_7365829 < baseStart_7365829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365832 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_7365832 : Nat := 118140960795 + 7365832 * 2 ^ 59
def prefixEnd_7365832 : Nat := 4983230072969 + 3 ^ 40 * 7365832 * 2
def baseEnd_7365832 : Nat := 1260737412089443460708387

theorem tailTrace_7365832 : CollatzResearch.WordTrace tailWord_7365832 prefixEnd_7365832 1260737412089443460708387 := by
  unfold tailWord_7365832
  simp only [CollatzResearch.WordTrace]
  refine ⟨134326981925428061398745875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179102642567237415198327833 134326981925428061398745875)
  ·
    refine ⟨201490472888142092098118813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134326981925428061398745875 201490472888142092098118813)
    ·
      refine ⟨75558927333053284536794555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201490472888142092098118813 75558927333053284536794555)
      ·
        refine ⟨113338390999579926805191833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75558927333053284536794555 113338390999579926805191833)
        ·
          refine ⟨85003793249684945103893875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113338390999579926805191833 85003793249684945103893875)
          ·
            refine ⟨127505689874527417655840813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85003793249684945103893875 127505689874527417655840813)
            ·
              refine ⟨47814633702947781620940305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127505689874527417655840813 47814633702947781620940305)
              ·
                refine ⟨35860975277210836215705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47814633702947781620940305 35860975277210836215705229)
                ·
                  refine ⟨13447865728954063580889461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35860975277210836215705229 13447865728954063580889461)
                  ·
                    refine ⟨1260737412089443460708387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13447865728954063580889461 1260737412089443460708387)
                    ·
                      rfl

theorem cell23_7365832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_7365832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365832 prefixEnd_7365832 := by exact prefixLift 7365832
  have htrace : WordTrace (prefixWord ++ tailWord_7365832) baseStart_7365832 baseEnd_7365832 := by
    simpa [prefixWord, tailWord_7365832, baseEnd_7365832] using wordTrace_append hprefix tailTrace_7365832
  have hstable : (prefixWord ++ tailWord_7365832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365832).length < 2 ^ (prefixWord ++ tailWord_7365832).sum := by decide
  have hdescent : baseEnd_7365832 < baseStart_7365832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365842 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7365842 : Nat := 118140960795 + 7365842 * 2 ^ 59
def prefixEnd_7365842 : Nat := 4983230072969 + 3 ^ 40 * 7365842 * 2
def baseEnd_7365842 : Nat := 3782217371074875343000115

theorem tailTrace_7365842 : CollatzResearch.WordTrace tailWord_7365842 prefixEnd_7365842 3782217371074875343000115 := by
  unfold tailWord_7365842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163582145204973626338945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179102885720546596336903853 67163582145204973626338945)
  ·
    refine ⟨50372686608903730219754209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67163582145204973626338945 50372686608903730219754209)
    ·
      refine ⟨37779514956677797664815657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50372686608903730219754209 37779514956677797664815657)
      ·
        refine ⟨28334636217508348248611743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37779514956677797664815657 28334636217508348248611743)
        ·
          refine ⟨42501954326262522372917615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28334636217508348248611743 42501954326262522372917615)
          ·
            refine ⟨63752931489393783559376423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42501954326262522372917615 63752931489393783559376423)
            ·
              refine ⟨95629397234090675339064635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63752931489393783559376423 95629397234090675339064635)
              ·
                refine ⟨143444095851136013008596953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95629397234090675339064635 143444095851136013008596953)
                ·
                  refine ⟨107583071888352009756447715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143444095851136013008596953 107583071888352009756447715)
                  ·
                    refine ⟨161374607832528014634671573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107583071888352009756447715 161374607832528014634671573)
                    ·
                      refine ⟨3782217371074875343000115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161374607832528014634671573 3782217371074875343000115)
                      ·
                        rfl

theorem cell23_7365842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7365842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365842 prefixEnd_7365842 := by exact prefixLift 7365842
  have htrace : WordTrace (prefixWord ++ tailWord_7365842) baseStart_7365842 baseEnd_7365842 := by
    simpa [prefixWord, tailWord_7365842, baseEnd_7365842] using wordTrace_append hprefix tailTrace_7365842
  have hstable : (prefixWord ++ tailWord_7365842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365842).length < 2 ^ (prefixWord ++ tailWord_7365842).sum := by decide
  have hdescent : baseEnd_7365842 < baseStart_7365842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365856 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2]
def baseStart_7365856 : Nat := 118140960795 + 7365856 * 2 ^ 59
def prefixEnd_7365856 : Nat := 4983230072969 + 3 ^ 40 * 7365856 * 2
def baseEnd_7365856 : Nat := 3782224559804038288225051

theorem tailTrace_7365856 : CollatzResearch.WordTrace tailWord_7365856 prefixEnd_7365856 3782224559804038288225051 := by
  unfold tailWord_7365856
  simp only [CollatzResearch.WordTrace]
  refine ⟨134327419601384587448182711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179103226135179449930910281 134327419601384587448182711)
  ·
    refine ⟨201491129402076881172274067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134327419601384587448182711 201491129402076881172274067)
    ·
      refine ⟨302236694103115321758411101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201491129402076881172274067 302236694103115321758411101)
      ·
        refine ⟨113338760288668245659404163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302236694103115321758411101 113338760288668245659404163)
        ·
          refine ⟨170008140433002368489106245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113338760288668245659404163 170008140433002368489106245)
          ·
            refine ⟨31876526331187944091707421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170008140433002368489106245 31876526331187944091707421)
            ·
              refine ⟨11953697374195479034390283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31876526331187944091707421 11953697374195479034390283)
              ·
                refine ⟨17930546061293218551585425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953697374195479034390283 17930546061293218551585425)
                ·
                  refine ⟨13447909545969913913689069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17930546061293218551585425 13447909545969913913689069)
                  ·
                    refine ⟨5042966079738717717633401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13447909545969913913689069 5042966079738717717633401)
                    ·
                      refine ⟨3782224559804038288225051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5042966079738717717633401 3782224559804038288225051)
                      ·
                        rfl

theorem cell23_7365856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_7365856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365856 prefixEnd_7365856 := by exact prefixLift 7365856
  have htrace : WordTrace (prefixWord ++ tailWord_7365856) baseStart_7365856 baseEnd_7365856 := by
    simpa [prefixWord, tailWord_7365856, baseEnd_7365856] using wordTrace_append hprefix tailTrace_7365856
  have hstable : (prefixWord ++ tailWord_7365856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365856).length < 2 ^ (prefixWord ++ tailWord_7365856).sum := by decide
  have hdescent : baseEnd_7365856 < baseStart_7365856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365866 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7365866 : Nat := 118140960795 + 7365866 * 2 ^ 59
def prefixEnd_7365866 : Nat := 4983230072969 + 3 ^ 40 * 7365866 * 2
def baseEnd_7365866 : Nat := 1260743231536861083033335

theorem tailTrace_7365866 : CollatzResearch.WordTrace tailWord_7365866 prefixEnd_7365866 1260743231536861083033335 := by
  unfold tailWord_7365866
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163800983183236651057363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179103469288488631069486301 67163800983183236651057363)
  ·
    refine ⟨100745701474774854976586045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67163800983183236651057363 100745701474774854976586045)
    ·
      refine ⟨37779638053040570616219767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100745701474774854976586045 37779638053040570616219767)
      ·
        refine ⟨56669457079560855924329651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37779638053040570616219767 56669457079560855924329651)
        ·
          refine ⟨85004185619341283886494477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56669457079560855924329651 85004185619341283886494477)
          ·
            refine ⟨31876569607252981457435429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85004185619341283886494477 31876569607252981457435429)
            ·
              refine ⟨5976856801359934023269143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31876569607252981457435429 5976856801359934023269143)
              ·
                refine ⟨8965285202039901034903715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976856801359934023269143 8965285202039901034903715)
                ·
                  refine ⟨13447927803059851552355573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965285202039901034903715 13447927803059851552355573)
                  ·
                    refine ⟨1260743231536861083033335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13447927803059851552355573 1260743231536861083033335)
                    ·
                      rfl

theorem cell23_7365866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7365866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365866 prefixEnd_7365866 := by exact prefixLift 7365866
  have htrace : WordTrace (prefixWord ++ tailWord_7365866) baseStart_7365866 baseEnd_7365866 := by
    simpa [prefixWord, tailWord_7365866, baseEnd_7365866] using wordTrace_append hprefix tailTrace_7365866
  have hstable : (prefixWord ++ tailWord_7365866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365866).length < 2 ^ (prefixWord ++ tailWord_7365866).sum := by decide
  have hdescent : baseEnd_7365866 < baseStart_7365866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365882 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_7365882 : Nat := 118140960795 + 7365882 * 2 ^ 59
def prefixEnd_7365882 : Nat := 4983230072969 + 3 ^ 40 * 7365882 * 2
def baseEnd_7365882 : Nat := 3782237910301055186499931

theorem tailTrace_7365882 : CollatzResearch.WordTrace tailWord_7365882 prefixEnd_7365882 3782237910301055186499931 := by
  unfold tailWord_7365882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163946875168745334202975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179103858333783320891207933 67163946875168745334202975)
  ·
    refine ⟨100745920312753118001304463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67163946875168745334202975 100745920312753118001304463)
    ·
      refine ⟨151118880469129677001956695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100745920312753118001304463 151118880469129677001956695)
      ·
        refine ⟨226678320703694515502935043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151118880469129677001956695 226678320703694515502935043)
        ·
          refine ⟨340017481055541773254402565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226678320703694515502935043 340017481055541773254402565)
          ·
            refine ⟨63753277697914082485200481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340017481055541773254402565 63753277697914082485200481)
            ·
              refine ⟨47814958273435561863900361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63753277697914082485200481 47814958273435561863900361)
              ·
                refine ⟨35861218705076671397925271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47814958273435561863900361 35861218705076671397925271)
                ·
                  refine ⟨53791828057615007096887907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35861218705076671397925271 53791828057615007096887907)
                  ·
                    refine ⟨80687742086422510645331861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53791828057615007096887907 80687742086422510645331861)
                    ·
                      refine ⟨3782237910301055186499931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80687742086422510645331861 3782237910301055186499931)
                      ·
                        rfl

theorem cell23_7365882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_7365882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365882 prefixEnd_7365882 := by exact prefixLift 7365882
  have htrace : WordTrace (prefixWord ++ tailWord_7365882) baseStart_7365882 baseEnd_7365882 := by
    simpa [prefixWord, tailWord_7365882, baseEnd_7365882] using wordTrace_append hprefix tailTrace_7365882
  have hstable : (prefixWord ++ tailWord_7365882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365882).length < 2 ^ (prefixWord ++ tailWord_7365882).sum := by decide
  have hdescent : baseEnd_7365882 < baseStart_7365882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365889 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7365889 : Nat := 118140960795 + 7365889 * 2 ^ 59
def prefixEnd_7365889 : Nat := 4983230072969 + 3 ^ 40 * 7365889 * 2
def baseEnd_7365889 : Nat := 3782241504665636659112399

theorem tailTrace_7365889 : CollatzResearch.WordTrace tailWord_7365889 prefixEnd_7365889 3782241504665636659112399 := by
  unfold tailWord_7365889
  simp only [CollatzResearch.WordTrace]
  refine ⟨268656042811649621532316721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179104028541099747688211147 268656042811649621532316721)
  ·
    refine ⟨201492032108737216149237541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268656042811649621532316721 201492032108737216149237541)
    ·
      refine ⟨37779756020388228027982039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201492032108737216149237541 37779756020388228027982039)
      ·
        refine ⟨56669634030582342041973059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37779756020388228027982039 56669634030582342041973059)
        ·
          refine ⟨85004451045873513062959589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56669634030582342041973059 85004451045873513062959589)
          ·
            refine ⟨15938334571101283699304923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85004451045873513062959589 15938334571101283699304923)
            ·
              refine ⟨23907501856651925548957385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15938334571101283699304923 23907501856651925548957385)
              ·
                refine ⟨17930626392488944161718039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23907501856651925548957385 17930626392488944161718039)
                ·
                  refine ⟨26895939588733416242577059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930626392488944161718039 26895939588733416242577059)
                  ·
                    refine ⟨40343909383100124363865589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26895939588733416242577059 40343909383100124363865589)
                    ·
                      refine ⟨3782241504665636659112399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40343909383100124363865589 3782241504665636659112399)
                      ·
                        rfl

theorem cell23_7365889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7365889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365889 prefixEnd_7365889 := by exact prefixLift 7365889
  have htrace : WordTrace (prefixWord ++ tailWord_7365889) baseStart_7365889 baseEnd_7365889 := by
    simpa [prefixWord, tailWord_7365889, baseEnd_7365889] using wordTrace_append hprefix tailTrace_7365889
  have hstable : (prefixWord ++ tailWord_7365889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365889).length < 2 ^ (prefixWord ++ tailWord_7365889).sum := by decide
  have hdescent : baseEnd_7365889 < baseStart_7365889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365896 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_7365896 : Nat := 118140960795 + 7365896 * 2 ^ 59
def prefixEnd_7365896 : Nat := 4983230072969 + 3 ^ 40 * 7365896 * 2
def baseEnd_7365896 : Nat := 1260748366343406043908289

theorem tailTrace_7365896 : CollatzResearch.WordTrace tailWord_7365896 prefixEnd_7365896 1260748366343406043908289 := by
  unfold tailWord_7365896
  simp only [CollatzResearch.WordTrace]
  refine ⟨134328149061312130863910771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179104198748416174485214361 134328149061312130863910771)
  ·
    refine ⟨201492223591968196295866157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134328149061312130863910771 201492223591968196295866157)
    ·
      refine ⟨75559583846988073610949809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201492223591968196295866157 75559583846988073610949809)
      ·
        refine ⟨56669687885241055208212357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75559583846988073610949809 56669687885241055208212357)
        ·
          refine ⟨10625566478482697851539817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56669687885241055208212357 10625566478482697851539817)
          ·
            refine ⟨7969174858862023388654863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10625566478482697851539817 7969174858862023388654863)
            ·
              refine ⟨11953762288293035082982295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969174858862023388654863 11953762288293035082982295)
              ·
                refine ⟨17930643432439552624473443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953762288293035082982295 17930643432439552624473443)
                ·
                  refine ⟨26895965148659328936710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930643432439552624473443 26895965148659328936710165)
                  ·
                    refine ⟨1260748366343406043908289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26895965148659328936710165 1260748366343406043908289)
                    ·
                      rfl

theorem cell23_7365896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_7365896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365896 prefixEnd_7365896 := by exact prefixLift 7365896
  have htrace : WordTrace (prefixWord ++ tailWord_7365896) baseStart_7365896 baseEnd_7365896 := by
    simpa [prefixWord, tailWord_7365896, baseEnd_7365896] using wordTrace_append hprefix tailTrace_7365896
  have hstable : (prefixWord ++ tailWord_7365896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365896).length < 2 ^ (prefixWord ++ tailWord_7365896).sum := by decide
  have hdescent : baseEnd_7365896 < baseStart_7365896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365899 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4]
def baseStart_7365899 : Nat := 118140960795 + 7365899 * 2 ^ 59
def prefixEnd_7365899 : Nat := 4983230072969 + 3 ^ 40 * 7365899 * 2
def baseEnd_7365899 : Nat := 3782246639472181619987353

theorem tailTrace_7365899 : CollatzResearch.WordTrace tailWord_7365899 prefixEnd_7365899 3782246639472181619987353 := by
  unfold tailWord_7365899
  simp only [CollatzResearch.WordTrace]
  refine ⟨268656407541613393240180751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179104271694408928826787167 268656407541613393240180751)
  ·
    refine ⟨402984611312420089860271127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268656407541613393240180751 402984611312420089860271127)
    ·
      refine ⟨604476916968630134790406691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402984611312420089860271127 604476916968630134790406691)
      ·
        refine ⟨906715375452945202185610037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604476916968630134790406691 906715375452945202185610037)
        ·
          refine ⟨85004566448713612704900941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 906715375452945202185610037 85004566448713612704900941)
          ·
            refine ⟨31876712418267604764337853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85004566448713612704900941 31876712418267604764337853)
            ·
              refine ⟨11953767156850351786626695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31876712418267604764337853 11953767156850351786626695)
              ·
                refine ⟨17930650735275527679940043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953767156850351786626695 17930650735275527679940043)
                ·
                  refine ⟨26895976102913291519910065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930650735275527679940043 26895976102913291519910065)
                  ·
                    refine ⟨20171982077184968639932549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26895976102913291519910065 20171982077184968639932549)
                    ·
                      refine ⟨3782246639472181619987353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20171982077184968639932549 3782246639472181619987353)
                      ·
                        rfl

theorem cell23_7365899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].length) (baseStart_7365899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365899 prefixEnd_7365899 := by exact prefixLift 7365899
  have htrace : WordTrace (prefixWord ++ tailWord_7365899) baseStart_7365899 baseEnd_7365899 := by
    simpa [prefixWord, tailWord_7365899, baseEnd_7365899] using wordTrace_append hprefix tailTrace_7365899
  have hstable : (prefixWord ++ tailWord_7365899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365899).length < 2 ^ (prefixWord ++ tailWord_7365899).sum := by decide
  have hdescent : baseEnd_7365899 < baseStart_7365899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365932 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_7365932 : Nat := 118140960795 + 7365932 * 2 ^ 59
def prefixEnd_7365932 : Nat := 4983230072969 + 3 ^ 40 * 7365932 * 2
def baseEnd_7365932 : Nat := 3782263584333779990874701

theorem tailTrace_7365932 : CollatzResearch.WordTrace tailWord_7365932 prefixEnd_7365932 3782263584333779990874701 := by
  unfold tailWord_7365932
  simp only [CollatzResearch.WordTrace]
  refine ⟨134328805575246919938066025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179105074100329226584088033 134328805575246919938066025)
  ·
    refine ⟨100746604181435189953549519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134328805575246919938066025 100746604181435189953549519)
    ·
      refine ⟨151119906272152784930324279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100746604181435189953549519 151119906272152784930324279)
      ·
        refine ⟨226679859408229177395486419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151119906272152784930324279 226679859408229177395486419)
        ·
          refine ⟨340019789112343766093229629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226679859408229177395486419 340019789112343766093229629)
          ·
            refine ⟨127507420917128912284961111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340019789112343766093229629 127507420917128912284961111)
            ·
              refine ⟨191261131375693368427441667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127507420917128912284961111 191261131375693368427441667)
              ·
                refine ⟨286891697063540052641162501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191261131375693368427441667 286891697063540052641162501)
                ·
                  refine ⟨53792193199413759870217969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286891697063540052641162501 53792193199413759870217969)
                  ·
                    refine ⟨40344144899560319902663477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53792193199413759870217969 40344144899560319902663477)
                    ·
                      refine ⟨3782263584333779990874701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40344144899560319902663477 3782263584333779990874701)
                      ·
                        rfl

theorem cell23_7365932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_7365932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365932 prefixEnd_7365932 := by exact prefixLift 7365932
  have htrace : WordTrace (prefixWord ++ tailWord_7365932) baseStart_7365932 baseEnd_7365932 := by
    simpa [prefixWord, tailWord_7365932, baseEnd_7365932] using wordTrace_append hprefix tailTrace_7365932
  have hstable : (prefixWord ++ tailWord_7365932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365932).length < 2 ^ (prefixWord ++ tailWord_7365932).sum := by decide
  have hdescent : baseEnd_7365932 < baseStart_7365932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365936 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_7365936 : Nat := 118140960795 + 7365936 * 2 ^ 59
def prefixEnd_7365936 : Nat := 4983230072969 + 3 ^ 40 * 7365936 * 2
def baseEnd_7365936 : Nat := 3782265638256397975224683

theorem tailTrace_7365936 : CollatzResearch.WordTrace tailWord_7365936 prefixEnd_7365936 3782265638256397975224683 := by
  unfold tailWord_7365936
  simp only [CollatzResearch.WordTrace]
  refine ⟨134328878521239674279638831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179105171361652899039518441 134328878521239674279638831)
  ·
    refine ⟨201493317781859511419458247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134328878521239674279638831 201493317781859511419458247)
    ·
      refine ⟨302239976672789267129187371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201493317781859511419458247 302239976672789267129187371)
      ·
        refine ⟨453359965009183900693781057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302239976672789267129187371 453359965009183900693781057)
        ·
          refine ⟨340019973756887925520335793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453359965009183900693781057 340019973756887925520335793)
          ·
            refine ⟨255014980317665944140251845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340019973756887925520335793 255014980317665944140251845)
            ·
              refine ⟨47815308809562364526297221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255014980317665944140251845 47815308809562364526297221)
              ·
                refine ⟨8965370401792943348680729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47815308809562364526297221 8965370401792943348680729)
                ·
                  refine ⟨6724027801344707511510547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8965370401792943348680729 6724027801344707511510547)
                  ·
                    refine ⟨10086041702017061267265821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6724027801344707511510547 10086041702017061267265821)
                    ·
                      refine ⟨3782265638256397975224683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10086041702017061267265821 3782265638256397975224683)
                      ·
                        rfl

theorem cell23_7365936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_7365936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365936 prefixEnd_7365936 := by exact prefixLift 7365936
  have htrace : WordTrace (prefixWord ++ tailWord_7365936) baseStart_7365936 baseEnd_7365936 := by
    simpa [prefixWord, tailWord_7365936, baseEnd_7365936] using wordTrace_append hprefix tailTrace_7365936
  have hstable : (prefixWord ++ tailWord_7365936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365936).length < 2 ^ (prefixWord ++ tailWord_7365936).sum := by decide
  have hdescent : baseEnd_7365936 < baseStart_7365936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365937 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_7365937 : Nat := 118140960795 + 7365937 * 2 ^ 59
def prefixEnd_7365937 : Nat := 4983230072969 + 3 ^ 40 * 7365937 * 2
def baseEnd_7365937 : Nat := 3782266151737052471312179

theorem tailTrace_7365937 : CollatzResearch.WordTrace tailWord_7365937 prefixEnd_7365937 3782266151737052471312179 := by
  unfold tailWord_7365937
  simp only [CollatzResearch.WordTrace]
  refine ⟨268657793515475725730064065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179105195676983817153376043 268657793515475725730064065)
  ·
    refine ⟨201493345136606794297548049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268657793515475725730064065 201493345136606794297548049)
    ·
      refine ⟨151120008852455095723161037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201493345136606794297548049 151120008852455095723161037)
      ·
        refine ⟨56670003319670660896185389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151120008852455095723161037 56670003319670660896185389)
        ·
          refine ⟨21251251244876497836069521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56670003319670660896185389 21251251244876497836069521)
          ·
            refine ⟨15938438433657373377052141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21251251244876497836069521 15938438433657373377052141)
            ·
              refine ⟨5976914412621515016394553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15938438433657373377052141 5976914412621515016394553)
              ·
                refine ⟨4482685809466136262295915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976914412621515016394553 4482685809466136262295915)
                ·
                  refine ⟨6724028714199204393443873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482685809466136262295915 6724028714199204393443873)
                  ·
                    refine ⟨5043021535649403295082905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724028714199204393443873 5043021535649403295082905)
                    ·
                      refine ⟨3782266151737052471312179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043021535649403295082905 3782266151737052471312179)
                      ·
                        rfl

theorem cell23_7365937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_7365937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365937 prefixEnd_7365937 := by exact prefixLift 7365937
  have htrace : WordTrace (prefixWord ++ tailWord_7365937) baseStart_7365937 baseEnd_7365937 := by
    simpa [prefixWord, tailWord_7365937, baseEnd_7365937] using wordTrace_append hprefix tailTrace_7365937
  have hstable : (prefixWord ++ tailWord_7365937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365937).length < 2 ^ (prefixWord ++ tailWord_7365937).sum := by decide
  have hdescent : baseEnd_7365937 < baseStart_7365937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365946 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_7365946 : Nat := 118140960795 + 7365946 * 2 ^ 59
def prefixEnd_7365946 : Nat := 4983230072969 + 3 ^ 40 * 7365946 * 2
def baseEnd_7365946 : Nat := 3782270773062942936099637

theorem tailTrace_7365946 : CollatzResearch.WordTrace tailWord_7365946 prefixEnd_7365946 3782270773062942936099637 := by
  unfold tailWord_7365946
  simp only [CollatzResearch.WordTrace]
  refine ⟨67164530443110780066785423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179105414514962080178094461 67164530443110780066785423)
  ·
    refine ⟨100746795664666170100178135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67164530443110780066785423 100746795664666170100178135)
    ·
      refine ⟨151120193496999255150267203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100746795664666170100178135 151120193496999255150267203)
      ·
        refine ⟨226680290245498882725400805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151120193496999255150267203 226680290245498882725400805)
        ·
          refine ⟨42502554421031040511012651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226680290245498882725400805 42502554421031040511012651)
          ·
            refine ⟨63753831631546560766518977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42502554421031040511012651 63753831631546560766518977)
            ·
              refine ⟨47815373723659920574889233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63753831631546560766518977 47815373723659920574889233)
              ·
                refine ⟨35861530292744940431166925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47815373723659920574889233 35861530292744940431166925)
                ·
                  refine ⟨13448073859779352661687597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35861530292744940431166925 13448073859779352661687597)
                  ·
                    refine ⟨5043027697417257248132849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13448073859779352661687597 5043027697417257248132849)
                    ·
                      refine ⟨3782270773062942936099637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043027697417257248132849 3782270773062942936099637)
                      ·
                        rfl

theorem cell23_7365946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_7365946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365946 prefixEnd_7365946 := by exact prefixLift 7365946
  have htrace : WordTrace (prefixWord ++ tailWord_7365946) baseStart_7365946 baseEnd_7365946 := by
    simpa [prefixWord, tailWord_7365946, baseEnd_7365946] using wordTrace_append hprefix tailTrace_7365946
  have hstable : (prefixWord ++ tailWord_7365946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365946).length < 2 ^ (prefixWord ++ tailWord_7365946).sum := by decide
  have hdescent : baseEnd_7365946 < baseStart_7365946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365952 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_7365952 : Nat := 118140960795 + 7365952 * 2 ^ 59
def prefixEnd_7365952 : Nat := 4983230072969 + 3 ^ 40 * 7365952 * 2
def baseEnd_7365952 : Nat := 1260757951315623304208203

theorem tailTrace_7365952 : CollatzResearch.WordTrace tailWord_7365952 prefixEnd_7365952 1260757951315623304208203 := by
  unfold tailWord_7365952
  simp only [CollatzResearch.WordTrace]
  refine ⟨134329170305210691645930055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179105560406947588861240073 134329170305210691645930055)
  ·
    refine ⟨201493755457816037468895083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134329170305210691645930055 201493755457816037468895083)
    ·
      refine ⟨302240633186724056203342625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201493755457816037468895083 302240633186724056203342625)
      ·
        refine ⟨226680474890043042152506969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302240633186724056203342625 226680474890043042152506969)
        ·
          refine ⟨170010356167532281614380227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226680474890043042152506969 170010356167532281614380227)
          ·
            refine ⟨255015534251298422421570341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170010356167532281614380227 255015534251298422421570341)
            ·
              refine ⟨47815412672118454204044439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255015534251298422421570341 47815412672118454204044439)
              ·
                refine ⟨71723119008177681306066659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47815412672118454204044439 71723119008177681306066659)
                ·
                  refine ⟨107584678512266521959099989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71723119008177681306066659 107584678512266521959099989)
                  ·
                    refine ⟨1260757951315623304208203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107584678512266521959099989 1260757951315623304208203)
                    ·
                      rfl

theorem cell23_7365952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_7365952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365952 prefixEnd_7365952 := by exact prefixLift 7365952
  have htrace : WordTrace (prefixWord ++ tailWord_7365952) baseStart_7365952 baseEnd_7365952 := by
    simpa [prefixWord, tailWord_7365952, baseEnd_7365952] using wordTrace_append hprefix tailTrace_7365952
  have hstable : (prefixWord ++ tailWord_7365952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365952).length < 2 ^ (prefixWord ++ tailWord_7365952).sum := by decide
  have hdescent : baseEnd_7365952 < baseStart_7365952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365974 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7365974 : Nat := 118140960795 + 7365974 * 2 ^ 59
def prefixEnd_7365974 : Nat := 4983230072969 + 3 ^ 40 * 7365974 * 2
def baseEnd_7365974 : Nat := 3782285150521268826549509

theorem tailTrace_7365974 : CollatzResearch.WordTrace tailWord_7365974 prefixEnd_7365974 3782285150521268826549509 := by
  unfold tailWord_7365974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791196438521355065572561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179106095344227787366107317 16791196438521355065572561)
  ·
    refine ⟨12593397328891016299179421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16791196438521355065572561 12593397328891016299179421)
    ·
      refine ⟨4722523998334131112192283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12593397328891016299179421 4722523998334131112192283)
      ·
        refine ⟨7083785997501196668288425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722523998334131112192283 7083785997501196668288425)
        ·
          refine ⟨5312839498125897501216319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083785997501196668288425 5312839498125897501216319)
          ·
            refine ⟨7969259247188846251824479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312839498125897501216319 7969259247188846251824479)
            ·
              refine ⟨11953888870783269377736719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969259247188846251824479 11953888870783269377736719)
              ·
                refine ⟨17930833306174904066605079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953888870783269377736719 17930833306174904066605079)
                ·
                  refine ⟨26896249959262356099907619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930833306174904066605079 26896249959262356099907619)
                  ·
                    refine ⟨40344374938893534149861429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26896249959262356099907619 40344374938893534149861429)
                    ·
                      refine ⟨3782285150521268826549509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40344374938893534149861429 3782285150521268826549509)
                      ·
                        rfl

theorem cell23_7365974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7365974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365974 prefixEnd_7365974 := by exact prefixLift 7365974
  have htrace : WordTrace (prefixWord ++ tailWord_7365974) baseStart_7365974 baseEnd_7365974 := by
    simpa [prefixWord, tailWord_7365974, baseEnd_7365974] using wordTrace_append hprefix tailTrace_7365974
  have hstable : (prefixWord ++ tailWord_7365974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365974).length < 2 ^ (prefixWord ++ tailWord_7365974).sum := by decide
  have hdescent : baseEnd_7365974 < baseStart_7365974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365976 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_7365976 : Nat := 118140960795 + 7365976 * 2 ^ 59
def prefixEnd_7365976 : Nat := 4983230072969 + 3 ^ 40 * 7365976 * 2
def baseEnd_7365976 : Nat := 3782286177482577818724499

theorem tailTrace_7365976 : CollatzResearch.WordTrace tailWord_7365976 prefixEnd_7365976 3782286177482577818724499 := by
  unfold tailWord_7365976
  simp only [CollatzResearch.WordTrace]
  refine ⟨134329607981167217695366891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179106143974889623593822521 134329607981167217695366891)
  ·
    refine ⟨201494411971750826543050337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134329607981167217695366891 201494411971750826543050337)
    ·
      refine ⟨151120808978813119907287753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201494411971750826543050337 151120808978813119907287753)
      ·
        refine ⟨113340606734109839930465815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151120808978813119907287753 113340606734109839930465815)
        ·
          refine ⟨170010910101164759895698723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113340606734109839930465815 170010910101164759895698723)
          ·
            refine ⟨255016365151747139843548085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170010910101164759895698723 255016365151747139843548085)
            ·
              refine ⟨23907784232976294360332633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255016365151747139843548085 23907784232976294360332633)
              ·
                refine ⟨17930838174732220770249475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23907784232976294360332633 17930838174732220770249475)
                ·
                  refine ⟨26896257262098331155374213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17930838174732220770249475 26896257262098331155374213)
                  ·
                    refine ⟨5043048236643437091632665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26896257262098331155374213 5043048236643437091632665)
                    ·
                      refine ⟨3782286177482577818724499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043048236643437091632665 3782286177482577818724499)
                      ·
                        rfl

theorem cell23_7365976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_7365976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365976 prefixEnd_7365976 := by exact prefixLift 7365976
  have htrace : WordTrace (prefixWord ++ tailWord_7365976) baseStart_7365976 baseEnd_7365976 := by
    simpa [prefixWord, tailWord_7365976, baseEnd_7365976] using wordTrace_append hprefix tailTrace_7365976
  have hstable : (prefixWord ++ tailWord_7365976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365976).length < 2 ^ (prefixWord ++ tailWord_7365976).sum := by decide
  have hdescent : baseEnd_7365976 < baseStart_7365976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7365989 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_7365989 : Nat := 118140960795 + 7365989 * 2 ^ 59
def prefixEnd_7365989 : Nat := 4983230072969 + 3 ^ 40 * 7365989 * 2
def baseEnd_7365989 : Nat := 3782292852731086267861939

theorem tailTrace_7365989 : CollatzResearch.WordTrace tailWord_7365989 prefixEnd_7365989 3782292852731086267861939 := by
  unfold tailWord_7365989
  simp only [CollatzResearch.WordTrace]
  refine ⟨268659690111287338610957021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179106460074191559073971347 268659690111287338610957021)
  ·
    refine ⟨100747383791732751979108883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268659690111287338610957021 100747383791732751979108883)
    ·
      refine ⟨151121075687599127968663325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100747383791732751979108883 151121075687599127968663325)
      ·
        refine ⟨56670403382849672988248747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151121075687599127968663325 56670403382849672988248747)
        ·
          refine ⟨85005605074274509482373121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56670403382849672988248747 85005605074274509482373121)
          ·
            refine ⟨63754203805705882111779841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85005605074274509482373121 63754203805705882111779841)
            ·
              refine ⟨47815652854279411583834881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63754203805705882111779841 47815652854279411583834881)
              ·
                refine ⟨35861739640709558687876161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47815652854279411583834881 35861739640709558687876161)
                ·
                  refine ⟨26896304730532169015907121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35861739640709558687876161 26896304730532169015907121)
                  ·
                    refine ⟨20172228547899126761930341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26896304730532169015907121 20172228547899126761930341)
                    ·
                      refine ⟨3782292852731086267861939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20172228547899126761930341 3782292852731086267861939)
                      ·
                        rfl

theorem cell23_7365989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_7365989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7365989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7365989 prefixEnd_7365989 := by exact prefixLift 7365989
  have htrace : WordTrace (prefixWord ++ tailWord_7365989) baseStart_7365989 baseEnd_7365989 := by
    simpa [prefixWord, tailWord_7365989, baseEnd_7365989] using wordTrace_append hprefix tailTrace_7365989
  have hstable : (prefixWord ++ tailWord_7365989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7365989).length < 2 ^ (prefixWord ++ tailWord_7365989).sum := by decide
  have hdescent : baseEnd_7365989 < baseStart_7365989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7365989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366009 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_7366009 : Nat := 118140960795 + 7366009 * 2 ^ 59
def prefixEnd_7366009 : Nat := 4983230072969 + 3 ^ 40 * 7366009 * 2
def baseEnd_7366009 : Nat := 3782303122344176189611847

theorem tailTrace_7366009 : CollatzResearch.WordTrace tailWord_7366009 prefixEnd_7366009 3782303122344176189611847 := by
  unfold tailWord_7366009
  simp only [CollatzResearch.WordTrace]
  refine ⟨268660419571214882026685081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179106946380809921351123387 268660419571214882026685081)
  ·
    refine ⟨201495314678411161520013811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268660419571214882026685081 201495314678411161520013811)
    ·
      refine ⟨302242972017616742280020717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201495314678411161520013811 302242972017616742280020717)
      ·
        refine ⟨113341114506606278355007769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302242972017616742280020717 113341114506606278355007769)
        ·
          refine ⟨85005835879954708766255827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113341114506606278355007769 85005835879954708766255827)
          ·
            refine ⟨127508753819932063149383741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85005835879954708766255827 127508753819932063149383741)
            ·
              refine ⟨47815782682474523681018903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127508753819932063149383741 47815782682474523681018903)
              ·
                refine ⟨71723674023711785521528355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47815782682474523681018903 71723674023711785521528355)
                ·
                  refine ⟨107585511035567678282292533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71723674023711785521528355 107585511035567678282292533)
                  ·
                    refine ⟨10086141659584469838964925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107585511035567678282292533 10086141659584469838964925)
                    ·
                      refine ⟨3782303122344176189611847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10086141659584469838964925 3782303122344176189611847)
                      ·
                        rfl

theorem cell23_7366009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_7366009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366009 prefixEnd_7366009 := by exact prefixLift 7366009
  have htrace : WordTrace (prefixWord ++ tailWord_7366009) baseStart_7366009 baseEnd_7366009 := by
    simpa [prefixWord, tailWord_7366009, baseEnd_7366009] using wordTrace_append hprefix tailTrace_7366009
  have hstable : (prefixWord ++ tailWord_7366009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366009).length < 2 ^ (prefixWord ++ tailWord_7366009).sum := by decide
  have hdescent : baseEnd_7366009 < baseStart_7366009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366044 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7366044 : Nat := 118140960795 + 7366044 * 2 ^ 59
def prefixEnd_7366044 : Nat := 4983230072969 + 3 ^ 40 * 7366044 * 2
def baseEnd_7366044 : Nat := 3782321094167083552674187

theorem tailTrace_7366044 : CollatzResearch.WordTrace tailWord_7366044 prefixEnd_7366044 3782321094167083552674187 := by
  unfold tailWord_7366044
  simp only [CollatzResearch.WordTrace]
  refine ⟨134330848063044041502104593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179107797417392055336139457 134330848063044041502104593)
  ·
    refine ⟨100748136047283031126578445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134330848063044041502104593 100748136047283031126578445)
    ·
      refine ⟨37780551017731136672466917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100748136047283031126578445 37780551017731136672466917)
      ·
        refine ⟨7083853315824588126087547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37780551017731136672466917 7083853315824588126087547)
        ·
          refine ⟨10625779973736882189131321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083853315824588126087547 10625779973736882189131321)
          ·
            refine ⟨7969334980302661641848491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10625779973736882189131321 7969334980302661641848491)
            ·
              refine ⟨11954002470453992462772737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969334980302661641848491 11954002470453992462772737)
              ·
                refine ⟨8965501852840494347079553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11954002470453992462772737 8965501852840494347079553)
                ·
                  refine ⟨6724126389630370760309665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8965501852840494347079553 6724126389630370760309665)
                  ·
                    refine ⟨5043094792222778070232249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724126389630370760309665 5043094792222778070232249)
                    ·
                      refine ⟨3782321094167083552674187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043094792222778070232249 3782321094167083552674187)
                      ·
                        rfl

theorem cell23_7366044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7366044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366044 prefixEnd_7366044 := by exact prefixLift 7366044
  have htrace : WordTrace (prefixWord ++ tailWord_7366044) baseStart_7366044 baseEnd_7366044 := by
    simpa [prefixWord, tailWord_7366044, baseEnd_7366044] using wordTrace_append hprefix tailTrace_7366044
  have hstable : (prefixWord ++ tailWord_7366044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366044).length < 2 ^ (prefixWord ++ tailWord_7366044).sum := by decide
  have hdescent : baseEnd_7366044 < baseStart_7366044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366066 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_7366066 : Nat := 118140960795 + 7366066 * 2 ^ 59
def prefixEnd_7366066 : Nat := 4983230072969 + 3 ^ 40 * 7366066 * 2
def baseEnd_7366066 : Nat := 3782332390741482466599085

theorem tailTrace_7366066 : CollatzResearch.WordTrace tailWord_7366066 prefixEnd_7366066 3782332390741482466599085 := by
  unfold tailWord_7366066
  simp only [CollatzResearch.WordTrace]
  refine ⟨67165624633002095190377513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179108332354672253841006701 67165624633002095190377513)
  ·
    refine ⟨50374218474751571392783135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67165624633002095190377513 50374218474751571392783135)
    ·
      refine ⟨75561327712127357089174703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50374218474751571392783135 75561327712127357089174703)
      ·
        refine ⟨113341991568191035633762055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75561327712127357089174703 113341991568191035633762055)
        ·
          refine ⟨170012987352286553450643083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113341991568191035633762055 170012987352286553450643083)
          ·
            refine ⟨255019481028429830175964625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170012987352286553450643083 255019481028429830175964625)
            ·
              refine ⟨191264610771322372631973469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255019481028429830175964625 191264610771322372631973469)
              ·
                refine ⟨71724229039245889736990051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191264610771322372631973469 71724229039245889736990051)
                ·
                  refine ⟨107586343558868834605485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71724229039245889736990051 107586343558868834605485077)
                  ·
                    refine ⟨5043109854321976622132113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107586343558868834605485077 5043109854321976622132113)
                    ·
                      refine ⟨3782332390741482466599085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043109854321976622132113 3782332390741482466599085)
                      ·
                        rfl

theorem cell23_7366066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_7366066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366066 prefixEnd_7366066 := by exact prefixLift 7366066
  have htrace : WordTrace (prefixWord ++ tailWord_7366066) baseStart_7366066 baseEnd_7366066 := by
    simpa [prefixWord, tailWord_7366066, baseEnd_7366066] using wordTrace_append hprefix tailTrace_7366066
  have hstable : (prefixWord ++ tailWord_7366066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366066).length < 2 ^ (prefixWord ++ tailWord_7366066).sum := by decide
  have hdescent : baseEnd_7366066 < baseStart_7366066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366136 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_7366136 : Nat := 118140960795 + 7366136 * 2 ^ 59
def prefixEnd_7366136 : Nat := 4983230072969 + 3 ^ 40 * 7366136 * 2
def baseEnd_7366136 : Nat := 1260789444795765730907921

theorem tailTrace_7366136 : CollatzResearch.WordTrace tailWord_7366136 prefixEnd_7366136 1260789444795765730907921 := by
  unfold tailWord_7366136
  simp only [CollatzResearch.WordTrace]
  refine ⟨134332525820877391358279131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179110034427836521811038841 134332525820877391358279131)
  ·
    refine ⟨201498788731316087037418697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134332525820877391358279131 201498788731316087037418697)
    ·
      refine ⟨151124091548487065278064023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201498788731316087037418697 151124091548487065278064023)
      ·
        refine ⟨226686137322730597917096035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151124091548487065278064023 226686137322730597917096035)
        ·
          refine ⟨340029205984095896875644053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226686137322730597917096035 340029205984095896875644053)
          ·
            refine ⟨15938869030504495166045815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340029205984095896875644053 15938869030504495166045815)
            ·
              refine ⟨23908303545756742749068723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15938869030504495166045815 23908303545756742749068723)
              ·
                refine ⟨35862455318635114123603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23908303545756742749068723 35862455318635114123603085)
                ·
                  refine ⟨13448420744488167796351157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35862455318635114123603085 13448420744488167796351157)
                  ·
                    refine ⟨1260789444795765730907921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13448420744488167796351157 1260789444795765730907921)
                    ·
                      rfl

theorem cell23_7366136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_7366136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366136 prefixEnd_7366136 := by exact prefixLift 7366136
  have htrace : WordTrace (prefixWord ++ tailWord_7366136) baseStart_7366136 baseEnd_7366136 := by
    simpa [prefixWord, tailWord_7366136, baseEnd_7366136] using wordTrace_append hprefix tailTrace_7366136
  have hstable : (prefixWord ++ tailWord_7366136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366136).length < 2 ^ (prefixWord ++ tailWord_7366136).sum := by decide
  have hdescent : baseEnd_7366136 < baseStart_7366136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366139 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_7366139 : Nat := 118140960795 + 7366139 * 2 ^ 59
def prefixEnd_7366139 : Nat := 4983230072969 + 3 ^ 40 * 7366139 * 2
def baseEnd_7366139 : Nat := 3782369874829260680986249

theorem tailTrace_7366139 : CollatzResearch.WordTrace tailWord_7366139 prefixEnd_7366139 3782369874829260680986249 := by
  unfold tailWord_7366139
  simp only [CollatzResearch.WordTrace]
  refine ⟨268665161060743914228917471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179110107373829276152611647 268665161060743914228917471)
  ·
    refine ⟨402997741591115871343376207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268665161060743914228917471 402997741591115871343376207)
    ·
      refine ⟨604496612386673807015064311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402997741591115871343376207 604496612386673807015064311)
      ·
        refine ⟨906744918580010710522596467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604496612386673807015064311 906744918580010710522596467)
        ·
          refine ⟨1360117377870016065783894701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906744918580010710522596467 1360117377870016065783894701)
          ·
            refine ⟨510044016701256024668960513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1360117377870016065783894701 510044016701256024668960513)
            ·
              refine ⟨382533012525942018501720385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510044016701256024668960513 382533012525942018501720385)
              ·
                refine ⟨286899759394456513876290289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382533012525942018501720385 286899759394456513876290289)
                ·
                  refine ⟨215174819545842385407217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286899759394456513876290289 215174819545842385407217717)
                  ·
                    refine ⟨20172639332422723631926661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215174819545842385407217717 20172639332422723631926661)
                    ·
                      refine ⟨3782369874829260680986249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20172639332422723631926661 3782369874829260680986249)
                      ·
                        rfl

theorem cell23_7366139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_7366139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366139 prefixEnd_7366139 := by exact prefixLift 7366139
  have htrace : WordTrace (prefixWord ++ tailWord_7366139) baseStart_7366139 baseEnd_7366139 := by
    simpa [prefixWord, tailWord_7366139, baseEnd_7366139] using wordTrace_append hprefix tailTrace_7366139
  have hstable : (prefixWord ++ tailWord_7366139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366139).length < 2 ^ (prefixWord ++ tailWord_7366139).sum := by decide
  have hdescent : baseEnd_7366139 < baseStart_7366139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366153 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_7366153 : Nat := 118140960795 + 7366153 * 2 ^ 59
def prefixEnd_7366153 : Nat := 4983230072969 + 3 ^ 40 * 7366153 * 2
def baseEnd_7366153 : Nat := 1260792354519474542070395

theorem tailTrace_7366153 : CollatzResearch.WordTrace tailWord_7366153 prefixEnd_7366153 1260792354519474542070395 := by
  unfold tailWord_7366153
  simp only [CollatzResearch.WordTrace]
  refine ⟨268665671682693194619927113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179110447788462129746618075 268665671682693194619927113)
  ·
    refine ⟨201499253762019895964945335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268665671682693194619927113 201499253762019895964945335)
    ·
      refine ⟨302248880643029843947418003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201499253762019895964945335 302248880643029843947418003)
      ·
        refine ⟨453373320964544765921127005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302248880643029843947418003 453373320964544765921127005)
        ·
          refine ⟨170014995361704287220422627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453373320964544765921127005 170014995361704287220422627)
          ·
            refine ⟨255022493042556430830633941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170014995361704287220422627 255022493042556430830633941)
            ·
              refine ⟨5977089680684916347592983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255022493042556430830633941 5977089680684916347592983)
              ·
                refine ⟨8965634521027374521389475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977089680684916347592983 8965634521027374521389475)
                ·
                  refine ⟨13448451781541061782084213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965634521027374521389475 13448451781541061782084213)
                  ·
                    refine ⟨1260792354519474542070395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13448451781541061782084213 1260792354519474542070395)
                    ·
                      rfl

theorem cell23_7366153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_7366153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366153 prefixEnd_7366153 := by exact prefixLift 7366153
  have htrace : WordTrace (prefixWord ++ tailWord_7366153) baseStart_7366153 baseEnd_7366153 := by
    simpa [prefixWord, tailWord_7366153, baseEnd_7366153] using wordTrace_append hprefix tailTrace_7366153
  have hstable : (prefixWord ++ tailWord_7366153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366153).length < 2 ^ (prefixWord ++ tailWord_7366153).sum := by decide
  have hdescent : baseEnd_7366153 < baseStart_7366153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366157 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7366157 : Nat := 118140960795 + 7366157 * 2 ^ 59
def prefixEnd_7366157 : Nat := 4983230072969 + 3 ^ 40 * 7366157 * 2
def baseEnd_7366157 : Nat := 420264346386782401173463

theorem tailTrace_7366157 : CollatzResearch.WordTrace tailWord_7366157 prefixEnd_7366157 420264346386782401173463 := by
  unfold tailWord_7366157
  simp only [CollatzResearch.WordTrace]
  refine ⟨268665817574678703303072725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179110545049785802202048483 268665817574678703303072725)
  ·
    refine ⟨6296855099406532108665767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 268665817574678703303072725 6296855099406532108665767)
    ·
      refine ⟨9445282649109798162998651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296855099406532108665767 9445282649109798162998651)
      ·
        refine ⟨14167923973664697244497977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445282649109798162998651 14167923973664697244497977)
        ·
          refine ⟨10625942980248522933373483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14167923973664697244497977 10625942980248522933373483)
          ·
            refine ⟨15938914470372784400060225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625942980248522933373483 15938914470372784400060225)
            ·
              refine ⟨11954185852779588300045169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15938914470372784400060225 11954185852779588300045169)
              ·
                refine ⟨8965639389584691225033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11954185852779588300045169 8965639389584691225033877)
                ·
                  refine ⟨420264346386782401173463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8965639389584691225033877 420264346386782401173463)
                  ·
                    rfl

theorem cell23_7366157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7366157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366157 prefixEnd_7366157 := by exact prefixLift 7366157
  have htrace : WordTrace (prefixWord ++ tailWord_7366157) baseStart_7366157 baseEnd_7366157 := by
    simpa [prefixWord, tailWord_7366157, baseEnd_7366157] using wordTrace_append hprefix tailTrace_7366157
  have hstable : (prefixWord ++ tailWord_7366157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366157).length < 2 ^ (prefixWord ++ tailWord_7366157).sum := by decide
  have hdescent : baseEnd_7366157 < baseStart_7366157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366193 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_7366193 : Nat := 118140960795 + 7366193 * 2 ^ 59
def prefixEnd_7366193 : Nat := 4983230072969 + 3 ^ 40 * 7366193 * 2
def baseEnd_7366193 : Nat := 3782397602784603469711001

theorem tailTrace_7366193 : CollatzResearch.WordTrace tailWord_7366193 prefixEnd_7366193 3782397602784603469711001 := by
  unfold tailWord_7366193
  simp only [CollatzResearch.WordTrace]
  refine ⟨268667130602548281451383233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179111420401698854300922155 268667130602548281451383233)
  ·
    refine ⟨201500347951911211088537425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268667130602548281451383233 201500347951911211088537425)
    ·
      refine ⟨151125260963933408316403069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201500347951911211088537425 151125260963933408316403069)
      ·
        refine ⟨56671972861475028118651151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151125260963933408316403069 56671972861475028118651151)
        ·
          refine ⟨85007959292212542177976727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56671972861475028118651151 85007959292212542177976727)
          ·
            refine ⟨127511938938318813266965091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85007959292212542177976727 127511938938318813266965091)
            ·
              refine ⟨191267908407478219900447637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127511938938318813266965091 191267908407478219900447637)
              ·
                refine ⟨8965683206600541557833483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191267908407478219900447637 8965683206600541557833483)
                ·
                  refine ⟨13448524809900812336750225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965683206600541557833483 13448524809900812336750225)
                  ·
                    refine ⟨10086393607425609252562669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13448524809900812336750225 10086393607425609252562669)
                    ·
                      refine ⟨3782397602784603469711001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10086393607425609252562669 3782397602784603469711001)
                      ·
                        rfl

theorem cell23_7366193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_7366193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366193 prefixEnd_7366193 := by exact prefixLift 7366193
  have htrace : WordTrace (prefixWord ++ tailWord_7366193) baseStart_7366193 baseEnd_7366193 := by
    simpa [prefixWord, tailWord_7366193, baseEnd_7366193] using wordTrace_append hprefix tailTrace_7366193
  have hstable : (prefixWord ++ tailWord_7366193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366193).length < 2 ^ (prefixWord ++ tailWord_7366193).sum := by decide
  have hdescent : baseEnd_7366193 < baseStart_7366193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366207 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 1, 2, 2]
def baseStart_7366207 : Nat := 118140960795 + 7366207 * 2 ^ 59
def prefixEnd_7366207 : Nat := 4983230072969 + 3 ^ 40 * 7366207 * 2
def baseEnd_7366207 : Nat := 3782404791513766414935937

theorem tailTrace_7366207 : CollatzResearch.WordTrace tailWord_7366207 prefixEnd_7366207 3782404791513766414935937 := by
  unfold tailWord_7366207
  simp only [CollatzResearch.WordTrace]
  refine ⟨268667641224497561842392875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179111760816331707894928583 268667641224497561842392875)
  ·
    refine ⟨403001461836746342763589313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268667641224497561842392875 403001461836746342763589313)
    ·
      refine ⟨302251096377559757072691985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403001461836746342763589313 302251096377559757072691985)
      ·
        refine ⟨226688322283169817804518989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302251096377559757072691985 226688322283169817804518989)
        ·
          refine ⟨85008120856188681676694621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226688322283169817804518989 85008120856188681676694621)
          ·
            refine ⟨31878045321070755628760483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85008120856188681676694621 31878045321070755628760483)
            ·
              refine ⟨47817067981606133443140725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31878045321070755628760483 47817067981606133443140725)
              ·
                refine ⟨4482850123275575010294443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47817067981606133443140725 4482850123275575010294443)
                ·
                  refine ⟨6724275184913362515441665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482850123275575010294443 6724275184913362515441665)
                  ·
                    refine ⟨5043206388685021886581249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724275184913362515441665 5043206388685021886581249)
                    ·
                      refine ⟨3782404791513766414935937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043206388685021886581249 3782404791513766414935937)
                      ·
                        rfl

theorem cell23_7366207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_7366207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366207 prefixEnd_7366207 := by exact prefixLift 7366207
  have htrace : WordTrace (prefixWord ++ tailWord_7366207) baseStart_7366207 baseEnd_7366207 := by
    simpa [prefixWord, tailWord_7366207, baseEnd_7366207] using wordTrace_append hprefix tailTrace_7366207
  have hstable : (prefixWord ++ tailWord_7366207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366207).length < 2 ^ (prefixWord ++ tailWord_7366207).sum := by decide
  have hdescent : baseEnd_7366207 < baseStart_7366207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366233 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 5, 3, 2]
def baseStart_7366233 : Nat := 118140960795 + 7366233 * 2 ^ 59
def prefixEnd_7366233 : Nat := 4983230072969 + 3 ^ 40 * 7366233 * 2
def baseEnd_7366233 : Nat := 3782418142010783313210817

theorem tailTrace_7366233 : CollatzResearch.WordTrace tailWord_7366233 prefixEnd_7366233 3782418142010783313210817 := by
  unfold tailWord_7366233
  simp only [CollatzResearch.WordTrace]
  refine ⟨268668589522403368282839353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179112393014935578855226235 268668589522403368282839353)
  ·
    refine ⟨201501442141802526212129515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268668589522403368282839353 201501442141802526212129515)
    ·
      refine ⟨302252163212703789318194273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201501442141802526212129515 302252163212703789318194273)
      ·
        refine ⟨226689122409527841988645705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302252163212703789318194273 226689122409527841988645705)
        ·
          refine ⟨170016841807145881491484279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226689122409527841988645705 170016841807145881491484279)
          ·
            refine ⟨255025262710718822237226419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170016841807145881491484279 255025262710718822237226419)
            ·
              refine ⟨382537894066078233355839629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255025262710718822237226419 382537894066078233355839629)
              ·
                refine ⟨143451710274779337508439861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382537894066078233355839629 143451710274779337508439861)
                ·
                  refine ⟨13448597838260562891416237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143451710274779337508439861 13448597838260562891416237)
                  ·
                    refine ⟨5043224189347711084281089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13448597838260562891416237 5043224189347711084281089)
                    ·
                      refine ⟨3782418142010783313210817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043224189347711084281089 3782418142010783313210817)
                      ·
                        rfl

theorem cell23_7366233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_7366233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366233 prefixEnd_7366233 := by exact prefixLift 7366233
  have htrace : WordTrace (prefixWord ++ tailWord_7366233) baseStart_7366233 baseEnd_7366233 := by
    simpa [prefixWord, tailWord_7366233, baseEnd_7366233] using wordTrace_append hprefix tailTrace_7366233
  have hstable : (prefixWord ++ tailWord_7366233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366233).length < 2 ^ (prefixWord ++ tailWord_7366233).sum := by decide
  have hdescent : baseEnd_7366233 < baseStart_7366233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366263 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_7366263 : Nat := 118140960795 + 7366263 * 2 ^ 59
def prefixEnd_7366263 : Nat := 4983230072969 + 3 ^ 40 * 7366263 * 2
def baseEnd_7366263 : Nat := 3782433546430418195835679

theorem tailTrace_7366263 : CollatzResearch.WordTrace tailWord_7366263 prefixEnd_7366263 3782433546430418195835679 := by
  unfold tailWord_7366263
  simp only [CollatzResearch.WordTrace]
  refine ⟨268669683712294683406431443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179113122474863122270954295 268669683712294683406431443)
  ·
    refine ⟨403004525568442025109647165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268669683712294683406431443 403004525568442025109647165)
    ·
      refine ⟨151126697088165759416117687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403004525568442025109647165 151126697088165759416117687)
      ·
        refine ⟨226690045632248639124176531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151126697088165759416117687 226690045632248639124176531)
        ·
          refine ⟨340035068448372958686264797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226690045632248639124176531 340035068448372958686264797)
          ·
            refine ⟨127513150668139859507349299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340035068448372958686264797 127513150668139859507349299)
            ·
              refine ⟨191269726002209789261023949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127513150668139859507349299 191269726002209789261023949)
              ·
                refine ⟨71726147250828670972883981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191269726002209789261023949 71726147250828670972883981)
                ·
                  refine ⟨26897305219060751614831493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71726147250828670972883981 26897305219060751614831493)
                  ·
                    refine ⟨5043244728573890927780905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26897305219060751614831493 5043244728573890927780905)
                    ·
                      refine ⟨3782433546430418195835679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043244728573890927780905 3782433546430418195835679)
                      ·
                        rfl

theorem cell23_7366263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_7366263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366263 prefixEnd_7366263 := by exact prefixLift 7366263
  have htrace : WordTrace (prefixWord ++ tailWord_7366263) baseStart_7366263 baseEnd_7366263 := by
    simpa [prefixWord, tailWord_7366263, baseEnd_7366263] using wordTrace_append hprefix tailTrace_7366263
  have hstable : (prefixWord ++ tailWord_7366263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366263).length < 2 ^ (prefixWord ++ tailWord_7366263).sum := by decide
  have hdescent : baseEnd_7366263 < baseStart_7366263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366333 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_7366333 : Nat := 118140960795 + 7366333 * 2 ^ 59
def prefixEnd_7366333 : Nat := 4983230072969 + 3 ^ 40 * 7366333 * 2
def baseEnd_7366333 : Nat := 1260823163358744307320119

theorem tailTrace_7366333 : CollatzResearch.WordTrace tailWord_7366333 prefixEnd_7366333 1260823163358744307320119 := by
  unfold tailWord_7366333
  simp only [CollatzResearch.WordTrace]
  refine ⟨268672236822041085361479653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179114824548027390240986435 268672236822041085361479653)
  ·
    refine ⟨50376044404132703505277435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268672236822041085361479653 50376044404132703505277435)
    ·
      refine ⟨75564066606199055257916153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50376044404132703505277435 75564066606199055257916153)
      ·
        refine ⟨56673049954649291443437115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75564066606199055257916153 56673049954649291443437115)
        ·
          refine ⟨85009574931973937165155673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56673049954649291443437115 85009574931973937165155673)
          ·
            refine ⟨63757181198980452873866755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85009574931973937165155673 63757181198980452873866755)
            ·
              refine ⟨95635771798470679310800133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63757181198980452873866755 95635771798470679310800133)
              ·
                refine ⟨17931707212213252370775025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95635771798470679310800133 17931707212213252370775025)
                ·
                  refine ⟨13448780409159939278081269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17931707212213252370775025 13448780409159939278081269)
                  ·
                    refine ⟨1260823163358744307320119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13448780409159939278081269 1260823163358744307320119)
                    ·
                      rfl

theorem cell23_7366333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_7366333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366333 prefixEnd_7366333 := by exact prefixLift 7366333
  have htrace : WordTrace (prefixWord ++ tailWord_7366333) baseStart_7366333 baseEnd_7366333 := by
    simpa [prefixWord, tailWord_7366333, baseEnd_7366333] using wordTrace_append hprefix tailTrace_7366333
  have hstable : (prefixWord ++ tailWord_7366333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366333).length < 2 ^ (prefixWord ++ tailWord_7366333).sum := by decide
  have hdescent : baseEnd_7366333 < baseStart_7366333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366340 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_7366340 : Nat := 118140960795 + 7366340 * 2 ^ 59
def prefixEnd_7366340 : Nat := 4983230072969 + 3 ^ 40 * 7366340 * 2
def baseEnd_7366340 : Nat := 3782473084440814394572825

theorem tailTrace_7366340 : CollatzResearch.WordTrace tailWord_7366340 prefixEnd_7366340 3782473084440814394572825 := by
  unfold tailWord_7366340
  simp only [CollatzResearch.WordTrace]
  refine ⟨134336246066507862778492237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179114994755343817037989649 134336246066507862778492237)
  ·
    refine ⟨50376092274940448541934589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134336246066507862778492237 50376092274940448541934589)
    ·
      refine ⟨18891034603102668203225471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50376092274940448541934589 18891034603102668203225471)
      ·
        refine ⟨28336551904654002304838207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18891034603102668203225471 28336551904654002304838207)
        ·
          refine ⟨42504827856981003457257311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28336551904654002304838207 42504827856981003457257311)
          ·
            refine ⟨63757241785471505185885967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42504827856981003457257311 63757241785471505185885967)
            ·
              refine ⟨95635862678207257778828951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63757241785471505185885967 95635862678207257778828951)
              ·
                refine ⟨143453794017310886668243427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95635862678207257778828951 143453794017310886668243427)
                ·
                  refine ⟨215180691025966330002365141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143453794017310886668243427 215180691025966330002365141)
                  ·
                    refine ⟨5043297445921085859430433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215180691025966330002365141 5043297445921085859430433)
                    ·
                      refine ⟨3782473084440814394572825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043297445921085859430433 3782473084440814394572825)
                      ·
                        rfl

theorem cell23_7366340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_7366340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366340 prefixEnd_7366340 := by exact prefixLift 7366340
  have htrace : WordTrace (prefixWord ++ tailWord_7366340) baseStart_7366340 baseEnd_7366340 := by
    simpa [prefixWord, tailWord_7366340, baseEnd_7366340] using wordTrace_append hprefix tailTrace_7366340
  have hstable : (prefixWord ++ tailWord_7366340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366340).length < 2 ^ (prefixWord ++ tailWord_7366340).sum := by decide
  have hdescent : baseEnd_7366340 < baseStart_7366340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366473 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_7366473 : Nat := 118140960795 + 7366473 * 2 ^ 59
def prefixEnd_7366473 : Nat := 4983230072969 + 3 ^ 40 * 7366473 * 2
def baseEnd_7366473 : Nat := 3782541377367862374209713

theorem tailTrace_7366473 : CollatzResearch.WordTrace tailWord_7366473 prefixEnd_7366473 3782541377367862374209713 := by
  unfold tailWord_7366473
  simp only [CollatzResearch.WordTrace]
  refine ⟨268677343041533889271576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179118228694355926181050715 268677343041533889271576073)
  ·
    refine ⟨201508007281150416953682055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268677343041533889271576073 201508007281150416953682055)
    ·
      refine ⟨302262010921725625430523083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201508007281150416953682055 302262010921725625430523083)
      ·
        refine ⟨453393016382588438145784625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302262010921725625430523083 453393016382588438145784625)
        ·
          refine ⟨340044762286941328609338469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453393016382588438145784625 340044762286941328609338469)
          ·
            refine ⟨63758392928801499114250963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340044762286941328609338469 63758392928801499114250963)
            ·
              refine ⟨95637589393202248671376445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63758392928801499114250963 95637589393202248671376445)
              ·
                refine ⟨35864096022450843251766167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95637589393202248671376445 35864096022450843251766167)
                ·
                  refine ⟨53796144033676264877649251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35864096022450843251766167 53796144033676264877649251)
                  ·
                    refine ⟨80694216050514397316473877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53796144033676264877649251 80694216050514397316473877)
                    ·
                      refine ⟨3782541377367862374209713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80694216050514397316473877 3782541377367862374209713)
                      ·
                        rfl

theorem cell23_7366473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_7366473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366473 prefixEnd_7366473 := by exact prefixLift 7366473
  have htrace : WordTrace (prefixWord ++ tailWord_7366473) baseStart_7366473 baseEnd_7366473 := by
    simpa [prefixWord, tailWord_7366473, baseEnd_7366473] using wordTrace_append hprefix tailTrace_7366473
  have hstable : (prefixWord ++ tailWord_7366473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366473).length < 2 ^ (prefixWord ++ tailWord_7366473).sum := by decide
  have hdescent : baseEnd_7366473 < baseStart_7366473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366490 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_7366490 : Nat := 118140960795 + 7366490 * 2 ^ 59
def prefixEnd_7366490 : Nat := 4983230072969 + 3 ^ 40 * 7366490 * 2
def baseEnd_7366490 : Nat := 3782550106538988807697135

theorem tailTrace_7366490 : CollatzResearch.WordTrace tailWord_7366490 prefixEnd_7366490 3782550106538988807697135 := by
  unfold tailWord_7366490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67169490770618075293736231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179118642054981534116629949 67169490770618075293736231)
  ·
    refine ⟨100754236155927112940604347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67169490770618075293736231 100754236155927112940604347)
    ·
      refine ⟨151131354233890669410906521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100754236155927112940604347 151131354233890669410906521)
      ·
        refine ⟨113348515675418002058179891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151131354233890669410906521 113348515675418002058179891)
        ·
          refine ⟨170022773513127003087269837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113348515675418002058179891 170022773513127003087269837)
          ·
            refine ⟨63758540067422626157726189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170022773513127003087269837 63758540067422626157726189)
            ·
              refine ⟨23909452525283484809147321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63758540067422626157726189 23909452525283484809147321)
              ·
                refine ⟨17932089393962613606860491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23909452525283484809147321 17932089393962613606860491)
                ·
                  refine ⟨26898134090943920410290737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17932089393962613606860491 26898134090943920410290737)
                  ·
                    refine ⟨20173600568207940307718053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26898134090943920410290737 20173600568207940307718053)
                    ·
                      refine ⟨3782550106538988807697135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20173600568207940307718053 3782550106538988807697135)
                      ·
                        rfl

theorem cell23_7366490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_7366490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366490 prefixEnd_7366490 := by exact prefixLift 7366490
  have htrace : WordTrace (prefixWord ++ tailWord_7366490) baseStart_7366490 baseEnd_7366490 := by
    simpa [prefixWord, tailWord_7366490, baseEnd_7366490] using wordTrace_append hprefix tailTrace_7366490
  have hstable : (prefixWord ++ tailWord_7366490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366490).length < 2 ^ (prefixWord ++ tailWord_7366490).sum := by decide
  have hdescent : baseEnd_7366490 < baseStart_7366490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366500 : List Nat := [2, 3, 1, 1, 6, 10]
def baseStart_7366500 : Nat := 118140960795 + 7366500 * 2 ^ 59
def prefixEnd_7366500 : Nat := 4983230072969 + 3 ^ 40 * 7366500 * 2
def baseEnd_7366500 : Nat := 15566070952039233615523

theorem tailTrace_7366500 : CollatzResearch.WordTrace tailWord_7366500 prefixEnd_7366500 15566070952039233615523 := by
  unfold tailWord_7366500
  simp only [CollatzResearch.WordTrace]
  refine ⟨134339163906218036441404477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179118885208290715255205969 134339163906218036441404477)
  ·
    refine ⟨50377186464831763665526679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134339163906218036441404477 50377186464831763665526679)
    ·
      refine ⟨75565779697247645498290019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50377186464831763665526679 75565779697247645498290019)
      ·
        refine ⟨113348669545871468247435029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75565779697247645498290019 113348669545871468247435029)
        ·
          refine ⟨5313218884962725074098517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113348669545871468247435029 5313218884962725074098517)
          ·
            refine ⟨15566070952039233615523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5313218884962725074098517 15566070952039233615523)
            ·
              rfl

theorem cell23_7366500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 10].length) (baseStart_7366500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366500 prefixEnd_7366500 := by exact prefixLift 7366500
  have htrace : WordTrace (prefixWord ++ tailWord_7366500) baseStart_7366500 baseEnd_7366500 := by
    simpa [prefixWord, tailWord_7366500, baseEnd_7366500] using wordTrace_append hprefix tailTrace_7366500
  have hstable : (prefixWord ++ tailWord_7366500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366500).length < 2 ^ (prefixWord ++ tailWord_7366500).sum := by decide
  have hdescent : baseEnd_7366500 < baseStart_7366500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366513 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_7366513 : Nat := 118140960795 + 7366513 * 2 ^ 59
def prefixEnd_7366513 : Nat := 4983230072969 + 3 ^ 40 * 7366513 * 2
def baseEnd_7366513 : Nat := 1260853972198014072569843

theorem tailTrace_7366513 : CollatzResearch.WordTrace tailWord_7366513 prefixEnd_7366513 1260853972198014072569843 := by
  unfold tailWord_7366513
  simp only [CollatzResearch.WordTrace]
  refine ⟨268678801961388976103032193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179119201307592650735354795 268678801961388976103032193)
  ·
    refine ⟨201509101471041732077274145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268678801961388976103032193 201509101471041732077274145)
    ·
      refine ⟨151131826103281299057955609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201509101471041732077274145 151131826103281299057955609)
      ·
        refine ⟨113348869577460974293466707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151131826103281299057955609 113348869577460974293466707)
        ·
          refine ⟨170023304366191461440200061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113348869577460974293466707 170023304366191461440200061)
          ·
            refine ⟨63758739137321798040075023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170023304366191461440200061 63758739137321798040075023)
            ·
              refine ⟨95638108705982697060112535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63758739137321798040075023 95638108705982697060112535)
              ·
                refine ⟨143457163058974045590168803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95638108705982697060112535 143457163058974045590168803)
                ·
                  refine ⟨215185744588461068385253205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143457163058974045590168803 215185744588461068385253205)
                  ·
                    refine ⟨1260853972198014072569843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215185744588461068385253205 1260853972198014072569843)
                    ·
                      rfl

theorem cell23_7366513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_7366513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366513 prefixEnd_7366513 := by exact prefixLift 7366513
  have htrace : WordTrace (prefixWord ++ tailWord_7366513) baseStart_7366513 baseEnd_7366513 := by
    simpa [prefixWord, tailWord_7366513, baseEnd_7366513] using wordTrace_append hprefix tailTrace_7366513
  have hstable : (prefixWord ++ tailWord_7366513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366513).length < 2 ^ (prefixWord ++ tailWord_7366513).sum := by decide
  have hdescent : baseEnd_7366513 < baseStart_7366513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366523 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_7366523 : Nat := 118140960795 + 7366523 * 2 ^ 59
def prefixEnd_7366523 : Nat := 4983230072969 + 3 ^ 40 * 7366523 * 2
def baseEnd_7366523 : Nat := 3782567051400587178584483

theorem tailTrace_7366523 : CollatzResearch.WordTrace tailWord_7366523 prefixEnd_7366523 3782567051400587178584483 := by
  unfold tailWord_7366523
  simp only [CollatzResearch.WordTrace]
  refine ⟨268679166691352747810896223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179119444460901831873930815 268679166691352747810896223)
  ·
    refine ⟨403018750037029121716344335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268679166691352747810896223 403018750037029121716344335)
    ·
      refine ⟨604528125055543682574516503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403018750037029121716344335 604528125055543682574516503)
      ·
        refine ⟨906792187583315523861774755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604528125055543682574516503 906792187583315523861774755)
        ·
          refine ⟨1360188281374973285792662133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906792187583315523861774755 1360188281374973285792662133)
          ·
            refine ⟨127517651378903745543062075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1360188281374973285792662133 127517651378903745543062075)
            ·
              refine ⟨191276477068355618314593113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127517651378903745543062075 191276477068355618314593113)
              ·
                refine ⟨143457357801266713735944835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191276477068355618314593113 143457357801266713735944835)
                ·
                  refine ⟨215186036701900070603917253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143457357801266713735944835 215186036701900070603917253)
                  ·
                    refine ⟨40347381881606263238234485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215186036701900070603917253 40347381881606263238234485)
                    ·
                      refine ⟨3782567051400587178584483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40347381881606263238234485 3782567051400587178584483)
                      ·
                        rfl

theorem cell23_7366523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_7366523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366523 prefixEnd_7366523 := by exact prefixLift 7366523
  have htrace : WordTrace (prefixWord ++ tailWord_7366523) baseStart_7366523 baseEnd_7366523 := by
    simpa [prefixWord, tailWord_7366523, baseEnd_7366523] using wordTrace_append hprefix tailTrace_7366523
  have hstable : (prefixWord ++ tailWord_7366523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366523).length < 2 ^ (prefixWord ++ tailWord_7366523).sum := by decide
  have hdescent : baseEnd_7366523 < baseStart_7366523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366537 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 3, 3, 2]
def baseStart_7366537 : Nat := 118140960795 + 7366537 * 2 ^ 59
def prefixEnd_7366537 : Nat := 4983230072969 + 3 ^ 40 * 7366537 * 2
def baseEnd_7366537 : Nat := 3782574240129750123809419

theorem tailTrace_7366537 : CollatzResearch.WordTrace tailWord_7366537 prefixEnd_7366537 3782574240129750123809419 := by
  unfold tailWord_7366537
  simp only [CollatzResearch.WordTrace]
  refine ⟨268679677313302028201905865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179119784875534685467937243 268679677313302028201905865)
  ·
    refine ⟨201509757984976521151429399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268679677313302028201905865 201509757984976521151429399)
    ·
      refine ⟨302264636977464781727144099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201509757984976521151429399 302264636977464781727144099)
      ·
        refine ⟨453396955466197172590716149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302264636977464781727144099 453396955466197172590716149)
        ·
          refine ⟨42505964574955984930379639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453396955466197172590716149 42505964574955984930379639)
          ·
            refine ⟨63758946862433977395569459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42505964574955984930379639 63758946862433977395569459)
            ·
              refine ⟨95638420293650966093354189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63758946862433977395569459 95638420293650966093354189)
              ·
                refine ⟨35864407610119112285007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95638420293650966093354189 35864407610119112285007821)
                ·
                  refine ⟨13449152853794667106877933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35864407610119112285007821 13449152853794667106877933)
                  ·
                    refine ⟨5043432320173000165079225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13449152853794667106877933 5043432320173000165079225)
                    ·
                      refine ⟨3782574240129750123809419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043432320173000165079225 3782574240129750123809419)
                      ·
                        rfl

theorem cell23_7366537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3, 2].length) (baseStart_7366537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366537 prefixEnd_7366537 := by exact prefixLift 7366537
  have htrace : WordTrace (prefixWord ++ tailWord_7366537) baseStart_7366537 baseEnd_7366537 := by
    simpa [prefixWord, tailWord_7366537, baseEnd_7366537] using wordTrace_append hprefix tailTrace_7366537
  have hstable : (prefixWord ++ tailWord_7366537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366537).length < 2 ^ (prefixWord ++ tailWord_7366537).sum := by decide
  have hdescent : baseEnd_7366537 < baseStart_7366537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366588 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7366588 : Nat := 118140960795 + 7366588 * 2 ^ 59
def prefixEnd_7366588 : Nat := 4983230072969 + 3 ^ 40 * 7366588 * 2
def baseEnd_7366588 : Nat := 3782600427643129424271685

theorem tailTrace_7366588 : CollatzResearch.WordTrace tailWord_7366588 prefixEnd_7366588 3782600427643129424271685 := by
  unfold tailWord_7366588
  simp only [CollatzResearch.WordTrace]
  refine ⟨134340768718058631956006209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179121024957411509274674945 134340768718058631956006209)
  ·
    refine ⟨100755576538543973967004657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134340768718058631956006209 100755576538543973967004657)
    ·
      refine ⟨75566682403907980475253493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100755576538543973967004657 75566682403907980475253493)
      ·
        refine ⟨7084376475366373169555015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75566682403907980475253493 7084376475366373169555015)
        ·
          refine ⟨10626564713049559754332523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084376475366373169555015 10626564713049559754332523)
          ·
            refine ⟨15939847069574339631498785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626564713049559754332523 15939847069574339631498785)
            ·
              refine ⟨11954885302180754723624089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15939847069574339631498785 11954885302180754723624089)
              ·
                refine ⟨8966163976635566042718067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11954885302180754723624089 8966163976635566042718067)
                ·
                  refine ⟨13449245964953349064077101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966163976635566042718067 13449245964953349064077101)
                  ·
                    refine ⟨5043467236857505899028913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13449245964953349064077101 5043467236857505899028913)
                    ·
                      refine ⟨3782600427643129424271685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043467236857505899028913 3782600427643129424271685)
                      ·
                        rfl

theorem cell23_7366588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7366588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366588 prefixEnd_7366588 := by exact prefixLift 7366588
  have htrace : WordTrace (prefixWord ++ tailWord_7366588) baseStart_7366588 baseEnd_7366588 := by
    simpa [prefixWord, tailWord_7366588, baseEnd_7366588] using wordTrace_append hprefix tailTrace_7366588
  have hstable : (prefixWord ++ tailWord_7366588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366588).length < 2 ^ (prefixWord ++ tailWord_7366588).sum := by decide
  have hdescent : baseEnd_7366588 < baseStart_7366588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366640 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_7366640 : Nat := 118140960795 + 7366640 * 2 ^ 59
def prefixEnd_7366640 : Nat := 4983230072969 + 3 ^ 40 * 7366640 * 2
def baseEnd_7366640 : Nat := 3782627128637163220821445

theorem tailTrace_7366640 : CollatzResearch.WordTrace tailWord_7366640 prefixEnd_7366640 3782627128637163220821445 := by
  unfold tailWord_7366640
  simp only [CollatzResearch.WordTrace]
  refine ⟨134341717015964438396452687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179122289354619251195270249 134341717015964438396452687)
  ·
    refine ⟨201512575523946657594679031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134341717015964438396452687 201512575523946657594679031)
    ·
      refine ⟨302268863285919986392018547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201512575523946657594679031 302268863285919986392018547)
      ·
        refine ⟨453403294928879979588027821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302268863285919986392018547 453403294928879979588027821)
        ·
          refine ⟨170026235598329992345510433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453403294928879979588027821 170026235598329992345510433)
          ·
            refine ⟨127519676698747494259132825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170026235598329992345510433 127519676698747494259132825)
            ·
              refine ⟨95639757524060620694349619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127519676698747494259132825 95639757524060620694349619)
              ·
                refine ⟨143459636286090931041524429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95639757524060620694349619 143459636286090931041524429)
                ·
                  refine ⟨53797363607284099140571661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143459636286090931041524429 53797363607284099140571661)
                  ·
                    refine ⟨20174011352731537177714373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53797363607284099140571661 20174011352731537177714373)
                    ·
                      refine ⟨3782627128637163220821445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20174011352731537177714373 3782627128637163220821445)
                      ·
                        rfl

theorem cell23_7366640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_7366640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366640 prefixEnd_7366640 := by exact prefixLift 7366640
  have htrace : WordTrace (prefixWord ++ tailWord_7366640) baseStart_7366640 baseEnd_7366640 := by
    simpa [prefixWord, tailWord_7366640, baseEnd_7366640] using wordTrace_append hprefix tailTrace_7366640
  have hstable : (prefixWord ++ tailWord_7366640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366640).length < 2 ^ (prefixWord ++ tailWord_7366640).sum := by decide
  have hdescent : baseEnd_7366640 < baseStart_7366640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366654 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7366654 : Nat := 118140960795 + 7366654 * 2 ^ 59
def prefixEnd_7366654 : Nat := 4983230072969 + 3 ^ 40 * 7366654 * 2
def baseEnd_7366654 : Nat := 1260878105788775388682127

theorem tailTrace_7366654 : CollatzResearch.WordTrace tailWord_7366654 prefixEnd_7366654 1260878105788775388682127 := by
  unfold tailWord_7366654
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585493081734769647989377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179122629769252104789276677 33585493081734769647989377)
  ·
    refine ⟨25189119811301077235992033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33585493081734769647989377 25189119811301077235992033)
    ·
      refine ⟨18891839858475807926994025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25189119811301077235992033 18891839858475807926994025)
      ·
        refine ⟨14168879893856855945245519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18891839858475807926994025 14168879893856855945245519)
        ·
          refine ⟨21253319840785283917868279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14168879893856855945245519 21253319840785283917868279)
          ·
            refine ⟨31879979761177925876802419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21253319840785283917868279 31879979761177925876802419)
            ·
              refine ⟨47819969641766888815203629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31879979761177925876802419 47819969641766888815203629)
              ·
                refine ⟨17932488615662583305701361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47819969641766888815203629 17932488615662583305701361)
                ·
                  refine ⟨13449366461746937479276021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17932488615662583305701361 13449366461746937479276021)
                  ·
                    refine ⟨1260878105788775388682127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13449366461746937479276021 1260878105788775388682127)
                    ·
                      rfl

theorem cell23_7366654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7366654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366654 prefixEnd_7366654 := by exact prefixLift 7366654
  have htrace : WordTrace (prefixWord ++ tailWord_7366654) baseStart_7366654 baseEnd_7366654 := by
    simpa [prefixWord, tailWord_7366654, baseEnd_7366654] using wordTrace_append hprefix tailTrace_7366654
  have hstable : (prefixWord ++ tailWord_7366654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366654).length < 2 ^ (prefixWord ++ tailWord_7366654).sum := by decide
  have hdescent : baseEnd_7366654 < baseStart_7366654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366700 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_7366700 : Nat := 118140960795 + 7366700 * 2 ^ 59
def prefixEnd_7366700 : Nat := 4983230072969 + 3 ^ 40 * 7366700 * 2
def baseEnd_7366700 : Nat := 3782657937476432986071169

theorem tailTrace_7366700 : CollatzResearch.WordTrace tailWord_7366700 prefixEnd_7366700 3782657937476432986071169 := by
  unfold tailWord_7366700
  simp only [CollatzResearch.WordTrace]
  refine ⟨134342811205855753520044777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179123748274474338026726369 134342811205855753520044777)
  ·
    refine ⟨100757108404391815140033583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134342811205855753520044777 100757108404391815140033583)
    ·
      refine ⟨151135662606587722710050375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100757108404391815140033583 151135662606587722710050375)
      ·
        refine ⟨226703493909881584065075563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151135662606587722710050375 226703493909881584065075563)
        ·
          refine ⟨340055240864822376097613345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226703493909881584065075563 340055240864822376097613345)
          ·
            refine ⟨255041430648616782073210009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340055240864822376097613345 255041430648616782073210009)
            ·
              refine ⟨191281072986462586554907507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255041430648616782073210009 191281072986462586554907507)
              ·
                refine ⟨286921609479693879832361261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191281072986462586554907507 286921609479693879832361261)
                ·
                  refine ⟨107595603554885204937135473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286921609479693879832361261 107595603554885204937135473)
                  ·
                    refine ⟨80696702666163903702851605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107595603554885204937135473 80696702666163903702851605)
                    ·
                      refine ⟨3782657937476432986071169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80696702666163903702851605 3782657937476432986071169)
                      ·
                        rfl

theorem cell23_7366700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_7366700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366700 prefixEnd_7366700 := by exact prefixLift 7366700
  have htrace : WordTrace (prefixWord ++ tailWord_7366700) baseStart_7366700 baseEnd_7366700 := by
    simpa [prefixWord, tailWord_7366700, baseEnd_7366700] using wordTrace_append hprefix tailTrace_7366700
  have hstable : (prefixWord ++ tailWord_7366700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366700).length < 2 ^ (prefixWord ++ tailWord_7366700).sum := by decide
  have hdescent : baseEnd_7366700 < baseStart_7366700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366708 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7366708 : Nat := 118140960795 + 7366708 * 2 ^ 59
def prefixEnd_7366708 : Nat := 4983230072969 + 3 ^ 40 * 7366708 * 2
def baseEnd_7366708 : Nat := 3782662045321668954771133

theorem tailTrace_7366708 : CollatzResearch.WordTrace tailWord_7366708 prefixEnd_7366708 3782662045321668954771133 := by
  unfold tailWord_7366708
  simp only [CollatzResearch.WordTrace]
  refine ⟨134342957097841262203190389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179123942797121682937587185 134342957097841262203190389)
  ·
    refine ⟨12594652227922618331549099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134342957097841262203190389 12594652227922618331549099)
    ·
      refine ⟨18891978341883927497323649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594652227922618331549099 18891978341883927497323649)
      ·
        refine ⟨14168983756412945622992737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18891978341883927497323649 14168983756412945622992737)
        ·
          refine ⟨10626737817309709217244553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14168983756412945622992737 10626737817309709217244553)
          ·
            refine ⟨7970053362982281912933415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10626737817309709217244553 7970053362982281912933415)
            ·
              refine ⟨11955080044473422869400123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7970053362982281912933415 11955080044473422869400123)
              ·
                refine ⟨17932620066710134304100185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11955080044473422869400123 17932620066710134304100185)
                ·
                  refine ⟨13449465050032600728075139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17932620066710134304100185 13449465050032600728075139)
                  ·
                    refine ⟨20174197575048901092112709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13449465050032600728075139 20174197575048901092112709)
                    ·
                      refine ⟨3782662045321668954771133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20174197575048901092112709 3782662045321668954771133)
                      ·
                        rfl

theorem cell23_7366708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7366708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366708 prefixEnd_7366708 := by exact prefixLift 7366708
  have htrace : WordTrace (prefixWord ++ tailWord_7366708) baseStart_7366708 baseEnd_7366708 := by
    simpa [prefixWord, tailWord_7366708, baseEnd_7366708] using wordTrace_append hprefix tailTrace_7366708
  have hstable : (prefixWord ++ tailWord_7366708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366708).length < 2 ^ (prefixWord ++ tailWord_7366708).sum := by decide
  have hdescent : baseEnd_7366708 < baseStart_7366708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366741 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7366741 : Nat := 118140960795 + 7366741 * 2 ^ 59
def prefixEnd_7366741 : Nat := 4983230072969 + 3 ^ 40 * 7366741 * 2
def baseEnd_7366741 : Nat := 3782678990183267325658481

theorem tailTrace_7366741 : CollatzResearch.WordTrace tailWord_7366741 prefixEnd_7366741 3782678990183267325658481 := by
  unfold tailWord_7366741
  simp only [CollatzResearch.WordTrace]
  refine ⟨268687117804562971042332077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179124745203041980694888051 268687117804562971042332077)
  ·
    refine ⟨100757669176711114140874529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268687117804562971042332077 100757669176711114140874529)
    ·
      refine ⟨75568251882533335605655897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100757669176711114140874529 75568251882533335605655897)
      ·
        refine ⟨56676188911900001704241923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75568251882533335605655897 56676188911900001704241923)
        ·
          refine ⟨85014283367850002556362885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56676188911900001704241923 85014283367850002556362885)
          ·
            refine ⟨15940178131471875479318041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85014283367850002556362885 15940178131471875479318041)
            ·
              refine ⟨11955133598603906609488531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15940178131471875479318041 11955133598603906609488531)
              ·
                refine ⟨17932700397905859914232797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11955133598603906609488531 17932700397905859914232797)
                ·
                  refine ⟨6724762649214697467837299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17932700397905859914232797 6724762649214697467837299)
                  ·
                    refine ⟨10087143973822046201755949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6724762649214697467837299 10087143973822046201755949)
                    ·
                      refine ⟨3782678990183267325658481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10087143973822046201755949 3782678990183267325658481)
                      ·
                        rfl

theorem cell23_7366741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7366741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366741 prefixEnd_7366741 := by exact prefixLift 7366741
  have htrace : WordTrace (prefixWord ++ tailWord_7366741) baseStart_7366741 baseEnd_7366741 := by
    simpa [prefixWord, tailWord_7366741, baseEnd_7366741] using wordTrace_append hprefix tailTrace_7366741
  have hstable : (prefixWord ++ tailWord_7366741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366741).length < 2 ^ (prefixWord ++ tailWord_7366741).sum := by decide
  have hdescent : baseEnd_7366741 < baseStart_7366741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366764 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_7366764 : Nat := 118140960795 + 7366764 * 2 ^ 59
def prefixEnd_7366764 : Nat := 4983230072969 + 3 ^ 40 * 7366764 * 2
def baseEnd_7366764 : Nat := 3782690800238320735670875

theorem tailTrace_7366764 : CollatzResearch.WordTrace tailWord_7366764 prefixEnd_7366764 3782690800238320735670875 := by
  unfold tailWord_7366764
  simp only [CollatzResearch.WordTrace]
  refine ⟨134343978341739822985209673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179125304455653097313612897 134343978341739822985209673)
  ·
    refine ⟨100757983756304867238907255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134343978341739822985209673 100757983756304867238907255)
    ·
      refine ⟨151136975634457300858360883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100757983756304867238907255 151136975634457300858360883)
      ·
        refine ⟨226705463451685951287541325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151136975634457300858360883 226705463451685951287541325)
        ·
          refine ⟨85014548794382231732827997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226705463451685951287541325 85014548794382231732827997)
          ·
            refine ⟨31880455797893336899810499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85014548794382231732827997 31880455797893336899810499)
            ·
              refine ⟨47820683696840005349715749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31880455797893336899810499 47820683696840005349715749)
              ·
                refine ⟨8966378193157501003071703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47820683696840005349715749 8966378193157501003071703)
                ·
                  refine ⟨13449567289736251504607555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966378193157501003071703 13449567289736251504607555)
                  ·
                    refine ⟨20174350934604377256911333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13449567289736251504607555 20174350934604377256911333)
                    ·
                      refine ⟨3782690800238320735670875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20174350934604377256911333 3782690800238320735670875)
                      ·
                        rfl

theorem cell23_7366764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_7366764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366764 prefixEnd_7366764 := by exact prefixLift 7366764
  have htrace : WordTrace (prefixWord ++ tailWord_7366764) baseStart_7366764 baseEnd_7366764 := by
    simpa [prefixWord, tailWord_7366764, baseEnd_7366764] using wordTrace_append hprefix tailTrace_7366764
  have hstable : (prefixWord ++ tailWord_7366764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366764).length < 2 ^ (prefixWord ++ tailWord_7366764).sum := by decide
  have hdescent : baseEnd_7366764 < baseStart_7366764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366787 : List Nat := [1, 1, 1, 3, 3, 5, 9]
def baseStart_7366787 : Nat := 118140960795 + 7366787 * 2 ^ 59
def prefixEnd_7366787 : Nat := 4983230072969 + 3 ^ 40 * 7366787 * 2
def baseEnd_7366787 : Nat := 46700032225844125255349

theorem tailTrace_7366787 : CollatzResearch.WordTrace tailWord_7366787 prefixEnd_7366787 46700032225844125255349 := by
  unfold tailWord_7366787
  simp only [CollatzResearch.WordTrace]
  refine ⟨268688795562396320898506615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179125863708264213932337743 268688795562396320898506615)
  ·
    refine ⟨403033193343594481347759923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268688795562396320898506615 403033193343594481347759923)
    ·
      refine ⟨604549790015391722021639885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403033193343594481347759923 604549790015391722021639885)
      ·
        refine ⟨226706171255771895758114957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604549790015391722021639885 226706171255771895758114957)
        ·
          refine ⟨85014814220914460909293109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226706171255771895758114957 85014814220914460909293109)
          ·
            refine ⟨7970138833210730710246229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85014814220914460909293109 7970138833210730710246229)
            ·
              refine ⟨46700032225844125255349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7970138833210730710246229 46700032225844125255349)
              ·
                rfl

theorem cell23_7366787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 9].length) (baseStart_7366787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366787 prefixEnd_7366787 := by exact prefixLift 7366787
  have htrace : WordTrace (prefixWord ++ tailWord_7366787) baseStart_7366787 baseEnd_7366787 := by
    simpa [prefixWord, tailWord_7366787, baseEnd_7366787] using wordTrace_append hprefix tailTrace_7366787
  have hstable : (prefixWord ++ tailWord_7366787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366787).length < 2 ^ (prefixWord ++ tailWord_7366787).sum := by decide
  have hdescent : baseEnd_7366787 < baseStart_7366787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366818 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7366818 : Nat := 118140960795 + 7366818 * 2 ^ 59
def prefixEnd_7366818 : Nat := 4983230072969 + 3 ^ 40 * 7366818 * 2
def baseEnd_7366818 : Nat := 3782718528193663524395627

theorem tailTrace_7366818 : CollatzResearch.WordTrace tailWord_7366818 prefixEnd_7366818 3782718528193663524395627 := by
  unfold tailWord_7366818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67172481556321003298221277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179126617483522675461923405 67172481556321003298221277)
  ·
    refine ⟨25189680583620376236832979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67172481556321003298221277 25189680583620376236832979)
    ·
      refine ⟨37784520875430564355249469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25189680583620376236832979 37784520875430564355249469)
      ·
        refine ⟨14169195328286461633218551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37784520875430564355249469 14169195328286461633218551)
        ·
          refine ⟨21253792992429692449827827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14169195328286461633218551 21253792992429692449827827)
          ·
            refine ⟨31880689488644538674741741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21253792992429692449827827 31880689488644538674741741)
            ·
              refine ⟨11955258558241702003028153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31880689488644538674741741 11955258558241702003028153)
              ·
                refine ⟨8966443918681276502271115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11955258558241702003028153 8966443918681276502271115)
                ·
                  refine ⟨13449665878021914753406673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966443918681276502271115 13449665878021914753406673)
                  ·
                    refine ⟨10087249408516436065055005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13449665878021914753406673 10087249408516436065055005)
                    ·
                      refine ⟨3782718528193663524395627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10087249408516436065055005 3782718528193663524395627)
                      ·
                        rfl

theorem cell23_7366818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7366818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366818 prefixEnd_7366818 := by exact prefixLift 7366818
  have htrace : WordTrace (prefixWord ++ tailWord_7366818) baseStart_7366818 baseEnd_7366818 := by
    simpa [prefixWord, tailWord_7366818, baseEnd_7366818] using wordTrace_append hprefix tailTrace_7366818
  have hstable : (prefixWord ++ tailWord_7366818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366818).length < 2 ^ (prefixWord ++ tailWord_7366818).sum := by decide
  have hdescent : baseEnd_7366818 < baseStart_7366818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366847 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 6]
def baseStart_7366847 : Nat := 118140960795 + 7366847 * 2 ^ 59
def prefixEnd_7366847 : Nat := 4983230072969 + 3 ^ 40 * 7366847 * 2
def baseEnd_7366847 : Nat := 1260911139710881303644331

theorem tailTrace_7366847 : CollatzResearch.WordTrace tailWord_7366847 prefixEnd_7366847 1260911139710881303644331 := by
  unfold tailWord_7366847
  simp only [CollatzResearch.WordTrace]
  refine ⟨268690983942178951145690795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179127322628119300763793863 268690983942178951145690795)
  ·
    refine ⟨403036475913268426718536193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268690983942178951145690795 403036475913268426718536193)
    ·
      refine ⟨302277356934951320038902145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403036475913268426718536193 302277356934951320038902145)
      ·
        refine ⟨226708017701213490029176609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302277356934951320038902145 226708017701213490029176609)
        ·
          refine ⟨170031013275910117521882457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226708017701213490029176609 170031013275910117521882457)
          ·
            refine ⟨127523259956932588141411843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170031013275910117521882457 127523259956932588141411843)
            ·
              refine ⟨191284889935398882212117765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127523259956932588141411843 191284889935398882212117765)
              ·
                refine ⟨35865916862887290414772081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191284889935398882212117765 35865916862887290414772081)
                ·
                  refine ⟨26899437647165467811079061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35865916862887290414772081 26899437647165467811079061)
                  ·
                    refine ⟨1260911139710881303644331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26899437647165467811079061 1260911139710881303644331)
                    ·
                      rfl

theorem cell23_7366847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_7366847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366847 prefixEnd_7366847 := by exact prefixLift 7366847
  have htrace : WordTrace (prefixWord ++ tailWord_7366847) baseStart_7366847 baseEnd_7366847 := by
    simpa [prefixWord, tailWord_7366847, baseEnd_7366847] using wordTrace_append hprefix tailTrace_7366847
  have hstable : (prefixWord ++ tailWord_7366847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366847).length < 2 ^ (prefixWord ++ tailWord_7366847).sum := by decide
  have hdescent : baseEnd_7366847 < baseStart_7366847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366848 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_7366848 : Nat := 118140960795 + 7366848 * 2 ^ 59
def prefixEnd_7366848 : Nat := 4983230072969 + 3 ^ 40 * 7366848 * 2
def baseEnd_7366848 : Nat := 3782733932613298407020489

theorem tailTrace_7366848 : CollatzResearch.WordTrace tailWord_7366848 prefixEnd_7366848 3782733932613298407020489 := by
  unfold tailWord_7366848
  simp only [CollatzResearch.WordTrace]
  refine ⟨134345510207587664158238599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179127346943450218877651465 134345510207587664158238599)
  ·
    refine ⟨201518265311381496237357899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134345510207587664158238599 201518265311381496237357899)
    ·
      refine ⟨302277397967072244356036849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201518265311381496237357899 302277397967072244356036849)
      ·
        refine ⟨226708048475304183267027637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302277397967072244356036849 226708048475304183267027637)
        ·
          refine ⟨21253879544559767181283841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226708048475304183267027637 21253879544559767181283841)
          ·
            refine ⟨15940409658419825385962881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21253879544559767181283841 15940409658419825385962881)
            ·
              refine ⟨11955307243814869039472161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15940409658419825385962881 11955307243814869039472161)
              ·
                refine ⟨8966480432861151779604121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11955307243814869039472161 8966480432861151779604121)
                ·
                  refine ⟨6724860324645863834703091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8966480432861151779604121 6724860324645863834703091)
                  ·
                    refine ⟨10087290486968795752054637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6724860324645863834703091 10087290486968795752054637)
                    ·
                      refine ⟨3782733932613298407020489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10087290486968795752054637 3782733932613298407020489)
                      ·
                        rfl

theorem cell23_7366848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_7366848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366848 prefixEnd_7366848 := by exact prefixLift 7366848
  have htrace : WordTrace (prefixWord ++ tailWord_7366848) baseStart_7366848 baseEnd_7366848 := by
    simpa [prefixWord, tailWord_7366848, baseEnd_7366848] using wordTrace_append hprefix tailTrace_7366848
  have hstable : (prefixWord ++ tailWord_7366848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366848).length < 2 ^ (prefixWord ++ tailWord_7366848).sum := by decide
  have hdescent : baseEnd_7366848 < baseStart_7366848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366857 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_7366857 : Nat := 118140960795 + 7366857 * 2 ^ 59
def prefixEnd_7366857 : Nat := 4983230072969 + 3 ^ 40 * 7366857 * 2
def baseEnd_7366857 : Nat := 3782738553939188871807947

theorem tailTrace_7366857 : CollatzResearch.WordTrace tailWord_7366857 prefixEnd_7366857 3782738553939188871807947 := by
  unfold tailWord_7366857
  simp only [CollatzResearch.WordTrace]
  refine ⟨268691348672142722853554825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179127565781428481902369883 268691348672142722853554825)
  ·
    refine ⟨201518511504107042140166119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268691348672142722853554825 201518511504107042140166119)
    ·
      refine ⟨302277767256160563210249179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201518511504107042140166119 302277767256160563210249179)
      ·
        refine ⟨453416650884240844815373769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302277767256160563210249179 453416650884240844815373769)
        ·
          refine ⟨340062488163180633611530327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453416650884240844815373769 340062488163180633611530327)
          ·
            refine ⟨510093732244770950417295491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340062488163180633611530327 510093732244770950417295491)
            ·
              refine ⟨765140598367156425625943237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510093732244770950417295491 765140598367156425625943237)
              ·
                refine ⟨143463862193841829804864357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765140598367156425625943237 143463862193841829804864357)
                ·
                  refine ⟨26899474161345343088412067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143463862193841829804864357 26899474161345343088412067)
                  ·
                    refine ⟨40349211242018014632618101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26899474161345343088412067 40349211242018014632618101)
                    ·
                      refine ⟨3782738553939188871807947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40349211242018014632618101 3782738553939188871807947)
                      ·
                        rfl

theorem cell23_7366857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_7366857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366857 prefixEnd_7366857 := by exact prefixLift 7366857
  have htrace : WordTrace (prefixWord ++ tailWord_7366857) baseStart_7366857 baseEnd_7366857 := by
    simpa [prefixWord, tailWord_7366857, baseEnd_7366857] using wordTrace_append hprefix tailTrace_7366857
  have hstable : (prefixWord ++ tailWord_7366857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366857).length < 2 ^ (prefixWord ++ tailWord_7366857).sum := by decide
  have hdescent : baseEnd_7366857 < baseStart_7366857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7366871 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_7366871 : Nat := 118140960795 + 7366871 * 2 ^ 59
def prefixEnd_7366871 : Nat := 4983230072969 + 3 ^ 40 * 7366871 * 2
def baseEnd_7366871 : Nat := 3782745742668351817032883

theorem tailTrace_7366871 : CollatzResearch.WordTrace tailWord_7366871 prefixEnd_7366871 3782745742668351817032883 := by
  unfold tailWord_7366871
  simp only [CollatzResearch.WordTrace]
  refine ⟨268691859294092003244564467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179127906196061335496376311 268691859294092003244564467)
  ·
    refine ⟨403037788941138004866846701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268691859294092003244564467 403037788941138004866846701)
    ·
      refine ⟨151139170852926751825067513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403037788941138004866846701 151139170852926751825067513)
      ·
        refine ⟨113354378139695063868800635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151139170852926751825067513 113354378139695063868800635)
        ·
          refine ⟨170031567209542595803200953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113354378139695063868800635 170031567209542595803200953)
          ·
            refine ⟨127523675407156946852400715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170031567209542595803200953 127523675407156946852400715)
            ·
              refine ⟨191285513110735420278601073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127523675407156946852400715 191285513110735420278601073)
              ·
                refine ⟨143464134833051565208950805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191285513110735420278601073 143464134833051565208950805)
                ·
                  refine ⟨6724881320299292119169569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143464134833051565208950805 6724881320299292119169569)
                  ·
                    refine ⟨5043660990224469089377177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724881320299292119169569 5043660990224469089377177)
                    ·
                      refine ⟨3782745742668351817032883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043660990224469089377177 3782745742668351817032883)
                      ·
                        rfl

theorem cell23_7366871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_7366871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7366871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7366871 prefixEnd_7366871 := by exact prefixLift 7366871
  have htrace : WordTrace (prefixWord ++ tailWord_7366871) baseStart_7366871 baseEnd_7366871 := by
    simpa [prefixWord, tailWord_7366871, baseEnd_7366871] using wordTrace_append hprefix tailTrace_7366871
  have hstable : (prefixWord ++ tailWord_7366871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7366871).length < 2 ^ (prefixWord ++ tailWord_7366871).sum := by decide
  have hdescent : baseEnd_7366871 < baseStart_7366871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7366871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367018 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_7367018 : Nat := 118140960795 + 7367018 * 2 ^ 59
def prefixEnd_7367018 : Nat := 4983230072969 + 3 ^ 40 * 7367018 * 2
def baseEnd_7367018 : Nat := 420313469369395860210523

theorem tailTrace_7367018 : CollatzResearch.WordTrace tailWord_7367018 prefixEnd_7367018 420313469369395860210523 := by
  unfold tailWord_7367018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67174305206139861837541427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179131480549706298233443805 67174305206139861837541427)
  ·
    refine ⟨100761457809209792756312141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67174305206139861837541427 100761457809209792756312141)
    ·
      refine ⟨37785546678453672283617053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100761457809209792756312141 37785546678453672283617053)
      ·
        refine ⟨14169580004420127106356395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37785546678453672283617053 14169580004420127106356395)
        ·
          refine ⟨21254370006630190659534593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14169580004420127106356395 21254370006630190659534593)
          ·
            refine ⟨15940777504972642994650945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21254370006630190659534593 15940777504972642994650945)
            ·
              refine ⟨11955583128729482245988209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15940777504972642994650945 11955583128729482245988209)
              ·
                refine ⟨8966687346547111684491157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11955583128729482245988209 8966687346547111684491157)
                ·
                  refine ⟨420313469369395860210523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8966687346547111684491157 420313469369395860210523)
                  ·
                    rfl

theorem cell23_7367018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_7367018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367018 prefixEnd_7367018 := by exact prefixLift 7367018
  have htrace : WordTrace (prefixWord ++ tailWord_7367018) baseStart_7367018 baseEnd_7367018 := by
    simpa [prefixWord, tailWord_7367018, baseEnd_7367018] using wordTrace_append hprefix tailTrace_7367018
  have hstable : (prefixWord ++ tailWord_7367018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367018).length < 2 ^ (prefixWord ++ tailWord_7367018).sum := by decide
  have hdescent : baseEnd_7367018 < baseStart_7367018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367034 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_7367034 : Nat := 118140960795 + 7367034 * 2 ^ 59
def prefixEnd_7367034 : Nat := 4983230072969 + 3 ^ 40 * 7367034 * 2
def baseEnd_7367034 : Nat := 3782829440015034679294633

theorem tailTrace_7367034 : CollatzResearch.WordTrace tailWord_7367034 prefixEnd_7367034 3782829440015034679294633 := by
  unfold tailWord_7367034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67174451098125370520687039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179131869595000988055165437 67174451098125370520687039)
  ·
    refine ⟨100761676647188055781030559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67174451098125370520687039 100761676647188055781030559)
    ·
      refine ⟨151142514970782083671545839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100761676647188055781030559 151142514970782083671545839)
      ·
        refine ⟨226713772456173125507318759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151142514970782083671545839 226713772456173125507318759)
        ·
          refine ⟨340070658684259688260978139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226713772456173125507318759 340070658684259688260978139)
          ·
            refine ⟨510105988026389532391467209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340070658684259688260978139 510105988026389532391467209)
            ·
              refine ⟨382579491019792149293600407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510105988026389532391467209 382579491019792149293600407)
              ·
                refine ⟨573869236529688223940400611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382579491019792149293600407 573869236529688223940400611)
                ·
                  refine ⟨860803854794532335910600917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 573869236529688223940400611 860803854794532335910600917)
                  ·
                    refine ⟨20175090346746851622904709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 860803854794532335910600917 20175090346746851622904709)
                    ·
                      refine ⟨3782829440015034679294633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20175090346746851622904709 3782829440015034679294633)
                      ·
                        rfl

theorem cell23_7367034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_7367034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367034 prefixEnd_7367034 := by exact prefixLift 7367034
  have htrace : WordTrace (prefixWord ++ tailWord_7367034) baseStart_7367034 baseEnd_7367034 := by
    simpa [prefixWord, tailWord_7367034, baseEnd_7367034] using wordTrace_append hprefix tailTrace_7367034
  have hstable : (prefixWord ++ tailWord_7367034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367034).length < 2 ^ (prefixWord ++ tailWord_7367034).sum := by decide
  have hdescent : baseEnd_7367034 < baseStart_7367034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367051 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4]
def baseStart_7367051 : Nat := 118140960795 + 7367051 * 2 ^ 59
def prefixEnd_7367051 : Nat := 4983230072969 + 3 ^ 40 * 7367051 * 2
def baseEnd_7367051 : Nat := 3782838169186161112782055

theorem tailTrace_7367051 : CollatzResearch.WordTrace tailWord_7367051 prefixEnd_7367051 3782838169186161112782055 := by
  unfold tailWord_7367051
  simp only [CollatzResearch.WordTrace]
  refine ⟨268698424433439893986117007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179132282955626595990744671 268698424433439893986117007)
  ·
    refine ⟨403047636650159840979175511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268698424433439893986117007 403047636650159840979175511)
    ·
      refine ⟨604571454975239761468763267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403047636650159840979175511 604571454975239761468763267)
      ·
        refine ⟨906857182462859642203144901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604571454975239761468763267 906857182462859642203144901)
        ·
          refine ⟨170035721711786182913089669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 906857182462859642203144901 170035721711786182913089669)
          ·
            refine ⟨31881697820959909296204313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170035721711786182913089669 31881697820959909296204313)
            ·
              refine ⟨23911273365719931972153235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31881697820959909296204313 23911273365719931972153235)
              ·
                refine ⟨35866910048579897958229853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23911273365719931972153235 35866910048579897958229853)
                ·
                  refine ⟨13450091268217461734336195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35866910048579897958229853 13450091268217461734336195)
                  ·
                    refine ⟨20175136902326192601504293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13450091268217461734336195 20175136902326192601504293)
                    ·
                      refine ⟨3782838169186161112782055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20175136902326192601504293 3782838169186161112782055)
                      ·
                        rfl

theorem cell23_7367051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_7367051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367051 prefixEnd_7367051 := by exact prefixLift 7367051
  have htrace : WordTrace (prefixWord ++ tailWord_7367051) baseStart_7367051 baseEnd_7367051 := by
    simpa [prefixWord, tailWord_7367051, baseEnd_7367051] using wordTrace_append hprefix tailTrace_7367051
  have hstable : (prefixWord ++ tailWord_7367051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367051).length < 2 ^ (prefixWord ++ tailWord_7367051).sum := by decide
  have hdescent : baseEnd_7367051 < baseStart_7367051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367061 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_7367061 : Nat := 118140960795 + 7367061 * 2 ^ 59
def prefixEnd_7367061 : Nat := 4983230072969 + 3 ^ 40 * 7367061 * 2
def baseEnd_7367061 : Nat := 1260947767997568691219003

theorem tailTrace_7367061 : CollatzResearch.WordTrace tailWord_7367061 prefixEnd_7367061 1260947767997568691219003 := by
  unfold tailWord_7367061
  simp only [CollatzResearch.WordTrace]
  refine ⟨268698789163403665693981037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179132526108935777129320691 268698789163403665693981037)
  ·
    refine ⟨100762045936276374635242889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268698789163403665693981037 100762045936276374635242889)
    ·
      refine ⟨75571534452207280976432167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100762045936276374635242889 75571534452207280976432167)
      ·
        refine ⟨113357301678310921464648251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75571534452207280976432167 113357301678310921464648251)
        ·
          refine ⟨170035952517466382196972377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113357301678310921464648251 170035952517466382196972377)
          ·
            refine ⟨127526964388099786647729283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170035952517466382196972377 127526964388099786647729283)
            ·
              refine ⟨191290446582149679971593925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127526964388099786647729283 191290446582149679971593925)
              ·
                refine ⟨35866958734153064994673861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191290446582149679971593925 35866958734153064994673861)
                ·
                  refine ⟨6725054762653699686501349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35866958734153064994673861 6725054762653699686501349)
                  ·
                    refine ⟨1260947767997568691219003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725054762653699686501349 1260947767997568691219003)
                    ·
                      rfl

theorem cell23_7367061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_7367061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367061 prefixEnd_7367061 := by exact prefixLift 7367061
  have htrace : WordTrace (prefixWord ++ tailWord_7367061) baseStart_7367061 baseEnd_7367061 := by
    simpa [prefixWord, tailWord_7367061, baseEnd_7367061] using wordTrace_append hprefix tailTrace_7367061
  have hstable : (prefixWord ++ tailWord_7367061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367061).length < 2 ^ (prefixWord ++ tailWord_7367061).sum := by decide
  have hdescent : baseEnd_7367061 < baseStart_7367061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367071 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7367071 : Nat := 118140960795 + 7367071 * 2 ^ 59
def prefixEnd_7367071 : Nat := 4983230072969 + 3 ^ 40 * 7367071 * 2
def baseEnd_7367071 : Nat := 3782848438799251034531963

theorem tailTrace_7367071 : CollatzResearch.WordTrace tailWord_7367071 prefixEnd_7367071 3782848438799251034531963 := by
  unfold tailWord_7367071
  simp only [CollatzResearch.WordTrace]
  refine ⟨268699153893367437401845067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179132769262244958267896711 268699153893367437401845067)
  ·
    refine ⟨403048730840051156102767601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268699153893367437401845067 403048730840051156102767601)
    ·
      refine ⟨302286548130038367077075701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403048730840051156102767601 302286548130038367077075701)
      ·
        refine ⟨28339363887191096913475847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302286548130038367077075701 28339363887191096913475847)
        ·
          refine ⟨42509045830786645370213771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28339363887191096913475847 42509045830786645370213771)
          ·
            refine ⟨63763568746179968055320657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42509045830786645370213771 63763568746179968055320657)
            ·
              refine ⟨47822676559634976041490493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63763568746179968055320657 47822676559634976041490493)
              ·
                refine ⟨17933503709863116015558935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47822676559634976041490493 17933503709863116015558935)
                ·
                  refine ⟨26900255564794674023338403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17933503709863116015558935 26900255564794674023338403)
                  ·
                    refine ⟨40350383347192011035007605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26900255564794674023338403 40350383347192011035007605)
                    ·
                      refine ⟨3782848438799251034531963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40350383347192011035007605 3782848438799251034531963)
                      ·
                        rfl

theorem cell23_7367071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7367071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367071 prefixEnd_7367071 := by exact prefixLift 7367071
  have htrace : WordTrace (prefixWord ++ tailWord_7367071) baseStart_7367071 baseEnd_7367071 := by
    simpa [prefixWord, tailWord_7367071, baseEnd_7367071] using wordTrace_append hprefix tailTrace_7367071
  have hstable : (prefixWord ++ tailWord_7367071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367071).length < 2 ^ (prefixWord ++ tailWord_7367071).sum := by decide
  have hdescent : baseEnd_7367071 < baseStart_7367071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367084 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_7367084 : Nat := 118140960795 + 7367084 * 2 ^ 59
def prefixEnd_7367084 : Nat := 4983230072969 + 3 ^ 40 * 7367084 * 2
def baseEnd_7367084 : Nat := 3782855114047759483669403

theorem tailTrace_7367084 : CollatzResearch.WordTrace tailWord_7367084 prefixEnd_7367084 3782855114047759483669403 := by
  unfold tailWord_7367084
  simp only [CollatzResearch.WordTrace]
  refine ⟨134349814021160170311034153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179133085361546893748045537 134349814021160170311034153)
  ·
    refine ⟨100762360515870127733275615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134349814021160170311034153 100762360515870127733275615)
    ·
      refine ⟨151143540773805191599913423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100762360515870127733275615 151143540773805191599913423)
      ·
        refine ⟨226715311160707787399870135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151143540773805191599913423 226715311160707787399870135)
        ·
          refine ⟨340072966741061681099805203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226715311160707787399870135 340072966741061681099805203)
          ·
            refine ⟨510109450111592521649707805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340072966741061681099805203 510109450111592521649707805)
            ·
              refine ⟨191291043791847195618640427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510109450111592521649707805 191291043791847195618640427)
              ·
                refine ⟨286936565687770793427960641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191291043791847195618640427 286936565687770793427960641)
                ·
                  refine ⟨215202424265828095070970481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286936565687770793427960641 215202424265828095070970481)
                  ·
                    refine ⟨161401818199371071303227861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215202424265828095070970481 161401818199371071303227861)
                    ·
                      refine ⟨3782855114047759483669403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161401818199371071303227861 3782855114047759483669403)
                      ·
                        rfl

theorem cell23_7367084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_7367084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367084 prefixEnd_7367084 := by exact prefixLift 7367084
  have htrace : WordTrace (prefixWord ++ tailWord_7367084) baseStart_7367084 baseEnd_7367084 := by
    simpa [prefixWord, tailWord_7367084, baseEnd_7367084] using wordTrace_append hprefix tailTrace_7367084
  have hstable : (prefixWord ++ tailWord_7367084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367084).length < 2 ^ (prefixWord ++ tailWord_7367084).sum := by decide
  have hdescent : baseEnd_7367084 < baseStart_7367084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367095 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 2, 4]
def baseStart_7367095 : Nat := 118140960795 + 7367095 * 2 ^ 59
def prefixEnd_7367095 : Nat := 4983230072969 + 3 ^ 40 * 7367095 * 2
def baseEnd_7367095 : Nat := 1260953587444986313543951

theorem tailTrace_7367095 : CollatzResearch.WordTrace tailWord_7367095 prefixEnd_7367095 1260953587444986313543951 := by
  unfold tailWord_7367095
  simp only [CollatzResearch.WordTrace]
  refine ⟨268700029245280489500718739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179133352830186993000479159 268700029245280489500718739)
  ·
    refine ⟨403050043867920734251078109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268700029245280489500718739 403050043867920734251078109)
    ·
      refine ⟨151143766450470275344154291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403050043867920734251078109 151143766450470275344154291)
      ·
        refine ⟨226715649675705413016231437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151143766450470275344154291 226715649675705413016231437)
        ·
          refine ⟨85018368628389529881086789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226715649675705413016231437 85018368628389529881086789)
          ·
            refine ⟨15940944117823036852703773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85018368628389529881086789 15940944117823036852703773)
            ·
              refine ⟨5977854044183638819763915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15940944117823036852703773 5977854044183638819763915)
              ·
                refine ⟨8966781066275458229645873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977854044183638819763915 8966781066275458229645873)
                ·
                  refine ⟨6725085799706593672234405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8966781066275458229645873 6725085799706593672234405)
                  ·
                    refine ⟨1260953587444986313543951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725085799706593672234405 1260953587444986313543951)
                    ·
                      rfl

theorem cell23_7367095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_7367095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367095 prefixEnd_7367095 := by exact prefixLift 7367095
  have htrace : WordTrace (prefixWord ++ tailWord_7367095) baseStart_7367095 baseEnd_7367095 := by
    simpa [prefixWord, tailWord_7367095, baseEnd_7367095] using wordTrace_append hprefix tailTrace_7367095
  have hstable : (prefixWord ++ tailWord_7367095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367095).length < 2 ^ (prefixWord ++ tailWord_7367095).sum := by decide
  have hdescent : baseEnd_7367095 < baseStart_7367095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367108 : List Nat := [2, 3, 3, 2, 2, 1, 1, 9]
def baseStart_7367108 : Nat := 118140960795 + 7367108 * 2 ^ 59
def prefixEnd_7367108 : Nat := 4983230072969 + 3 ^ 40 * 7367108 * 2
def baseEnd_7367108 : Nat := 140106201391980273695159

theorem tailTrace_7367108 : CollatzResearch.WordTrace tailWord_7367108 prefixEnd_7367108 140106201391980273695159 := by
  unfold tailWord_7367108
  simp only [CollatzResearch.WordTrace]
  refine ⟨134350251697116696360470989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179133668929488928480627985 134350251697116696360470989)
  ·
    refine ⟨50381344386418761135176621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134350251697116696360470989 50381344386418761135176621)
    ·
      refine ⟨18893004144907035425691233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50381344386418761135176621 18893004144907035425691233)
      ·
        refine ⟨14169753108680276569268425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18893004144907035425691233 14169753108680276569268425)
        ·
          refine ⟨10627314831510207426951319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14169753108680276569268425 10627314831510207426951319)
          ·
            refine ⟨15940972247265311140426979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10627314831510207426951319 15940972247265311140426979)
            ·
              refine ⟨23911458370897966710640469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15940972247265311140426979 23911458370897966710640469)
              ·
                refine ⟨140106201391980273695159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23911458370897966710640469 140106201391980273695159)
                ·
                  rfl

theorem cell23_7367108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 9].length) (baseStart_7367108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367108 prefixEnd_7367108 := by exact prefixLift 7367108
  have htrace : WordTrace (prefixWord ++ tailWord_7367108) baseStart_7367108 baseEnd_7367108 := by
    simpa [prefixWord, tailWord_7367108, baseEnd_7367108] using wordTrace_append hprefix tailTrace_7367108
  have hstable : (prefixWord ++ tailWord_7367108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367108).length < 2 ^ (prefixWord ++ tailWord_7367108).sum := by decide
  have hdescent : baseEnd_7367108 < baseStart_7367108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367128 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_7367128 : Nat := 118140960795 + 7367128 * 2 ^ 59
def prefixEnd_7367128 : Nat := 4983230072969 + 3 ^ 40 * 7367128 * 2
def baseEnd_7367128 : Nat := 3782877707196557311519201

theorem tailTrace_7367128 : CollatzResearch.WordTrace tailWord_7367128 prefixEnd_7367128 3782877707196557311519201 := by
  unfold tailWord_7367128
  simp only [CollatzResearch.WordTrace]
  refine ⟨134350616427080468068335019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179134155236107290757780025 134350616427080468068335019)
  ·
    refine ⟨201525924640620702102502529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134350616427080468068335019 201525924640620702102502529)
    ·
      refine ⟨151144443480465526576876897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201525924640620702102502529 151144443480465526576876897)
      ·
        refine ⟨113358332610349144932657673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151144443480465526576876897 113358332610349144932657673)
        ·
          refine ⟨85018749457761858699493255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113358332610349144932657673 85018749457761858699493255)
          ·
            refine ⟨127528124186642788049239883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85018749457761858699493255 127528124186642788049239883)
            ·
              refine ⟨191292186279964182073859825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127528124186642788049239883 191292186279964182073859825)
              ·
                refine ⟨143469139709973136555394869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191292186279964182073859825 143469139709973136555394869)
                ·
                  refine ⟨13450231847809981552068269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143469139709973136555394869 13450231847809981552068269)
                  ·
                    refine ⟨5043836942928743082025601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13450231847809981552068269 5043836942928743082025601)
                    ·
                      refine ⟨3782877707196557311519201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043836942928743082025601 3782877707196557311519201)
                      ·
                        rfl

theorem cell23_7367128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_7367128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367128 prefixEnd_7367128 := by exact prefixLift 7367128
  have htrace : WordTrace (prefixWord ++ tailWord_7367128) baseStart_7367128 baseEnd_7367128 := by
    simpa [prefixWord, tailWord_7367128, baseEnd_7367128] using wordTrace_append hprefix tailTrace_7367128
  have hstable : (prefixWord ++ tailWord_7367128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367128).length < 2 ^ (prefixWord ++ tailWord_7367128).sum := by decide
  have hdescent : baseEnd_7367128 < baseStart_7367128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367161 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7367161 : Nat := 118140960795 + 7367161 * 2 ^ 59
def prefixEnd_7367161 : Nat := 4983230072969 + 3 ^ 40 * 7367161 * 2
def baseEnd_7367161 : Nat := 3782894652058155682406549

theorem tailTrace_7367161 : CollatzResearch.WordTrace tailWord_7367161 prefixEnd_7367161 3782894652058155682406549 := by
  unfold tailWord_7367161
  simp only [CollatzResearch.WordTrace]
  refine ⟨268702436463041382772621337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179134957642027588515080891 268702436463041382772621337)
  ·
    refine ⟨201526827347281037079466003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268702436463041382772621337 201526827347281037079466003)
    ·
      refine ⟨302290241020921555619199005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201526827347281037079466003 302290241020921555619199005)
      ·
        refine ⟨113358840382845583357199627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302290241020921555619199005 113358840382845583357199627)
        ·
          refine ⟨170038260574268375035799441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113358840382845583357199627 170038260574268375035799441)
          ·
            refine ⟨127528695430701281276849581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170038260574268375035799441 127528695430701281276849581)
            ·
              refine ⟨47823260786512980478818593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127528695430701281276849581 47823260786512980478818593)
              ·
                refine ⟨35867445589884735359113945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47823260786512980478818593 35867445589884735359113945)
                ·
                  refine ⟨26900584192413551519335459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35867445589884735359113945 26900584192413551519335459)
                  ·
                    refine ⟨40350876288620327279003189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26900584192413551519335459 40350876288620327279003189)
                    ·
                      refine ⟨3782894652058155682406549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40350876288620327279003189 3782894652058155682406549)
                      ·
                        rfl

theorem cell23_7367161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7367161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367161 prefixEnd_7367161 := by exact prefixLift 7367161
  have htrace : WordTrace (prefixWord ++ tailWord_7367161) baseStart_7367161 baseEnd_7367161 := by
    simpa [prefixWord, tailWord_7367161, baseEnd_7367161] using wordTrace_append hprefix tailTrace_7367161
  have hstable : (prefixWord ++ tailWord_7367161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367161).length < 2 ^ (prefixWord ++ tailWord_7367161).sum := by decide
  have hdescent : baseEnd_7367161 < baseStart_7367161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367192 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7367192 : Nat := 118140960795 + 7367192 * 2 ^ 59
def prefixEnd_7367192 : Nat := 4983230072969 + 3 ^ 40 * 7367192 * 2
def baseEnd_7367192 : Nat := 3782910569958445061118907

theorem tailTrace_7367192 : CollatzResearch.WordTrace tailWord_7367192 prefixEnd_7367192 3782910569958445061118907 := by
  unfold tailWord_7367192
  simp only [CollatzResearch.WordTrace]
  refine ⟨134351783562964537533499915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179135711417286050044666553 134351783562964537533499915)
  ·
    refine ⟨201527675344446806300249873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134351783562964537533499915 201527675344446806300249873)
    ·
      refine ⟨151145756508335104725187405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201527675344446806300249873 151145756508335104725187405)
      ·
        refine ⟨56679658690625664271945277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151145756508335104725187405 56679658690625664271945277)
        ·
          refine ⟨21254872008984624101979479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56679658690625664271945277 21254872008984624101979479)
          ·
            refine ⟨31882308013476936152969219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21254872008984624101979479 31882308013476936152969219)
            ·
              refine ⟨47823462020215404229453829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31882308013476936152969219 47823462020215404229453829)
              ·
                refine ⟨8966899128790388293022593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47823462020215404229453829 8966899128790388293022593)
                ·
                  refine ⟨6725174346592791219766945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8966899128790388293022593 6725174346592791219766945)
                  ·
                    refine ⟨5043880759944593414825209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725174346592791219766945 5043880759944593414825209)
                    ·
                      refine ⟨3782910569958445061118907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043880759944593414825209 3782910569958445061118907)
                      ·
                        rfl

theorem cell23_7367192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7367192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367192 prefixEnd_7367192 := by exact prefixLift 7367192
  have htrace : WordTrace (prefixWord ++ tailWord_7367192) baseStart_7367192 baseEnd_7367192 := by
    simpa [prefixWord, tailWord_7367192, baseEnd_7367192] using wordTrace_append hprefix tailTrace_7367192
  have hstable : (prefixWord ++ tailWord_7367192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367192).length < 2 ^ (prefixWord ++ tailWord_7367192).sum := by decide
  have hdescent : baseEnd_7367192 < baseStart_7367192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367211 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 4, 5]
def baseStart_7367211 : Nat := 118140960795 + 7367211 * 2 ^ 59
def prefixEnd_7367211 : Nat := 4983230072969 + 3 ^ 40 * 7367211 * 2
def baseEnd_7367211 : Nat := 1260973442030293495593773

theorem tailTrace_7367211 : CollatzResearch.WordTrace tailWord_7367211 prefixEnd_7367211 1260973442030293495593773 := by
  unfold tailWord_7367211
  simp only [CollatzResearch.WordTrace]
  refine ⟨268704260112860241311941487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179136173408573494207960991 268704260112860241311941487)
  ·
    refine ⟨403056390169290361967912231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268704260112860241311941487 403056390169290361967912231)
    ·
      refine ⟨604584585253935542951868347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403056390169290361967912231 604584585253935542951868347)
      ·
        refine ⟨906876877880903314427802521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604584585253935542951868347 906876877880903314427802521)
        ·
          refine ⟨680157658410677485820851891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906876877880903314427802521 680157658410677485820851891)
          ·
            refine ⟨1020236487616016228731277837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680157658410677485820851891 1020236487616016228731277837)
            ·
              refine ⟨382588682856006085774229189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1020236487616016228731277837 382588682856006085774229189)
              ·
                refine ⟨71735378035501141082667973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382588682856006085774229189 71735378035501141082667973)
                ·
                  refine ⟨13450383381656463953000245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71735378035501141082667973 13450383381656463953000245)
                  ·
                    refine ⟨1260973442030293495593773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13450383381656463953000245 1260973442030293495593773)
                    ·
                      rfl

theorem cell23_7367211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].length) (baseStart_7367211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367211 prefixEnd_7367211 := by exact prefixLift 7367211
  have htrace : WordTrace (prefixWord ++ tailWord_7367211) baseStart_7367211 baseEnd_7367211 := by
    simpa [prefixWord, tailWord_7367211, baseEnd_7367211] using wordTrace_append hprefix tailTrace_7367211
  have hstable : (prefixWord ++ tailWord_7367211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367211).length < 2 ^ (prefixWord ++ tailWord_7367211).sum := by decide
  have hdescent : baseEnd_7367211 < baseStart_7367211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367228 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7367228 : Nat := 118140960795 + 7367228 * 2 ^ 59
def prefixEnd_7367228 : Nat := 4983230072969 + 3 ^ 40 * 7367228 * 2
def baseEnd_7367228 : Nat := 1260976351754002306756247

theorem tailTrace_7367228 : CollatzResearch.WordTrace tailWord_7367228 prefixEnd_7367228 1260976351754002306756247 := by
  unfold tailWord_7367228
  simp only [CollatzResearch.WordTrace]
  refine ⟨134352440076899326607655169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179136586769199102143540225 134352440076899326607655169)
  ·
    refine ⟨100764330057674494955741377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134352440076899326607655169 100764330057674494955741377)
    ·
      refine ⟨75573247543255871216806033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100764330057674494955741377 75573247543255871216806033)
      ·
        refine ⟨56679935657441903412604525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75573247543255871216806033 56679935657441903412604525)
        ·
          refine ⟨21254975871540713779726697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56679935657441903412604525 21254975871540713779726697)
          ·
            refine ⟨15941231903655535334795023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21254975871540713779726697 15941231903655535334795023)
            ·
              refine ⟨23911847855483303002192535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941231903655535334795023 23911847855483303002192535)
              ·
                refine ⟨35867771783224954503288803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23911847855483303002192535 35867771783224954503288803)
                ·
                  refine ⟨53801657674837431754933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35867771783224954503288803 53801657674837431754933205)
                  ·
                    refine ⟨1260976351754002306756247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53801657674837431754933205 1260976351754002306756247)
                    ·
                      rfl

theorem cell23_7367228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7367228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367228 prefixEnd_7367228 := by exact prefixLift 7367228
  have htrace : WordTrace (prefixWord ++ tailWord_7367228) baseStart_7367228 baseEnd_7367228 := by
    simpa [prefixWord, tailWord_7367228, baseEnd_7367228] using wordTrace_append hprefix tailTrace_7367228
  have hstable : (prefixWord ++ tailWord_7367228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367228).length < 2 ^ (prefixWord ++ tailWord_7367228).sum := by decide
  have hdescent : baseEnd_7367228 < baseStart_7367228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367265 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_7367265 : Nat := 118140960795 + 7367265 * 2 ^ 59
def prefixEnd_7367265 : Nat := 4983230072969 + 3 ^ 40 * 7367265 * 2
def baseEnd_7367265 : Nat := 3782948054046223275506071

theorem tailTrace_7367265 : CollatzResearch.WordTrace tailWord_7367265 prefixEnd_7367265 3782948054046223275506071 := by
  unfold tailWord_7367265
  simp only [CollatzResearch.WordTrace]
  refine ⟨268706229654664608534407249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179137486436443072356271499 268706229654664608534407249)
  ·
    refine ⟨201529672240998456400805437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268706229654664608534407249 201529672240998456400805437)
    ·
      refine ⟨75573627090374421150302039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201529672240998456400805437 75573627090374421150302039)
      ·
        refine ⟨113360440635561631725453059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75573627090374421150302039 113360440635561631725453059)
        ·
          refine ⟨170040660953342447588179589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113360440635561631725453059 170040660953342447588179589)
          ·
            refine ⟨31882623928751708922783673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170040660953342447588179589 31882623928751708922783673)
            ·
              refine ⟨23911967946563781692087755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31882623928751708922783673 23911967946563781692087755)
              ·
                refine ⟨35867951919845672538131633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23911967946563781692087755 35867951919845672538131633)
                ·
                  refine ⟨26900963939884254403598725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35867951919845672538131633 26900963939884254403598725)
                  ·
                    refine ⟨5043930738728297700674761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26900963939884254403598725 5043930738728297700674761)
                    ·
                      refine ⟨3782948054046223275506071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043930738728297700674761 3782948054046223275506071)
                      ·
                        rfl

theorem cell23_7367265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_7367265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367265 prefixEnd_7367265 := by exact prefixLift 7367265
  have htrace : WordTrace (prefixWord ++ tailWord_7367265) baseStart_7367265 baseEnd_7367265 := by
    simpa [prefixWord, tailWord_7367265, baseEnd_7367265] using wordTrace_append hprefix tailTrace_7367265
  have hstable : (prefixWord ++ tailWord_7367265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367265).length < 2 ^ (prefixWord ++ tailWord_7367265).sum := by decide
  have hdescent : baseEnd_7367265 < baseStart_7367265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367268 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_7367268 : Nat := 118140960795 + 7367268 * 2 ^ 59
def prefixEnd_7367268 : Nat := 4983230072969 + 3 ^ 40 * 7367268 * 2
def baseEnd_7367268 : Nat := 3782949594488186763768557

theorem tailTrace_7367268 : CollatzResearch.WordTrace tailWord_7367268 prefixEnd_7367268 3782949594488186763768557 := by
  unfold tailWord_7367268
  simp only [CollatzResearch.WordTrace]
  refine ⟨134353169536826870023383229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179137559382435826697844305 134353169536826870023383229)
  ·
    refine ⟨50382438576310076258768711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134353169536826870023383229 50382438576310076258768711)
    ·
      refine ⟨75573657864465114388153067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50382438576310076258768711 75573657864465114388153067)
      ·
        refine ⟨113360486796697671582229601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75573657864465114388153067 113360486796697671582229601)
        ·
          refine ⟨85020365097523253686672201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113360486796697671582229601 85020365097523253686672201)
          ·
            refine ⟨63765273823142440265004151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85020365097523253686672201 63765273823142440265004151)
            ·
              refine ⟨95647910734713660397506227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63765273823142440265004151 95647910734713660397506227)
              ·
                refine ⟨143471866102070490596259341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95647910734713660397506227 143471866102070490596259341)
                ·
                  refine ⟨53801949788276433973597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143471866102070490596259341 53801949788276433973597253)
                  ·
                    refine ⟨10087865585301831370049485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53801949788276433973597253 10087865585301831370049485)
                    ·
                      refine ⟨3782949594488186763768557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10087865585301831370049485 3782949594488186763768557)
                      ·
                        rfl

theorem cell23_7367268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_7367268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367268 prefixEnd_7367268 := by exact prefixLift 7367268
  have htrace : WordTrace (prefixWord ++ tailWord_7367268) baseStart_7367268 baseEnd_7367268 := by
    simpa [prefixWord, tailWord_7367268, baseEnd_7367268] using wordTrace_append hprefix tailTrace_7367268
  have hstable : (prefixWord ++ tailWord_7367268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367268).length < 2 ^ (prefixWord ++ tailWord_7367268).sum := by decide
  have hdescent : baseEnd_7367268 < baseStart_7367268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367281 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7367281 : Nat := 118140960795 + 7367281 * 2 ^ 59
def prefixEnd_7367281 : Nat := 4983230072969 + 3 ^ 40 * 7367281 * 2
def baseEnd_7367281 : Nat := 3782956269736695212905997

theorem tailTrace_7367281 : CollatzResearch.WordTrace tailWord_7367281 prefixEnd_7367281 3782956269736695212905997 := by
  unfold tailWord_7367281
  simp only [CollatzResearch.WordTrace]
  refine ⟨268706813222606643266989697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179137875481737762177993131 268706813222606643266989697)
  ·
    refine ⟨201530109916954982450242273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268706813222606643266989697 201530109916954982450242273)
    ·
      refine ⟨151147582437716236837681705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201530109916954982450242273 151147582437716236837681705)
      ·
        refine ⟨113360686828287177628261279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151147582437716236837681705 113360686828287177628261279)
        ·
          refine ⟨170041030242430766442391919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113360686828287177628261279 170041030242430766442391919)
          ·
            refine ⟨255061545363646149663587879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170041030242430766442391919 255061545363646149663587879)
            ·
              refine ⟨382592318045469224495381819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255061545363646149663587879 382592318045469224495381819)
              ·
                refine ⟨573888477068203836743072729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382592318045469224495381819 573888477068203836743072729)
                ·
                  refine ⟨430416357801152877557304547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573888477068203836743072729 430416357801152877557304547)
                  ·
                    refine ⟨645624536701729316335956821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 430416357801152877557304547 645624536701729316335956821)
                    ·
                      refine ⟨3782956269736695212905997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 645624536701729316335956821 3782956269736695212905997)
                      ·
                        rfl

theorem cell23_7367281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7367281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367281 prefixEnd_7367281 := by exact prefixLift 7367281
  have htrace : WordTrace (prefixWord ++ tailWord_7367281) baseStart_7367281 baseEnd_7367281 := by
    simpa [prefixWord, tailWord_7367281, baseEnd_7367281] using wordTrace_append hprefix tailTrace_7367281
  have hstable : (prefixWord ++ tailWord_7367281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367281).length < 2 ^ (prefixWord ++ tailWord_7367281).sum := by decide
  have hdescent : baseEnd_7367281 < baseStart_7367281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367291 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_7367291 : Nat := 118140960795 + 7367291 * 2 ^ 59
def prefixEnd_7367291 : Nat := 4983230072969 + 3 ^ 40 * 7367291 * 2
def baseEnd_7367291 : Nat := 3782961404543240173780951

theorem tailTrace_7367291 : CollatzResearch.WordTrace tailWord_7367291 prefixEnd_7367291 3782961404543240173780951 := by
  unfold tailWord_7367291
  simp only [CollatzResearch.WordTrace]
  refine ⟨268707177952570414974853727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179138118635046943316569151 268707177952570414974853727)
  ·
    refine ⟨403060766928855622462280591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268707177952570414974853727 403060766928855622462280591)
    ·
      refine ⟨604591150393283433693420887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403060766928855622462280591 604591150393283433693420887)
      ·
        refine ⟨906886725589925150540131331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604591150393283433693420887 906886725589925150540131331)
        ·
          refine ⟨1360330088384887725810196997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906886725589925150540131331 1360330088384887725810196997)
          ·
            refine ⟨255061891572166448589411937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1360330088384887725810196997 255061891572166448589411937)
            ·
              refine ⟨191296418679124836442058953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255061891572166448589411937 191296418679124836442058953)
              ·
                refine ⟨143472314009343627331544215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191296418679124836442058953 143472314009343627331544215)
                ·
                  refine ⟨215208471014015440997316323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143472314009343627331544215 215208471014015440997316323)
                  ·
                    refine ⟨322812706521023161495974485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 215208471014015440997316323 322812706521023161495974485)
                    ·
                      refine ⟨3782961404543240173780951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 322812706521023161495974485 3782961404543240173780951)
                      ·
                        rfl

theorem cell23_7367291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_7367291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367291 prefixEnd_7367291 := by exact prefixLift 7367291
  have htrace : WordTrace (prefixWord ++ tailWord_7367291) baseStart_7367291 baseEnd_7367291 := by
    simpa [prefixWord, tailWord_7367291, baseEnd_7367291] using wordTrace_append hprefix tailTrace_7367291
  have hstable : (prefixWord ++ tailWord_7367291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367291).length < 2 ^ (prefixWord ++ tailWord_7367291).sum := by decide
  have hdescent : baseEnd_7367291 < baseStart_7367291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367292 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_7367292 : Nat := 118140960795 + 7367292 * 2 ^ 59
def prefixEnd_7367292 : Nat := 4983230072969 + 3 ^ 40 * 7367292 * 2
def baseEnd_7367292 : Nat := 1260987306007964889956149

theorem tailTrace_7367292 : CollatzResearch.WordTrace tailWord_7367292 prefixEnd_7367292 1260987306007964889956149 := by
  unfold tailWord_7367292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134353607212783396072820065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179138142950377861430426753 134353607212783396072820065)
  ·
    refine ⟨100765205409587547054615049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134353607212783396072820065 100765205409587547054615049)
    ·
      refine ⟨75573904057190660290961287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100765205409587547054615049 75573904057190660290961287)
      ·
        refine ⟨113360856085785990436441931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75573904057190660290961287 113360856085785990436441931)
        ·
          refine ⟨170041284128678985654662897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113360856085785990436441931 170041284128678985654662897)
          ·
            refine ⟨127530963096509239240997173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170041284128678985654662897 127530963096509239240997173)
            ·
              refine ⟨11956027790297741178843485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127530963096509239240997173 11956027790297741178843485)
              ·
                refine ⟨4483510421361652942066307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11956027790297741178843485 4483510421361652942066307)
                ·
                  refine ⟨6725265632042479413099461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483510421361652942066307 6725265632042479413099461)
                  ·
                    refine ⟨1260987306007964889956149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725265632042479413099461 1260987306007964889956149)
                    ·
                      rfl

theorem cell23_7367292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_7367292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367292 prefixEnd_7367292 := by exact prefixLift 7367292
  have htrace : WordTrace (prefixWord ++ tailWord_7367292) baseStart_7367292 baseEnd_7367292 := by
    simpa [prefixWord, tailWord_7367292, baseEnd_7367292] using wordTrace_append hprefix tailTrace_7367292
  have hstable : (prefixWord ++ tailWord_7367292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367292).length < 2 ^ (prefixWord ++ tailWord_7367292).sum := by decide
  have hdescent : baseEnd_7367292 < baseStart_7367292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367322 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_7367322 : Nat := 118140960795 + 7367322 * 2 ^ 59
def prefixEnd_7367322 : Nat := 4983230072969 + 3 ^ 40 * 7367322 * 2
def baseEnd_7367322 : Nat := 420330813604836616943701

theorem tailTrace_7367322 : CollatzResearch.WordTrace tailWord_7367322 prefixEnd_7367322 420330813604836616943701 := by
  unfold tailWord_7367322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67177077153864526817308055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179138872410305404846154813 67177077153864526817308055)
  ·
    refine ⟨100765615730796790225962083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67177077153864526817308055 100765615730796790225962083)
    ·
      refine ⟨151148423596195185338943125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100765615730796790225962083 151148423596195185338943125)
      ·
        refine ⟨7085082356071649312762959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151148423596195185338943125 7085082356071649312762959)
        ·
          refine ⟨10627623534107473969144439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7085082356071649312762959 10627623534107473969144439)
          ·
            refine ⟨15941435301161210953716659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10627623534107473969144439 15941435301161210953716659)
            ·
              refine ⟨23912152951741816430574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941435301161210953716659 23912152951741816430574989)
              ·
                refine ⟨8967057356903181161465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23912152951741816430574989 8967057356903181161465621)
                ·
                  refine ⟨420330813604836616943701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8967057356903181161465621 420330813604836616943701)
                  ·
                    rfl

theorem cell23_7367322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_7367322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367322 prefixEnd_7367322 := by exact prefixLift 7367322
  have htrace : WordTrace (prefixWord ++ tailWord_7367322) baseStart_7367322 baseEnd_7367322 := by
    simpa [prefixWord, tailWord_7367322, baseEnd_7367322] using wordTrace_append hprefix tailTrace_7367322
  have hstable : (prefixWord ++ tailWord_7367322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367322).length < 2 ^ (prefixWord ++ tailWord_7367322).sum := by decide
  have hdescent : baseEnd_7367322 < baseStart_7367322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367325 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_7367325 : Nat := 118140960795 + 7367325 * 2 ^ 59
def prefixEnd_7367325 : Nat := 4983230072969 + 3 ^ 40 * 7367325 * 2
def baseEnd_7367325 : Nat := 3782978862885493040755795

theorem tailTrace_7367325 : CollatzResearch.WordTrace tailWord_7367325 prefixEnd_7367325 3782978862885493040755795 := by
  unfold tailWord_7367325
  simp only [CollatzResearch.WordTrace]
  refine ⟨268708418034447238781591429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179138945356298159187727619 268708418034447238781591429)
  ·
    refine ⟨50382828381458857271548393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268708418034447238781591429 50382828381458857271548393)
    ·
      refine ⟨37787121286094142953661295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50382828381458857271548393 37787121286094142953661295)
      ·
        refine ⟨56680681929141214430491943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37787121286094142953661295 56680681929141214430491943)
        ·
          refine ⟨85021022893711821645737915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56680681929141214430491943 85021022893711821645737915)
          ·
            refine ⟨127531534340567732468606873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85021022893711821645737915 127531534340567732468606873)
            ·
              refine ⟨95648650755425799351455155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127531534340567732468606873 95648650755425799351455155)
              ·
                refine ⟨143472976133138699027182733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95648650755425799351455155 143472976133138699027182733)
                ·
                  refine ⟨53802366049927012135193525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143472976133138699027182733 53802366049927012135193525)
                  ·
                    refine ⟨5043971817180657387674393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53802366049927012135193525 5043971817180657387674393)
                    ·
                      refine ⟨3782978862885493040755795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5043971817180657387674393 3782978862885493040755795)
                      ·
                        rfl

theorem cell23_7367325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_7367325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367325 prefixEnd_7367325 := by exact prefixLift 7367325
  have htrace : WordTrace (prefixWord ++ tailWord_7367325) baseStart_7367325 baseEnd_7367325 := by
    simpa [prefixWord, tailWord_7367325, baseEnd_7367325] using wordTrace_append hprefix tailTrace_7367325
  have hstable : (prefixWord ++ tailWord_7367325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367325).length < 2 ^ (prefixWord ++ tailWord_7367325).sum := by decide
  have hdescent : baseEnd_7367325 < baseStart_7367325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367385 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_7367385 : Nat := 118140960795 + 7367385 * 2 ^ 59
def prefixEnd_7367385 : Nat := 4983230072969 + 3 ^ 40 * 7367385 * 2
def baseEnd_7367385 : Nat := 3783009671724762806005519

theorem tailTrace_7367385 : CollatzResearch.WordTrace tailWord_7367385 prefixEnd_7367385 3783009671724762806005519 := by
  unfold tailWord_7367385
  simp only [CollatzResearch.WordTrace]
  refine ⟨268710606414229869028775609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179140404276153246019183739 268710606414229869028775609)
  ·
    refine ⟨201532954810672401771581707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268710606414229869028775609 201532954810672401771581707)
    ·
      refine ⟨302299432216008602657372561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201532954810672401771581707 302299432216008602657372561)
      ·
        refine ⟨226724574162006451993029421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302299432216008602657372561 226724574162006451993029421)
        ·
          refine ⟨85021715310752419497386033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226724574162006451993029421 85021715310752419497386033)
          ·
            refine ⟨63766286483064314623039525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85021715310752419497386033 63766286483064314623039525)
            ·
              refine ⟨11956178715574558991819911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63766286483064314623039525 11956178715574558991819911)
              ·
                refine ⟨17934268073361838487729867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11956178715574558991819911 17934268073361838487729867)
                ·
                  refine ⟨26901402110042757731594801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17934268073361838487729867 26901402110042757731594801)
                  ·
                    refine ⟨20176051582532068298696101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26901402110042757731594801 20176051582532068298696101)
                    ·
                      refine ⟨3783009671724762806005519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20176051582532068298696101 3783009671724762806005519)
                      ·
                        rfl

theorem cell23_7367385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_7367385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367385 prefixEnd_7367385 := by exact prefixLift 7367385
  have htrace : WordTrace (prefixWord ++ tailWord_7367385) baseStart_7367385 baseEnd_7367385 := by
    simpa [prefixWord, tailWord_7367385, baseEnd_7367385] using wordTrace_append hprefix tailTrace_7367385
  have hstable : (prefixWord ++ tailWord_7367385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367385).length < 2 ^ (prefixWord ++ tailWord_7367385).sum := by decide
  have hdescent : baseEnd_7367385 < baseStart_7367385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367406 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_7367406 : Nat := 118140960795 + 7367406 * 2 ^ 59
def prefixEnd_7367406 : Nat := 4983230072969 + 3 ^ 40 * 7367406 * 2
def baseEnd_7367406 : Nat := 3783020454818507223842923

theorem tailTrace_7367406 : CollatzResearch.WordTrace tailWord_7367406 prefixEnd_7367406 3783020454818507223842923 := by
  unfold tailWord_7367406
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588921543394223701911259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179140914898102526410193381 33588921543394223701911259)
  ·
    refine ⟨50383382315091335552866889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33588921543394223701911259 50383382315091335552866889)
    ·
      refine ⟨37787536736318501664650167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50383382315091335552866889 37787536736318501664650167)
      ·
        refine ⟨56681305104477752496975251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37787536736318501664650167 56681305104477752496975251)
        ·
          refine ⟨85021957656716628745462877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56681305104477752496975251 85021957656716628745462877)
          ·
            refine ⟨31883234121268735779548579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85021957656716628745462877 31883234121268735779548579)
            ·
              refine ⟨47824851181903103669322869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31883234121268735779548579 47824851181903103669322869)
              ·
                refine ⟨4483579798303415968999019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47824851181903103669322869 4483579798303415968999019)
                ·
                  refine ⟨6725369697455123953498529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483579798303415968999019 6725369697455123953498529)
                  ·
                    refine ⟨5044027273091342965123897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725369697455123953498529 5044027273091342965123897)
                    ·
                      refine ⟨3783020454818507223842923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044027273091342965123897 3783020454818507223842923)
                      ·
                        rfl

theorem cell23_7367406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_7367406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367406 prefixEnd_7367406 := by exact prefixLift 7367406
  have htrace : WordTrace (prefixWord ++ tailWord_7367406) baseStart_7367406 baseEnd_7367406 := by
    simpa [prefixWord, tailWord_7367406, baseEnd_7367406] using wordTrace_append hprefix tailTrace_7367406
  have hstable : (prefixWord ++ tailWord_7367406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367406).length < 2 ^ (prefixWord ++ tailWord_7367406).sum := by decide
  have hdescent : baseEnd_7367406 < baseStart_7367406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367439 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 2, 1, 3]
def baseStart_7367439 : Nat := 118140960795 + 7367439 * 2 ^ 59
def prefixEnd_7367439 : Nat := 4983230072969 + 3 ^ 40 * 7367439 * 2
def baseEnd_7367439 : Nat := 3783037399680105594730271

theorem tailTrace_7367439 : CollatzResearch.WordTrace tailWord_7367439 prefixEnd_7367439 3783037399680105594730271 := by
  unfold tailWord_7367439
  simp only [CollatzResearch.WordTrace]
  refine ⟨268712575956034236251241371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179141717304022824167494247 268712575956034236251241371)
  ·
    refine ⟨403068863934051354376862057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268712575956034236251241371 403068863934051354376862057)
    ·
      refine ⟨302301647950538515782646543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403068863934051354376862057 302301647950538515782646543)
      ·
        refine ⟨453452471925807773673969815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302301647950538515782646543 453452471925807773673969815)
        ·
          refine ⟨680178707888711660510954723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453452471925807773673969815 680178707888711660510954723)
          ·
            refine ⟨1020268061833067490766432085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680178707888711660510954723 1020268061833067490766432085)
            ·
              refine ⟨5978133174803129828709563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1020268061833067490766432085 5978133174803129828709563)
              ·
                refine ⟨8967199762204694743064345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978133174803129828709563 8967199762204694743064345)
                ·
                  refine ⟨6725399821653521057298259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967199762204694743064345 6725399821653521057298259)
                  ·
                    refine ⟨10088099732480281585947389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6725399821653521057298259 10088099732480281585947389)
                    ·
                      refine ⟨3783037399680105594730271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088099732480281585947389 3783037399680105594730271)
                      ·
                        rfl

theorem cell23_7367439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 1, 3].length) (baseStart_7367439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367439 prefixEnd_7367439 := by exact prefixLift 7367439
  have htrace : WordTrace (prefixWord ++ tailWord_7367439) baseStart_7367439 baseEnd_7367439 := by
    simpa [prefixWord, tailWord_7367439, baseEnd_7367439] using wordTrace_append hprefix tailTrace_7367439
  have hstable : (prefixWord ++ tailWord_7367439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367439).length < 2 ^ (prefixWord ++ tailWord_7367439).sum := by decide
  have hdescent : baseEnd_7367439 < baseStart_7367439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367479 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_7367479 : Nat := 118140960795 + 7367479 * 2 ^ 59
def prefixEnd_7367479 : Nat := 4983230072969 + 3 ^ 40 * 7367479 * 2
def baseEnd_7367479 : Nat := 3783057938906285438230087

theorem tailTrace_7367479 : CollatzResearch.WordTrace tailWord_7367479 prefixEnd_7367479 3783057938906285438230087 := by
  unfold tailWord_7367479
  simp only [CollatzResearch.WordTrace]
  refine ⟨268714034875889323082697491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179142689917259548721798327 268714034875889323082697491)
  ·
    refine ⟨403071052313833984624046237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268714034875889323082697491 403071052313833984624046237)
    ·
      refine ⟨151151644617687744234017339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403071052313833984624046237 151151644617687744234017339)
      ·
        refine ⟨226727466926531616351026009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151151644617687744234017339 226727466926531616351026009)
        ·
          refine ⟨170045600194898712263269507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226727466926531616351026009 170045600194898712263269507)
          ·
            refine ⟨255068400292348068394904261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170045600194898712263269507 255068400292348068394904261)
            ·
              refine ⟨47825325054815262824044549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255068400292348068394904261 47825325054815262824044549)
              ·
                refine ⟨8967248447777861779508353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47825325054815262824044549 8967248447777861779508353)
                ·
                  refine ⟨6725436335833396334631265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967248447777861779508353 6725436335833396334631265)
                  ·
                    refine ⟨5044077251875047250973449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725436335833396334631265 5044077251875047250973449)
                    ·
                      refine ⟨3783057938906285438230087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044077251875047250973449 3783057938906285438230087)
                      ·
                        rfl

theorem cell23_7367479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_7367479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367479 prefixEnd_7367479 := by exact prefixLift 7367479
  have htrace : WordTrace (prefixWord ++ tailWord_7367479) baseStart_7367479 baseEnd_7367479 := by
    simpa [prefixWord, tailWord_7367479, baseEnd_7367479] using wordTrace_append hprefix tailTrace_7367479
  have hstable : (prefixWord ++ tailWord_7367479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367479).length < 2 ^ (prefixWord ++ tailWord_7367479).sum := by decide
  have hdescent : baseEnd_7367479 < baseStart_7367479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367495 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_7367495 : Nat := 118140960795 + 7367495 * 2 ^ 59
def prefixEnd_7367495 : Nat := 4983230072969 + 3 ^ 40 * 7367495 * 2
def baseEnd_7367495 : Nat := 3783066154596757375630013

theorem tailTrace_7367495 : CollatzResearch.WordTrace tailWord_7367495 prefixEnd_7367495 3783066154596757375630013 := by
  unfold tailWord_7367495
  simp only [CollatzResearch.WordTrace]
  refine ⟨268714618443831357815279939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179143078962554238543519959 268714618443831357815279939)
  ·
    refine ⟨403071927665747036722919909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268714618443831357815279939 403071927665747036722919909)
    ·
      refine ⟨75575986437327569385547483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403071927665747036722919909 75575986437327569385547483)
      ·
        refine ⟨113363979655991354078321225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75575986437327569385547483 113363979655991354078321225)
        ·
          refine ⟨85022984741993515558740919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113363979655991354078321225 85022984741993515558740919)
          ·
            refine ⟨127534477112990273338111379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85022984741993515558740919 127534477112990273338111379)
            ·
              refine ⟨191301715669485410007167069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127534477112990273338111379 191301715669485410007167069)
              ·
                refine ⟨71738143376057028752687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191301715669485410007167069 71738143376057028752687651)
                ·
                  refine ⟨107607215064085543129031477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71738143376057028752687651 107607215064085543129031477)
                  ·
                    refine ⟨10088176412258019668346701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107607215064085543129031477 10088176412258019668346701)
                    ·
                      refine ⟨3783066154596757375630013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088176412258019668346701 3783066154596757375630013)
                      ·
                        rfl

theorem cell23_7367495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_7367495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367495 prefixEnd_7367495 := by exact prefixLift 7367495
  have htrace : WordTrace (prefixWord ++ tailWord_7367495) baseStart_7367495 baseEnd_7367495 := by
    simpa [prefixWord, tailWord_7367495, baseEnd_7367495] using wordTrace_append hprefix tailTrace_7367495
  have hstable : (prefixWord ++ tailWord_7367495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367495).length < 2 ^ (prefixWord ++ tailWord_7367495).sum := by decide
  have hdescent : baseEnd_7367495 < baseStart_7367495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367525 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_7367525 : Nat := 118140960795 + 7367525 * 2 ^ 59
def prefixEnd_7367525 : Nat := 4983230072969 + 3 ^ 40 * 7367525 * 2
def baseEnd_7367525 : Nat := 3783081559016392258254875

theorem tailTrace_7367525 : CollatzResearch.WordTrace tailWord_7367525 prefixEnd_7367525 3783081559016392258254875 := by
  unfold tailWord_7367525
  simp only [CollatzResearch.WordTrace]
  refine ⟨268715712633722672938872029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179143808422481781959248019 268715712633722672938872029)
  ·
    refine ⟨100768392237646002352077011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268715712633722672938872029 100768392237646002352077011)
    ·
      refine ⟨151152588356469003528115517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100768392237646002352077011 151152588356469003528115517)
      ·
        refine ⟨56682220633675876323043319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151152588356469003528115517 56682220633675876323043319)
        ·
          refine ⟨85023330950513814484564979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56682220633675876323043319 85023330950513814484564979)
          ·
            refine ⟨127534996425770721726847469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85023330950513814484564979 127534996425770721726847469)
            ·
              refine ⟨47825623659664020647567801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127534996425770721726847469 47825623659664020647567801)
              ·
                refine ⟨35869217744748015485675851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47825623659664020647567801 35869217744748015485675851)
                ·
                  refine ⟨53803826617122023228513777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35869217744748015485675851 53803826617122023228513777)
                  ·
                    refine ⟨40352869962841517421385333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53803826617122023228513777 40352869962841517421385333)
                    ·
                      refine ⟨3783081559016392258254875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40352869962841517421385333 3783081559016392258254875)
                      ·
                        rfl

theorem cell23_7367525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_7367525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367525 prefixEnd_7367525 := by exact prefixLift 7367525
  have htrace : WordTrace (prefixWord ++ tailWord_7367525) baseStart_7367525 baseEnd_7367525 := by
    simpa [prefixWord, tailWord_7367525, baseEnd_7367525] using wordTrace_append hprefix tailTrace_7367525
  have hstable : (prefixWord ++ tailWord_7367525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367525).length < 2 ^ (prefixWord ++ tailWord_7367525).sum := by decide
  have hdescent : baseEnd_7367525 < baseStart_7367525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367575 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 8]
def baseStart_7367575 : Nat := 118140960795 + 7367575 * 2 ^ 59
def prefixEnd_7367575 : Nat := 4983230072969 + 3 ^ 40 * 7367575 * 2
def baseEnd_7367575 : Nat := 420345248116568562514405

theorem tailTrace_7367575 : CollatzResearch.WordTrace tailWord_7367575 prefixEnd_7367575 420345248116568562514405 := by
  unfold tailWord_7367575
  simp only [CollatzResearch.WordTrace]
  refine ⟨268717536283541531478192179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179145024189027687652128119 268717536283541531478192179)
  ·
    refine ⟨403076304425312297217288269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268717536283541531478192179 403076304425312297217288269)
    ·
      refine ⟨151153614159492111456483101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403076304425312297217288269 151153614159492111456483101)
      ·
        refine ⟨56682605309809541796181163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151153614159492111456483101 56682605309809541796181163)
        ·
          refine ⟨85023907964714312694271745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56682605309809541796181163 85023907964714312694271745)
          ·
            refine ⟨63767930973535734520703809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85023907964714312694271745 63767930973535734520703809)
            ·
              refine ⟨47825948230151800890527857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63767930973535734520703809 47825948230151800890527857)
              ·
                refine ⟨35869461172613850667895893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47825948230151800890527857 35869461172613850667895893)
                ·
                  refine ⟨420345248116568562514405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35869461172613850667895893 420345248116568562514405)
                  ·
                    rfl

theorem cell23_7367575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 8].length) (baseStart_7367575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367575 prefixEnd_7367575 := by exact prefixLift 7367575
  have htrace : WordTrace (prefixWord ++ tailWord_7367575) baseStart_7367575 baseEnd_7367575 := by
    simpa [prefixWord, tailWord_7367575, baseEnd_7367575] using wordTrace_append hprefix tailTrace_7367575
  have hstable : (prefixWord ++ tailWord_7367575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367575).length < 2 ^ (prefixWord ++ tailWord_7367575).sum := by decide
  have hdescent : baseEnd_7367575 < baseStart_7367575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367609 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 6]
def baseStart_7367609 : Nat := 118140960795 + 7367609 * 2 ^ 59
def prefixEnd_7367609 : Nat := 4983230072969 + 3 ^ 40 * 7367609 * 2
def baseEnd_7367609 : Nat := 420347187932374436622721

theorem tailTrace_7367609 : CollatzResearch.WordTrace tailWord_7367609 prefixEnd_7367609 420347187932374436622721 := by
  unfold tailWord_7367609
  simp only [CollatzResearch.WordTrace]
  refine ⟨268718776365418355284929881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179145850910278903523286587 268718776365418355284929881)
  ·
    refine ⟨201539082274063766463697411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268718776365418355284929881 201539082274063766463697411)
    ·
      refine ⟨302308623411095649695546117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201539082274063766463697411 302308623411095649695546117)
      ·
        refine ⟨56682866889580434317914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302308623411095649695546117 56682866889580434317914897)
        ·
          refine ⟨42512150167185325738436173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56682866889580434317914897 42512150167185325738436173)
          ·
            refine ⟨15942056312694497151913565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42512150167185325738436173 15942056312694497151913565)
            ·
              refine ⟨5978271117260436431967587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15942056312694497151913565 5978271117260436431967587)
              ·
                refine ⟨8967406675890654647951381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978271117260436431967587 8967406675890654647951381)
                ·
                  refine ⟨420347187932374436622721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8967406675890654647951381 420347187932374436622721)
                  ·
                    rfl

theorem cell23_7367609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_7367609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367609 prefixEnd_7367609 := by exact prefixLift 7367609
  have htrace : WordTrace (prefixWord ++ tailWord_7367609) baseStart_7367609 baseEnd_7367609 := by
    simpa [prefixWord, tailWord_7367609, baseEnd_7367609] using wordTrace_append hprefix tailTrace_7367609
  have hstable : (prefixWord ++ tailWord_7367609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367609).length < 2 ^ (prefixWord ++ tailWord_7367609).sum := by decide
  have hdescent : baseEnd_7367609 < baseStart_7367609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367672 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_7367672 : Nat := 118140960795 + 7367672 * 2 ^ 59
def prefixEnd_7367672 : Nat := 4983230072969 + 3 ^ 40 * 7367672 * 2
def baseEnd_7367672 : Nat := 3783157040672603183116699

theorem tailTrace_7367672 : CollatzResearch.WordTrace tailWord_7367672 prefixEnd_7367672 3783157040672603183116699 := by
  unfold tailWord_7367672
  simp only [CollatzResearch.WordTrace]
  refine ⟨134360537082095058522236635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179147382776126744696315513 134360537082095058522236635)
  ·
    refine ⟨201540805623142587783354953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134360537082095058522236635 201540805623142587783354953)
    ·
      refine ⟨151155604217356940837516215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201540805623142587783354953 151155604217356940837516215)
      ·
        refine ⟨226733406326035411256274323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151155604217356940837516215 226733406326035411256274323)
        ·
          refine ⟨340100109489053116884411485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226733406326035411256274323 340100109489053116884411485)
          ·
            refine ⟨127537541058394918831654307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340100109489053116884411485 127537541058394918831654307)
            ·
              refine ⟨191306311587592378247481461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127537541058394918831654307 191306311587592378247481461)
              ·
                refine ⟨17934966711336785460701387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191306311587592378247481461 17934966711336785460701387)
                ·
                  refine ⟨26902450067005178191052081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17934966711336785460701387 26902450067005178191052081)
                  ·
                    refine ⟨20176837550253883643289061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26902450067005178191052081 20176837550253883643289061)
                    ·
                      refine ⟨3783157040672603183116699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20176837550253883643289061 3783157040672603183116699)
                      ·
                        rfl

theorem cell23_7367672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_7367672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367672 prefixEnd_7367672 := by exact prefixLift 7367672
  have htrace : WordTrace (prefixWord ++ tailWord_7367672) baseStart_7367672 baseEnd_7367672 := by
    simpa [prefixWord, tailWord_7367672, baseEnd_7367672] using wordTrace_append hprefix tailTrace_7367672
  have hstable : (prefixWord ++ tailWord_7367672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367672).length < 2 ^ (prefixWord ++ tailWord_7367672).sum := by decide
  have hdescent : baseEnd_7367672 < baseStart_7367672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367676 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_7367676 : Nat := 118140960795 + 7367676 * 2 ^ 59
def prefixEnd_7367676 : Nat := 4983230072969 + 3 ^ 40 * 7367676 * 2
def baseEnd_7367676 : Nat := 3783159094595221167466681

theorem tailTrace_7367676 : CollatzResearch.WordTrace tailWord_7367676 prefixEnd_7367676 3783159094595221167466681 := by
  unfold tailWord_7367676
  simp only [CollatzResearch.WordTrace]
  refine ⟨134360610028087812863809441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179147480037450417151745921 134360610028087812863809441)
  ·
    refine ⟨100770457521065859647857081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134360610028087812863809441 100770457521065859647857081)
    ·
      refine ⟨75577843140799394735892811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100770457521065859647857081 75577843140799394735892811)
      ·
        refine ⟨113366764711199092103839217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75577843140799394735892811 113366764711199092103839217)
        ·
          refine ⟨85025073533399319077879413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113366764711199092103839217 85025073533399319077879413)
          ·
            refine ⟨7971100643756186163551195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85025073533399319077879413 7971100643756186163551195)
            ·
              refine ⟨11956650965634279245326793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971100643756186163551195 11956650965634279245326793)
              ·
                refine ⟨8967488224225709433995095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11956650965634279245326793 8967488224225709433995095)
                ·
                  refine ⟨13451232336338564150992643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8967488224225709433995095 13451232336338564150992643)
                  ·
                    refine ⟨20176848504507846226488965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13451232336338564150992643 20176848504507846226488965)
                    ·
                      refine ⟨3783159094595221167466681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20176848504507846226488965 3783159094595221167466681)
                      ·
                        rfl

theorem cell23_7367676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_7367676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367676 prefixEnd_7367676 := by exact prefixLift 7367676
  have htrace : WordTrace (prefixWord ++ tailWord_7367676) baseStart_7367676 baseEnd_7367676 := by
    simpa [prefixWord, tailWord_7367676, baseEnd_7367676] using wordTrace_append hprefix tailTrace_7367676
  have hstable : (prefixWord ++ tailWord_7367676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367676).length < 2 ^ (prefixWord ++ tailWord_7367676).sum := by decide
  have hdescent : baseEnd_7367676 < baseStart_7367676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367726 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7367726 : Nat := 118140960795 + 7367726 * 2 ^ 59
def prefixEnd_7367726 : Nat := 4983230072969 + 3 ^ 40 * 7367726 * 2
def baseEnd_7367726 : Nat := 3783184768627945971841451

theorem tailTrace_7367726 : CollatzResearch.WordTrace tailWord_7367726 prefixEnd_7367726 3783184768627945971841451 := by
  unfold tailWord_7367726
  simp only [CollatzResearch.WordTrace]
  refine ⟨33590380463249310533367379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179148695803996322844626021 33590380463249310533367379)
  ·
    refine ⟨50385570694873965800051069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33590380463249310533367379 50385570694873965800051069)
    ·
      refine ⟨18894589010577737175019151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50385570694873965800051069 18894589010577737175019151)
      ·
        refine ⟨28341883515866605762528727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18894589010577737175019151 28341883515866605762528727)
        ·
          refine ⟨42512825273799908643793091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28341883515866605762528727 42512825273799908643793091)
          ·
            refine ⟨63769237910699862965689637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42512825273799908643793091 63769237910699862965689637)
            ·
              refine ⟨11956732108256224306066807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63769237910699862965689637 11956732108256224306066807)
              ·
                refine ⟨17935098162384336459100211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11956732108256224306066807 17935098162384336459100211)
                ·
                  refine ⟨26902647243576504688650317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17935098162384336459100211 26902647243576504688650317)
                  ·
                    refine ⟨10088492716341189258243869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26902647243576504688650317 10088492716341189258243869)
                    ·
                      refine ⟨3783184768627945971841451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088492716341189258243869 3783184768627945971841451)
                      ·
                        rfl

theorem cell23_7367726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7367726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367726 prefixEnd_7367726 := by exact prefixLift 7367726
  have htrace : WordTrace (prefixWord ++ tailWord_7367726) baseStart_7367726 baseEnd_7367726 := by
    simpa [prefixWord, tailWord_7367726, baseEnd_7367726] using wordTrace_append hprefix tailTrace_7367726
  have hstable : (prefixWord ++ tailWord_7367726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367726).length < 2 ^ (prefixWord ++ tailWord_7367726).sum := by decide
  have hdescent : baseEnd_7367726 < baseStart_7367726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367736 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_7367736 : Nat := 118140960795 + 7367736 * 2 ^ 59
def prefixEnd_7367736 : Nat := 4983230072969 + 3 ^ 40 * 7367736 * 2
def baseEnd_7367736 : Nat := 3783189903434490932716405

theorem tailTrace_7367736 : CollatzResearch.WordTrace tailWord_7367736 prefixEnd_7367736 3783189903434490932716405 := by
  unfold tailWord_7367736
  simp only [CollatzResearch.WordTrace]
  refine ⟨134361704217979127987401531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179148938957305503983202041 134361704217979127987401531)
  ·
    refine ⟨201542556326968691981102297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134361704217979127987401531 201542556326968691981102297)
    ·
      refine ⟨151156917245226518985826723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201542556326968691981102297 151156917245226518985826723)
      ·
        refine ⟨226735375867839778478740085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151156917245226518985826723 226735375867839778478740085)
        ·
          refine ⟨21256441487609979232381883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226735375867839778478740085 21256441487609979232381883)
          ·
            refine ⟨31884662231414968848572825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21256441487609979232381883 31884662231414968848572825)
            ·
              refine ⟨23913496673561226636429619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31884662231414968848572825 23913496673561226636429619)
              ·
                refine ⟨35870245010341839954644429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23913496673561226636429619 35870245010341839954644429)
                ·
                  refine ⟨13451341878878189982991661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35870245010341839954644429 13451341878878189982991661)
                  ·
                    refine ⟨5044253204579321243621873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13451341878878189982991661 5044253204579321243621873)
                    ·
                      refine ⟨3783189903434490932716405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044253204579321243621873 3783189903434490932716405)
                      ·
                        rfl

theorem cell23_7367736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_7367736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367736 prefixEnd_7367736 := by exact prefixLift 7367736
  have htrace : WordTrace (prefixWord ++ tailWord_7367736) baseStart_7367736 baseEnd_7367736 := by
    simpa [prefixWord, tailWord_7367736, baseEnd_7367736] using wordTrace_append hprefix tailTrace_7367736
  have hstable : (prefixWord ++ tailWord_7367736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367736).length < 2 ^ (prefixWord ++ tailWord_7367736).sum := by decide
  have hdescent : baseEnd_7367736 < baseStart_7367736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367752 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7367752 : Nat := 118140960795 + 7367752 * 2 ^ 59
def prefixEnd_7367752 : Nat := 4983230072969 + 3 ^ 40 * 7367752 * 2
def baseEnd_7367752 : Nat := 3783198119124962870116331

theorem tailTrace_7367752 : CollatzResearch.WordTrace tailWord_7367752 prefixEnd_7367752 3783198119124962870116331 := by
  unfold tailWord_7367752
  simp only [CollatzResearch.WordTrace]
  refine ⟨134361996001950145353692755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179149328002600193804923673 134361996001950145353692755)
  ·
    refine ⟨201542994002925218030539133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134361996001950145353692755 201542994002925218030539133)
    ·
      refine ⟨75578622751096956761452175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201542994002925218030539133 75578622751096956761452175)
      ·
        refine ⟨113367934126645435142178263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75578622751096956761452175 113367934126645435142178263)
        ·
          refine ⟨170051901189968152713267395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113367934126645435142178263 170051901189968152713267395)
          ·
            refine ⟨255077851784952229069901093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170051901189968152713267395 255077851784952229069901093)
            ·
              refine ⟨47827097209678542950606455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255077851784952229069901093 47827097209678542950606455)
              ·
                refine ⟨71740645814517814425909683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47827097209678542950606455 71740645814517814425909683)
                ·
                  refine ⟨107610968721776721638864525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71740645814517814425909683 107610968721776721638864525)
                  ·
                    refine ⟨40354113270666270614574197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107610968721776721638864525 40354113270666270614574197)
                    ·
                      refine ⟨3783198119124962870116331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40354113270666270614574197 3783198119124962870116331)
                      ·
                        rfl

theorem cell23_7367752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7367752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367752 prefixEnd_7367752 := by exact prefixLift 7367752
  have htrace : WordTrace (prefixWord ++ tailWord_7367752) baseStart_7367752 baseEnd_7367752 := by
    simpa [prefixWord, tailWord_7367752, baseEnd_7367752] using wordTrace_append hprefix tailTrace_7367752
  have hstable : (prefixWord ++ tailWord_7367752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367752).length < 2 ^ (prefixWord ++ tailWord_7367752).sum := by decide
  have hdescent : baseEnd_7367752 < baseStart_7367752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367783 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_7367783 : Nat := 118140960795 + 7367783 * 2 ^ 59
def prefixEnd_7367783 : Nat := 4983230072969 + 3 ^ 40 * 7367783 * 2
def baseEnd_7367783 : Nat := 3783214037025252248828689

theorem tailTrace_7367783 : CollatzResearch.WordTrace tailWord_7367783 prefixEnd_7367783 3783214037025252248828689 := by
  unfold tailWord_7367783
  simp only [CollatzResearch.WordTrace]
  refine ⟨268725122666787983001764003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179150081777858655334509335 268725122666787983001764003)
  ·
    refine ⟨403087684000181974502646005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268725122666787983001764003 403087684000181974502646005)
    ·
      refine ⟨37789470375017060109623063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403087684000181974502646005 37789470375017060109623063)
      ·
        refine ⟨56684205562525590164434595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37789470375017060109623063 56684205562525590164434595)
        ·
          refine ⟨85026308343788385246651893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56684205562525590164434595 85026308343788385246651893)
          ·
            refine ⟨7971216407230161116873615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85026308343788385246651893 7971216407230161116873615)
            ·
              refine ⟨11956824610845241675310423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971216407230161116873615 11956824610845241675310423)
              ·
                refine ⟨17935236916267862512965635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11956824610845241675310423 17935236916267862512965635)
                ·
                  refine ⟨26902855374401793769448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17935236916267862512965635 26902855374401793769448453)
                  ·
                    refine ⟨5044285382700336331771585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26902855374401793769448453 5044285382700336331771585)
                    ·
                      refine ⟨3783214037025252248828689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044285382700336331771585 3783214037025252248828689)
                      ·
                        rfl

theorem cell23_7367783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_7367783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367783 prefixEnd_7367783 := by exact prefixLift 7367783
  have htrace : WordTrace (prefixWord ++ tailWord_7367783) baseStart_7367783 baseEnd_7367783 := by
    simpa [prefixWord, tailWord_7367783, baseEnd_7367783] using wordTrace_append hprefix tailTrace_7367783
  have hstable : (prefixWord ++ tailWord_7367783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367783).length < 2 ^ (prefixWord ++ tailWord_7367783).sum := by decide
  have hdescent : baseEnd_7367783 < baseStart_7367783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367789 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 7]
def baseStart_7367789 : Nat := 118140960795 + 7367789 * 2 ^ 59
def prefixEnd_7367789 : Nat := 4983230072969 + 3 ^ 40 * 7367789 * 2
def baseEnd_7367789 : Nat := 420357457545464358372629

theorem tailTrace_7367789 : CollatzResearch.WordTrace tailWord_7367789 prefixEnd_7367789 420357457545464358372629 := by
  unfold tailWord_7367789
  simp only [CollatzResearch.WordTrace]
  refine ⟨268725341504766246026482421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179150227669844164017654947 268725341504766246026482421)
  ·
    refine ⟨25193000766071835564982727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268725341504766246026482421 25193000766071835564982727)
    ·
      refine ⟨37789501149107753347474091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193000766071835564982727 37789501149107753347474091)
      ·
        refine ⟨56684251723661630021211137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37789501149107753347474091 56684251723661630021211137)
        ·
          refine ⟨42513188792746222515908353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56684251723661630021211137 42513188792746222515908353)
          ·
            refine ⟨31884891594559666886931265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42513188792746222515908353 31884891594559666886931265)
            ·
              refine ⟨23913668695919750165198449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31884891594559666886931265 23913668695919750165198449)
              ·
                refine ⟨17935251521939812623898837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23913668695919750165198449 17935251521939812623898837)
                ·
                  refine ⟨420357457545464358372629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17935251521939812623898837 420357457545464358372629)
                  ·
                    rfl

theorem cell23_7367789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_7367789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367789 prefixEnd_7367789 := by exact prefixLift 7367789
  have htrace : WordTrace (prefixWord ++ tailWord_7367789) baseStart_7367789 baseEnd_7367789 := by
    simpa [prefixWord, tailWord_7367789, baseEnd_7367789] using wordTrace_append hprefix tailTrace_7367789
  have hstable : (prefixWord ++ tailWord_7367789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367789).length < 2 ^ (prefixWord ++ tailWord_7367789).sum := by decide
  have hdescent : baseEnd_7367789 < baseStart_7367789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367853 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_7367853 : Nat := 118140960795 + 7367853 * 2 ^ 59
def prefixEnd_7367853 : Nat := 4983230072969 + 3 ^ 40 * 7367853 * 2
def baseEnd_7367853 : Nat := 1261083326890355658317789

theorem tailTrace_7367853 : CollatzResearch.WordTrace tailWord_7367853 prefixEnd_7367853 1261083326890355658317789 := by
  unfold tailWord_7367853
  simp only [CollatzResearch.WordTrace]
  refine ⟨268727675776534384956812213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179151783851022923304541475 268727675776534384956812213)
  ·
    refine ⟨25193219604050098589701145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268727675776534384956812213 25193219604050098589701145)
    ·
      refine ⟨18894914703037573942275859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25193219604050098589701145 18894914703037573942275859)
      ·
        refine ⟨28342372054556360913413789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18894914703037573942275859 28342372054556360913413789)
        ·
          refine ⟨10628389520458635342530171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28342372054556360913413789 10628389520458635342530171)
          ·
            refine ⟨15942584280687953013795257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10628389520458635342530171 15942584280687953013795257)
            ·
              refine ⟨11956938210515964760346443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15942584280687953013795257 11956938210515964760346443)
              ·
                refine ⟨17935407315773947140519665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11956938210515964760346443 17935407315773947140519665)
                ·
                  refine ⟨13451555486830460355389749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17935407315773947140519665 13451555486830460355389749)
                  ·
                    refine ⟨1261083326890355658317789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13451555486830460355389749 1261083326890355658317789)
                    ·
                      rfl

theorem cell23_7367853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_7367853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367853 prefixEnd_7367853 := by exact prefixLift 7367853
  have htrace : WordTrace (prefixWord ++ tailWord_7367853) baseStart_7367853 baseEnd_7367853 := by
    simpa [prefixWord, tailWord_7367853, baseEnd_7367853] using wordTrace_append hprefix tailTrace_7367853
  have hstable : (prefixWord ++ tailWord_7367853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367853).length < 2 ^ (prefixWord ++ tailWord_7367853).sum := by decide
  have hdescent : baseEnd_7367853 < baseStart_7367853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367859 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3]
def baseStart_7367859 : Nat := 118140960795 + 7367859 * 2 ^ 59
def prefixEnd_7367859 : Nat := 4983230072969 + 3 ^ 40 * 7367859 * 2
def baseEnd_7367859 : Nat := 3783253061554993951478339

theorem tailTrace_7367859 : CollatzResearch.WordTrace tailWord_7367859 prefixEnd_7367859 3783253061554993951478339 := by
  unfold tailWord_7367859
  simp only [CollatzResearch.WordTrace]
  refine ⟨268727894614512647981530631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179151929743008431987687087 268727894614512647981530631)
  ·
    refine ⟨403091841921768971972295947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268727894614512647981530631 403091841921768971972295947)
    ·
      refine ⟨604637762882653457958443921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403091841921768971972295947 604637762882653457958443921)
      ·
        refine ⟨453478322161990093468832941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604637762882653457958443921 453478322161990093468832941)
        ·
          refine ⟨170054370810746285050812353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453478322161990093468832941 170054370810746285050812353)
          ·
            refine ⟨127540778108059713788109265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170054370810746285050812353 127540778108059713788109265)
            ·
              refine ⟨95655583581044785341081949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127540778108059713788109265 95655583581044785341081949)
              ·
                refine ⟨35870843842891794502905731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95655583581044785341081949 35870843842891794502905731)
                ·
                  refine ⟨53806265764337691754358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35870843842891794502905731 53806265764337691754358597)
                  ·
                    refine ⟨10088674830813317203942237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53806265764337691754358597 10088674830813317203942237)
                    ·
                      refine ⟨3783253061554993951478339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088674830813317203942237 3783253061554993951478339)
                      ·
                        rfl

theorem cell23_7367859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_7367859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367859 prefixEnd_7367859 := by exact prefixLift 7367859
  have htrace : WordTrace (prefixWord ++ tailWord_7367859) baseStart_7367859 baseEnd_7367859 := by
    simpa [prefixWord, tailWord_7367859, baseEnd_7367859] using wordTrace_append hprefix tailTrace_7367859
  have hstable : (prefixWord ++ tailWord_7367859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367859).length < 2 ^ (prefixWord ++ tailWord_7367859).sum := by decide
  have hdescent : baseEnd_7367859 < baseStart_7367859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367873 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7367873 : Nat := 118140960795 + 7367873 * 2 ^ 59
def prefixEnd_7367873 : Nat := 4983230072969 + 3 ^ 40 * 7367873 * 2
def baseEnd_7367873 : Nat := 3783260250284156896703275

theorem tailTrace_7367873 : CollatzResearch.WordTrace tailWord_7367873 prefixEnd_7367873 3783260250284156896703275 := by
  unfold tailWord_7367873
  simp only [CollatzResearch.WordTrace]
  refine ⟨268728405236461928372540273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179152270157641285581693515 268728405236461928372540273)
  ·
    refine ⟨201546303927346446279405205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268728405236461928372540273 201546303927346446279405205)
    ·
      refine ⟨9447482996594364669347119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201546303927346446279405205 9447482996594364669347119)
      ·
        refine ⟨14171224494891547004020679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447482996594364669347119 14171224494891547004020679)
        ·
          refine ⟨21256836742337320506031019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14171224494891547004020679 21256836742337320506031019)
          ·
            refine ⟨31885255113505980759046529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21256836742337320506031019 31885255113505980759046529)
            ·
              refine ⟨23913941335129485569284897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31885255113505980759046529 23913941335129485569284897)
              ·
                refine ⟨17935456001347114176963673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23913941335129485569284897 17935456001347114176963673)
                ·
                  refine ⟨13451592001010335632722755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17935456001347114176963673 13451592001010335632722755)
                  ·
                    refine ⟨20177388001515503449084133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13451592001010335632722755 20177388001515503449084133)
                    ·
                      refine ⟨3783260250284156896703275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20177388001515503449084133 3783260250284156896703275)
                      ·
                        rfl

theorem cell23_7367873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7367873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367873 prefixEnd_7367873 := by exact prefixLift 7367873
  have htrace : WordTrace (prefixWord ++ tailWord_7367873) baseStart_7367873 baseEnd_7367873 := by
    simpa [prefixWord, tailWord_7367873, baseEnd_7367873] using wordTrace_append hprefix tailTrace_7367873
  have hstable : (prefixWord ++ tailWord_7367873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367873).length < 2 ^ (prefixWord ++ tailWord_7367873).sum := by decide
  have hdescent : baseEnd_7367873 < baseStart_7367873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367874 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7367874 : Nat := 118140960795 + 7367874 * 2 ^ 59
def prefixEnd_7367874 : Nat := 4983230072969 + 3 ^ 40 * 7367874 * 2
def baseEnd_7367874 : Nat := 420362307084979043643419

theorem tailTrace_7367874 : CollatzResearch.WordTrace tailWord_7367874 prefixEnd_7367874 420362307084979043643419 := by
  unfold tailWord_7367874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67182110427364576385831669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179152294472972203695551117 67182110427364576385831669)
  ·
    refine ⟨6298322852565429036171719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67182110427364576385831669 6298322852565429036171719)
    ·
      refine ⟨9447484278848143554257579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298322852565429036171719 9447484278848143554257579)
      ·
        refine ⟨14171226418272215331386369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447484278848143554257579 14171226418272215331386369)
        ·
          refine ⟨10628419813704161498539777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14171226418272215331386369 10628419813704161498539777)
          ·
            refine ⟨7971314860278121123904833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10628419813704161498539777 7971314860278121123904833)
            ·
              refine ⟨5978486145208590842928625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971314860278121123904833 5978486145208590842928625)
              ·
                refine ⟨4483864608906443132196469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978486145208590842928625 4483864608906443132196469)
                ·
                  refine ⟨420362307084979043643419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4483864608906443132196469 420362307084979043643419)
                  ·
                    rfl

theorem cell23_7367874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7367874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367874 prefixEnd_7367874 := by exact prefixLift 7367874
  have htrace : WordTrace (prefixWord ++ tailWord_7367874) baseStart_7367874 baseEnd_7367874 := by
    simpa [prefixWord, tailWord_7367874, baseEnd_7367874] using wordTrace_append hprefix tailTrace_7367874
  have hstable : (prefixWord ++ tailWord_7367874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367874).length < 2 ^ (prefixWord ++ tailWord_7367874).sum := by decide
  have hdescent : baseEnd_7367874 < baseStart_7367874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367889 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_7367889 : Nat := 118140960795 + 7367889 * 2 ^ 59
def prefixEnd_7367889 : Nat := 4983230072969 + 3 ^ 40 * 7367889 * 2
def baseEnd_7367889 : Nat := 3783268465974628834103201

theorem tailTrace_7367889 : CollatzResearch.WordTrace tailWord_7367889 prefixEnd_7367889 3783268465974628834103201 := by
  unfold tailWord_7367889
  simp only [CollatzResearch.WordTrace]
  refine ⟨268728988804403963105122721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179152659202935975403415147 268728988804403963105122721)
  ·
    refine ⟨201546741603302972328842041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268728988804403963105122721 201546741603302972328842041)
    ·
      refine ⟨151160056202477229246631531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201546741603302972328842041 151160056202477229246631531)
      ·
        refine ⟨226740084303715843869947297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151160056202477229246631531 226740084303715843869947297)
        ·
          refine ⟨170055063227786882902460473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226740084303715843869947297 170055063227786882902460473)
          ·
            refine ⟨127541297420840162176845355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170055063227786882902460473 127541297420840162176845355)
            ·
              refine ⟨191311946131260243265268033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127541297420840162176845355 191311946131260243265268033)
              ·
                refine ⟨143483959598445182448951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191311946131260243265268033 143483959598445182448951025)
                ·
                  refine ⟨107612969698833886836713269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143483959598445182448951025 107612969698833886836713269)
                  ·
                    refine ⟨10088715909265676890941869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107612969698833886836713269 10088715909265676890941869)
                    ·
                      refine ⟨3783268465974628834103201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088715909265676890941869 3783268465974628834103201)
                      ·
                        rfl

theorem cell23_7367889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_7367889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367889 prefixEnd_7367889 := by exact prefixLift 7367889
  have htrace : WordTrace (prefixWord ++ tailWord_7367889) baseStart_7367889 baseEnd_7367889 := by
    simpa [prefixWord, tailWord_7367889, baseEnd_7367889] using wordTrace_append hprefix tailTrace_7367889
  have hstable : (prefixWord ++ tailWord_7367889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367889).length < 2 ^ (prefixWord ++ tailWord_7367889).sum := by decide
  have hdescent : baseEnd_7367889 < baseStart_7367889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367940 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7367940 : Nat := 118140960795 + 7367940 * 2 ^ 59
def prefixEnd_7367940 : Nat := 4983230072969 + 3 ^ 40 * 7367940 * 2
def baseEnd_7367940 : Nat := 3783294653488008134565467

theorem tailTrace_7367940 : CollatzResearch.WordTrace tailWord_7367940 prefixEnd_7367940 3783294653488008134565467 := by
  unfold tailWord_7367940
  simp only [CollatzResearch.WordTrace]
  refine ⟨134365424463609599407614637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179153899284812799210152849 134365424463609599407614637)
  ·
    refine ⟨50387034173853599777855489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134365424463609599407614637 50387034173853599777855489)
    ·
      refine ⟨37790275630390199833391617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50387034173853599777855489 37790275630390199833391617)
      ·
        refine ⟨28342706722792649875043713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37790275630390199833391617 28342706722792649875043713)
        ·
          refine ⟨21257030042094487406282785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28342706722792649875043713 21257030042094487406282785)
          ·
            refine ⟨15942772531570865554712089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21257030042094487406282785 15942772531570865554712089)
            ·
              refine ⟨11957079398678149166034067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15942772531570865554712089 11957079398678149166034067)
              ·
                refine ⟨17935619098017223749051101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11957079398678149166034067 17935619098017223749051101)
                ·
                  refine ⟨6725857161756458905894163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17935619098017223749051101 6725857161756458905894163)
                  ·
                    refine ⟨10088785742634688358841245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6725857161756458905894163 10088785742634688358841245)
                    ·
                      refine ⟨3783294653488008134565467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10088785742634688358841245 3783294653488008134565467)
                      ·
                        rfl

theorem cell23_7367940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7367940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367940 prefixEnd_7367940 := by exact prefixLift 7367940
  have htrace : WordTrace (prefixWord ++ tailWord_7367940) baseStart_7367940 baseEnd_7367940 := by
    simpa [prefixWord, tailWord_7367940, baseEnd_7367940] using wordTrace_append hprefix tailTrace_7367940
  have hstable : (prefixWord ++ tailWord_7367940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367940).length < 2 ^ (prefixWord ++ tailWord_7367940).sum := by decide
  have hdescent : baseEnd_7367940 < baseStart_7367940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7367986 : List Nat := [3, 2, 1, 1, 4, 3, 9]
def baseStart_7367986 : Nat := 118140960795 + 7367986 * 2 ^ 59
def prefixEnd_7367986 : Nat := 4983230072969 + 3 ^ 40 * 7367986 * 2
def baseEnd_7367986 : Nat := 46707633007384135241855

theorem tailTrace_7367986 : CollatzResearch.WordTrace tailWord_7367986 prefixEnd_7367986 46707633007384135241855 := by
  unfold tailWord_7367986
  simp only [CollatzResearch.WordTrace]
  refine ⟨67183131671263137167850953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179155017790035032447602541 67183131671263137167850953)
  ·
    refine ⟨50387348753447352875888215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67183131671263137167850953 50387348753447352875888215)
    ·
      refine ⟨75581023130171029313832323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50387348753447352875888215 75581023130171029313832323)
      ·
        refine ⟨113371534695256543970748485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75581023130171029313832323 113371534695256543970748485)
        ·
          refine ⟨21257162755360601994515341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113371534695256543970748485 21257162755360601994515341)
          ·
            refine ⟨7971436033260225747943253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21257162755360601994515341 7971436033260225747943253)
            ·
              refine ⟨46707633007384135241855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7971436033260225747943253 46707633007384135241855)
              ·
                rfl

theorem cell23_7367986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 9].length) (baseStart_7367986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7367986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7367986 prefixEnd_7367986 := by exact prefixLift 7367986
  have htrace : WordTrace (prefixWord ++ tailWord_7367986) baseStart_7367986 baseEnd_7367986 := by
    simpa [prefixWord, tailWord_7367986, baseEnd_7367986] using wordTrace_append hprefix tailTrace_7367986
  have hstable : (prefixWord ++ tailWord_7367986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7367986).length < 2 ^ (prefixWord ++ tailWord_7367986).sum := by decide
  have hdescent : baseEnd_7367986 < baseStart_7367986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7367986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368076 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 7]
def baseStart_7368076 : Nat := 118140960795 + 7368076 * 2 ^ 59
def prefixEnd_7368076 : Nat := 4983230072969 + 3 ^ 40 * 7368076 * 2
def baseEnd_7368076 : Nat := 420373831873002178051649

theorem tailTrace_7368076 : CollatzResearch.WordTrace tailWord_7368076 prefixEnd_7368076 420373831873002178051649 := by
  unfold tailWord_7368076
  simp only [CollatzResearch.WordTrace]
  refine ⟨134367904627363247021090041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179157206169817662694786721 134367904627363247021090041)
  ·
    refine ⟨100775928470522435265817531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134367904627363247021090041 100775928470522435265817531)
    ·
      refine ⟨151163892705783652898726297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100775928470522435265817531 151163892705783652898726297)
      ·
        refine ⟨113372919529337739674044723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151163892705783652898726297 113372919529337739674044723)
        ·
          refine ⟨170059379294006609511067085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113372919529337739674044723 170059379294006609511067085)
          ·
            refine ⟨63772267235252478566650157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170059379294006609511067085 63772267235252478566650157)
            ·
              refine ⟨23914600213219679462493809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63772267235252478566650157 23914600213219679462493809)
              ·
                refine ⟨17935950159914759596870357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23914600213219679462493809 17935950159914759596870357)
                ·
                  refine ⟨420373831873002178051649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17935950159914759596870357 420373831873002178051649)
                  ·
                    rfl

theorem cell23_7368076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_7368076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368076 prefixEnd_7368076 := by exact prefixLift 7368076
  have htrace : WordTrace (prefixWord ++ tailWord_7368076) baseStart_7368076 baseEnd_7368076 := by
    simpa [prefixWord, tailWord_7368076, baseEnd_7368076] using wordTrace_append hprefix tailTrace_7368076
  have hstable : (prefixWord ++ tailWord_7368076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368076).length < 2 ^ (prefixWord ++ tailWord_7368076).sum := by decide
  have hdescent : baseEnd_7368076 < baseStart_7368076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368103 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7368103 : Nat := 118140960795 + 7368103 * 2 ^ 59
def prefixEnd_7368103 : Nat := 4983230072969 + 3 ^ 40 * 7368103 * 2
def baseEnd_7368103 : Nat := 3783378350834690996827217

theorem tailTrace_7368103 : CollatzResearch.WordTrace tailWord_7368103 prefixEnd_7368103 3783378350834690996827217 := by
  unfold tailWord_7368103
  simp only [CollatzResearch.WordTrace]
  refine ⟨268736794025628677653412963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179157862683752451768941975 268736794025628677653412963)
  ·
    refine ⟨403105191038443016480119445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268736794025628677653412963 403105191038443016480119445)
    ·
      refine ⟨18895555829927016397505599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 403105191038443016480119445 18895555829927016397505599)
      ·
        refine ⟨28343333744890524596258399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18895555829927016397505599 28343333744890524596258399)
        ·
          refine ⟨42515000617335786894387599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28343333744890524596258399 42515000617335786894387599)
          ·
            refine ⟨63772500926003680341581399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42515000617335786894387599 63772500926003680341581399)
            ·
              refine ⟨95658751389005520512372099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63772500926003680341581399 95658751389005520512372099)
              ·
                refine ⟨143488127083508280768558149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95658751389005520512372099 143488127083508280768558149)
                ·
                  refine ⟨26904023828157802644104653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143488127083508280768558149 26904023828157802644104653)
                  ·
                    refine ⟨10089008935559175991539245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26904023828157802644104653 10089008935559175991539245)
                    ·
                      refine ⟨3783378350834690996827217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10089008935559175991539245 3783378350834690996827217)
                      ·
                        rfl

theorem cell23_7368103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7368103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368103 prefixEnd_7368103 := by exact prefixLift 7368103
  have htrace : WordTrace (prefixWord ++ tailWord_7368103) baseStart_7368103 baseEnd_7368103 := by
    simpa [prefixWord, tailWord_7368103, baseEnd_7368103] using wordTrace_append hprefix tailTrace_7368103
  have hstable : (prefixWord ++ tailWord_7368103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368103).length < 2 ^ (prefixWord ++ tailWord_7368103).sum := by decide
  have hdescent : baseEnd_7368103 < baseStart_7368103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368104 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7368104 : Nat := 118140960795 + 7368104 * 2 ^ 59
def prefixEnd_7368104 : Nat := 4983230072969 + 3 ^ 40 * 7368104 * 2
def baseEnd_7368104 : Nat := 3783378864315345492914713

theorem tailTrace_7368104 : CollatzResearch.WordTrace tailWord_7368104 prefixEnd_7368104 3783378864315345492914713 := by
  unfold tailWord_7368104
  simp only [CollatzResearch.WordTrace]
  refine ⟨134368415249312527412099683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179157886999083369882799577 134368415249312527412099683)
  ·
    refine ⟨201552622873968791118149525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134368415249312527412099683 201552622873968791118149525)
    ·
      refine ⟨9447779197217287083663259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201552622873968791118149525 9447779197217287083663259)
      ·
        refine ⟨14171668795825930625494889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447779197217287083663259 14171668795825930625494889)
        ·
          refine ⟨10628751596869447969121167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14171668795825930625494889 10628751596869447969121167)
          ·
            refine ⟨15943127395304171953681751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10628751596869447969121167 15943127395304171953681751)
            ·
              refine ⟨23914691092956257930522627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15943127395304171953681751 23914691092956257930522627)
              ·
                refine ⟨35872036639434386895783941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23914691092956257930522627 35872036639434386895783941)
                ·
                  refine ⟨6726006869893947542959489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35872036639434386895783941 6726006869893947542959489)
                  ·
                    refine ⟨5044505152420460657219617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726006869893947542959489 5044505152420460657219617)
                    ·
                      refine ⟨3783378864315345492914713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044505152420460657219617 3783378864315345492914713)
                      ·
                        rfl

theorem cell23_7368104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7368104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368104 prefixEnd_7368104 := by exact prefixLift 7368104
  have htrace : WordTrace (prefixWord ++ tailWord_7368104) baseStart_7368104 baseEnd_7368104 := by
    simpa [prefixWord, tailWord_7368104, baseEnd_7368104] using wordTrace_append hprefix tailTrace_7368104
  have hstable : (prefixWord ++ tailWord_7368104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368104).length < 2 ^ (prefixWord ++ tailWord_7368104).sum := by decide
  have hdescent : baseEnd_7368104 < baseStart_7368104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368136 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_7368136 : Nat := 118140960795 + 7368136 * 2 ^ 59
def prefixEnd_7368136 : Nat := 4983230072969 + 3 ^ 40 * 7368136 * 2
def baseEnd_7368136 : Nat := 1261131765232096455904855

theorem tailTrace_7368136 : CollatzResearch.WordTrace tailWord_7368136 prefixEnd_7368136 1261131765232096455904855 := by
  unfold tailWord_7368136
  simp only [CollatzResearch.WordTrace]
  refine ⟨134368998817254562144682131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179158665089672749526242841 134368998817254562144682131)
  ·
    refine ⟨201553498225881843217023197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134368998817254562144682131 201553498225881843217023197)
    ·
      refine ⟨75582561834705691206383699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201553498225881843217023197 75582561834705691206383699)
      ·
        refine ⟨113373842752058536809575549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75582561834705691206383699 113373842752058536809575549)
        ·
          refine ⟨42515191032021951303590831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113373842752058536809575549 42515191032021951303590831)
          ·
            refine ⟨63772786548032926955386247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42515191032021951303590831 63772786548032926955386247)
            ·
              refine ⟨95659179822049390433079371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63772786548032926955386247 95659179822049390433079371)
              ·
                refine ⟨143488769733074085649619057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95659179822049390433079371 143488769733074085649619057)
                ·
                  refine ⟨107616577299805564237214293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143488769733074085649619057 107616577299805564237214293)
                  ·
                    refine ⟨1261131765232096455904855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107616577299805564237214293 1261131765232096455904855)
                    ·
                      rfl

theorem cell23_7368136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_7368136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368136 prefixEnd_7368136 := by exact prefixLift 7368136
  have htrace : WordTrace (prefixWord ++ tailWord_7368136) baseStart_7368136 baseEnd_7368136 := by
    simpa [prefixWord, tailWord_7368136, baseEnd_7368136] using wordTrace_append hprefix tailTrace_7368136
  have hstable : (prefixWord ++ tailWord_7368136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368136).length < 2 ^ (prefixWord ++ tailWord_7368136).sum := by decide
  have hdescent : baseEnd_7368136 < baseStart_7368136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368143 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 6, 2]
def baseStart_7368143 : Nat := 118140960795 + 7368143 * 2 ^ 59
def prefixEnd_7368143 : Nat := 4983230072969 + 3 ^ 40 * 7368143 * 2
def baseEnd_7368143 : Nat := 3783398890060870840327033

theorem tailTrace_7368143 : CollatzResearch.WordTrace tailWord_7368143 prefixEnd_7368143 3783398890060870840327033 := by
  unfold tailWord_7368143
  simp only [CollatzResearch.WordTrace]
  refine ⟨268738252945483764484869083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179158835296989176323246055 268738252945483764484869083)
  ·
    refine ⟨403107379418225646727303625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268738252945483764484869083 403107379418225646727303625)
    ·
      refine ⟨302330534563669235045477719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403107379418225646727303625 302330534563669235045477719)
      ·
        refine ⟨453495801845503852568216579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302330534563669235045477719 453495801845503852568216579)
        ·
          refine ⟨680243702768255778852324869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453495801845503852568216579 680243702768255778852324869)
          ·
            refine ⟨127545694269047958534810913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 680243702768255778852324869 127545694269047958534810913)
            ·
              refine ⟨95659270701785968901108185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127545694269047958534810913 95659270701785968901108185)
              ·
                refine ⟨71744453026339476675831139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95659270701785968901108185 71744453026339476675831139)
                ·
                  refine ⟨107616679539509215013746709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71744453026339476675831139 107616679539509215013746709)
                  ·
                    refine ⟨5044531853414494453769377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107616679539509215013746709 5044531853414494453769377)
                    ·
                      refine ⟨3783398890060870840327033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044531853414494453769377 3783398890060870840327033)
                      ·
                        rfl

theorem cell23_7368143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6, 2].length) (baseStart_7368143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368143 prefixEnd_7368143 := by exact prefixLift 7368143
  have htrace : WordTrace (prefixWord ++ tailWord_7368143) baseStart_7368143 baseEnd_7368143 := by
    simpa [prefixWord, tailWord_7368143, baseEnd_7368143] using wordTrace_append hprefix tailTrace_7368143
  have hstable : (prefixWord ++ tailWord_7368143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368143).length < 2 ^ (prefixWord ++ tailWord_7368143).sum := by decide
  have hdescent : baseEnd_7368143 < baseStart_7368143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368243 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 6]
def baseStart_7368243 : Nat := 118140960795 + 7368243 * 2 ^ 59
def prefixEnd_7368243 : Nat := 4983230072969 + 3 ^ 40 * 7368243 * 2
def baseEnd_7368243 : Nat := 1261150079375440149692191

theorem tailTrace_7368243 : CollatzResearch.WordTrace tailWord_7368243 prefixEnd_7368243 1261150079375440149692191 := by
  unfold tailWord_7368243
  simp only [CollatzResearch.WordTrace]
  refine ⟨268741900245121481563509383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179161266830080987709006255 268741900245121481563509383)
  ·
    refine ⟨403112850367682222345264075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268741900245121481563509383 403112850367682222345264075)
    ·
      refine ⟨604669275551523333517896113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403112850367682222345264075 604669275551523333517896113)
      ·
        refine ⟨453501956663642500138422085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604669275551523333517896113 453501956663642500138422085)
        ·
          refine ⟨85031616874432968775954141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453501956663642500138422085 85031616874432968775954141)
          ·
            refine ⟨31886856327912363290982803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85031616874432968775954141 31886856327912363290982803)
            ·
              refine ⟨47830284491868544936474205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31886856327912363290982803 47830284491868544936474205)
              ·
                refine ⟨17936356684450704351177827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47830284491868544936474205 17936356684450704351177827)
                ·
                  refine ⟨26904535026676056526766741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17936356684450704351177827 26904535026676056526766741)
                  ·
                    refine ⟨1261150079375440149692191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26904535026676056526766741 1261150079375440149692191)
                    ·
                      rfl

theorem cell23_7368243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_7368243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368243 prefixEnd_7368243 := by exact prefixLift 7368243
  have htrace : WordTrace (prefixWord ++ tailWord_7368243) baseStart_7368243 baseEnd_7368243 := by
    simpa [prefixWord, tailWord_7368243, baseEnd_7368243] using wordTrace_append hprefix tailTrace_7368243
  have hstable : (prefixWord ++ tailWord_7368243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368243).length < 2 ^ (prefixWord ++ tailWord_7368243).sum := by decide
  have hdescent : baseEnd_7368243 < baseStart_7368243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368250 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_7368250 : Nat := 118140960795 + 7368250 * 2 ^ 59
def prefixEnd_7368250 : Nat := 4983230072969 + 3 ^ 40 * 7368250 * 2
def baseEnd_7368250 : Nat := 3783453832490901921689041

theorem tailTrace_7368250 : CollatzResearch.WordTrace tailWord_7368250 prefixEnd_7368250 3783453832490901921689041 := by
  unfold tailWord_7368250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67185538889024030439753551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179161437037397414506009469 67185538889024030439753551)
  ·
    refine ⟨100778308333536045659630327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67185538889024030439753551 100778308333536045659630327)
    ·
      refine ⟨151167462500304068489445491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100778308333536045659630327 151167462500304068489445491)
      ·
        refine ⟨226751193750456102734168237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151167462500304068489445491 226751193750456102734168237)
        ·
          refine ⟨85031697656421038525313089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226751193750456102734168237 85031697656421038525313089)
          ·
            refine ⟨63773773242315778893984817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85031697656421038525313089 63773773242315778893984817)
            ·
              refine ⟨47830329931736834170488613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63773773242315778893984817 47830329931736834170488613)
              ·
                refine ⟨8968186862200656406966615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47830329931736834170488613 8968186862200656406966615)
                ·
                  refine ⟨13452280293300984610449923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968186862200656406966615 13452280293300984610449923)
                  ·
                    refine ⟨20178420439951476915674885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13452280293300984610449923 20178420439951476915674885)
                    ·
                      refine ⟨3783453832490901921689041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20178420439951476915674885 3783453832490901921689041)
                      ·
                        rfl

theorem cell23_7368250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_7368250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368250 prefixEnd_7368250 := by exact prefixLift 7368250
  have htrace : WordTrace (prefixWord ++ tailWord_7368250) baseStart_7368250 baseEnd_7368250 := by
    simpa [prefixWord, tailWord_7368250, baseEnd_7368250] using wordTrace_append hprefix tailTrace_7368250
  have hstable : (prefixWord ++ tailWord_7368250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368250).length < 2 ^ (prefixWord ++ tailWord_7368250).sum := by decide
  have hdescent : baseEnd_7368250 < baseStart_7368250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368278 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7368278 : Nat := 118140960795 + 7368278 * 2 ^ 59
def prefixEnd_7368278 : Nat := 4983230072969 + 3 ^ 40 * 7368278 * 2
def baseEnd_7368278 : Nat := 3783468209949227812138913

theorem tailTrace_7368278 : CollatzResearch.WordTrace tailWord_7368278 prefixEnd_7368278 3783468209949227812138913 := by
  unfold tailWord_7368278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796448549999667658814593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 179162117866663121694022325 16796448549999667658814593)
  ·
    refine ⟨12597336412499750744110945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16796448549999667658814593 12597336412499750744110945)
    ·
      refine ⟨9448002309374813058083209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12597336412499750744110945 9448002309374813058083209)
      ·
        refine ⟨7086001732031109793562407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448002309374813058083209 7086001732031109793562407)
        ·
          refine ⟨10629002598046664690343611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086001732031109793562407 10629002598046664690343611)
          ·
            refine ⟨15943503897069997035515417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629002598046664690343611 15943503897069997035515417)
            ·
              refine ⟨11957627922802497776636563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15943503897069997035515417 11957627922802497776636563)
              ·
                refine ⟨17936441884203746664954845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11957627922802497776636563 17936441884203746664954845)
                ·
                  refine ⟨6726165706576404999358067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17936441884203746664954845 6726165706576404999358067)
                  ·
                    refine ⟨10089248559864607499037101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726165706576404999358067 10089248559864607499037101)
                    ·
                      refine ⟨3783468209949227812138913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10089248559864607499037101 3783468209949227812138913)
                      ·
                        rfl

theorem cell23_7368278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7368278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368278 prefixEnd_7368278 := by exact prefixLift 7368278
  have htrace : WordTrace (prefixWord ++ tailWord_7368278) baseStart_7368278 baseEnd_7368278 := by
    simpa [prefixWord, tailWord_7368278, baseEnd_7368278] using wordTrace_append hprefix tailTrace_7368278
  have hstable : (prefixWord ++ tailWord_7368278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368278).length < 2 ^ (prefixWord ++ tailWord_7368278).sum := by decide
  have hdescent : baseEnd_7368278 < baseStart_7368278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368284 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7368284 : Nat := 118140960795 + 7368284 * 2 ^ 59
def prefixEnd_7368284 : Nat := 4983230072969 + 3 ^ 40 * 7368284 * 2
def baseEnd_7368284 : Nat := 3783471290833154788663885

theorem tailTrace_7368284 : CollatzResearch.WordTrace tailWord_7368284 prefixEnd_7368284 3783471290833154788663885 := by
  unfold tailWord_7368284
  simp only [CollatzResearch.WordTrace]
  refine ⟨134371697818986472782875953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179162263758648630377167937 134371697818986472782875953)
  ·
    refine ⟨100778773364239854587156965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134371697818986472782875953 100778773364239854587156965)
    ·
      refine ⟨18896020005794972735091931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100778773364239854587156965 18896020005794972735091931)
      ·
        refine ⟨28344030008692459102637897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18896020005794972735091931 28344030008692459102637897)
        ·
          refine ⟨21258022506519344326978423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28344030008692459102637897 21258022506519344326978423)
          ·
            refine ⟨31887033759779016490467635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21258022506519344326978423 31887033759779016490467635)
            ·
              refine ⟨47830550639668524735701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31887033759779016490467635 47830550639668524735701453)
              ·
                refine ⟨17936456489875696775888045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47830550639668524735701453 17936456489875696775888045)
                ·
                  refine ⟨6726171183703386290958017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17936456489875696775888045 6726171183703386290958017)
                  ·
                    refine ⟨5044628387777539718218513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726171183703386290958017 5044628387777539718218513)
                    ·
                      refine ⟨3783471290833154788663885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044628387777539718218513 3783471290833154788663885)
                      ·
                        rfl

theorem cell23_7368284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7368284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368284 prefixEnd_7368284 := by exact prefixLift 7368284
  have htrace : WordTrace (prefixWord ++ tailWord_7368284) baseStart_7368284 baseEnd_7368284 := by
    simpa [prefixWord, tailWord_7368284, baseEnd_7368284] using wordTrace_append hprefix tailTrace_7368284
  have hstable : (prefixWord ++ tailWord_7368284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368284).length < 2 ^ (prefixWord ++ tailWord_7368284).sum := by decide
  have hdescent : baseEnd_7368284 < baseStart_7368284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368313 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7368313 : Nat := 118140960795 + 7368313 * 2 ^ 59
def prefixEnd_7368313 : Nat := 4983230072969 + 3 ^ 40 * 7368313 * 2
def baseEnd_7368313 : Nat := 3783486181772135175201251

theorem tailTrace_7368313 : CollatzResearch.WordTrace tailWord_7368313 prefixEnd_7368313 3783486181772135175201251 := by
  unfold tailWord_7368313
  simp only [CollatzResearch.WordTrace]
  refine ⟨268744453354867883518557593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179162968903245255679038395 268744453354867883518557593)
  ·
    refine ⟨201558340016150912638918195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268744453354867883518557593 201558340016150912638918195)
    ·
      refine ⟨302337510024226368958377293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201558340016150912638918195 302337510024226368958377293)
      ·
        refine ⟨113376566259084888359391485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302337510024226368958377293 113376566259084888359391485)
        ·
          refine ⟨42516212347156833134771807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113376566259084888359391485 42516212347156833134771807)
          ·
            refine ⟨63774318520735249702157711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42516212347156833134771807 63774318520735249702157711)
            ·
              refine ⟨95661477781102874553236567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63774318520735249702157711 95661477781102874553236567)
              ·
                refine ⟨143492216671654311829854851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95661477781102874553236567 143492216671654311829854851)
                ·
                  refine ⟨215238325007481467744782277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143492216671654311829854851 215238325007481467744782277)
                  ·
                    refine ⟨40357185938902775202146677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215238325007481467744782277 40357185938902775202146677)
                    ·
                      refine ⟨3783486181772135175201251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40357185938902775202146677 3783486181772135175201251)
                      ·
                        rfl

theorem cell23_7368313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7368313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368313 prefixEnd_7368313 := by exact prefixLift 7368313
  have htrace : WordTrace (prefixWord ++ tailWord_7368313) baseStart_7368313 baseEnd_7368313 := by
    simpa [prefixWord, tailWord_7368313, baseEnd_7368313] using wordTrace_append hprefix tailTrace_7368313
  have hstable : (prefixWord ++ tailWord_7368313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368313).length < 2 ^ (prefixWord ++ tailWord_7368313).sum := by decide
  have hdescent : baseEnd_7368313 < baseStart_7368313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368317 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_7368317 : Nat := 118140960795 + 7368317 * 2 ^ 59
def prefixEnd_7368317 : Nat := 4983230072969 + 3 ^ 40 * 7368317 * 2
def baseEnd_7368317 : Nat := 3783488235694753159551233

theorem tailTrace_7368317 : CollatzResearch.WordTrace tailWord_7368317 prefixEnd_7368317 3783488235694753159551233 := by
  unfold tailWord_7368317
  simp only [CollatzResearch.WordTrace]
  refine ⟨268744599246853392201703205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179163066164568928134468803 268744599246853392201703205)
  ·
    refine ⟨50389612358785011037819351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268744599246853392201703205 50389612358785011037819351)
    ·
      refine ⟨75584418538177516556729027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50389612358785011037819351 75584418538177516556729027)
      ·
        refine ⟨113376627807266274835093541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75584418538177516556729027 113376627807266274835093541)
        ·
          refine ⟨21258117713862426531580039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113376627807266274835093541 21258117713862426531580039)
          ·
            refine ⟨31887176570793639797370059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21258117713862426531580039 31887176570793639797370059)
            ·
              refine ⟨47830764856190459696055089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31887176570793639797370059 47830764856190459696055089)
              ·
                refine ⟨35873073642142844772041317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47830764856190459696055089 35873073642142844772041317)
                ·
                  refine ⟨6726201307901783394757747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35873073642142844772041317 6726201307901783394757747)
                  ·
                    refine ⟨10089301961852675092136621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726201307901783394757747 10089301961852675092136621)
                    ·
                      refine ⟨3783488235694753159551233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10089301961852675092136621 3783488235694753159551233)
                      ·
                        rfl

theorem cell23_7368317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_7368317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368317 prefixEnd_7368317 := by exact prefixLift 7368317
  have htrace : WordTrace (prefixWord ++ tailWord_7368317) baseStart_7368317 baseEnd_7368317 := by
    simpa [prefixWord, tailWord_7368317, baseEnd_7368317] using wordTrace_append hprefix tailTrace_7368317
  have hstable : (prefixWord ++ tailWord_7368317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368317).length < 2 ^ (prefixWord ++ tailWord_7368317).sum := by decide
  have hdescent : baseEnd_7368317 < baseStart_7368317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368323 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_7368323 : Nat := 118140960795 + 7368323 * 2 ^ 59
def prefixEnd_7368323 : Nat := 4983230072969 + 3 ^ 40 * 7368323 * 2
def baseEnd_7368323 : Nat := 3783491316578680136076205

theorem tailTrace_7368323 : CollatzResearch.WordTrace tailWord_7368323 prefixEnd_7368323 3783491316578680136076205 := by
  unfold tailWord_7368323
  simp only [CollatzResearch.WordTrace]
  refine ⟨268744818084831655226421623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179163212056554436817614415 268744818084831655226421623)
  ·
    refine ⟨403117227127247482839632435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268744818084831655226421623 403117227127247482839632435)
    ·
      refine ⟨604675840690871224259448653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403117227127247482839632435 604675840690871224259448653)
      ·
        refine ⟨226753440259076709097293245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604675840690871224259448653 226753440259076709097293245)
        ·
          refine ⟨85032540097153765911484967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226753440259076709097293245 85032540097153765911484967)
          ·
            refine ⟨127548810145730648867227451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85032540097153765911484967 127548810145730648867227451)
            ·
              refine ⟨191323215218595973300841177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127548810145730648867227451 191323215218595973300841177)
              ·
                refine ⟨143492411413946979975630883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191323215218595973300841177 143492411413946979975630883)
                ·
                  refine ⟨215238617120920469963446325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143492411413946979975630883 215238617120920469963446325)
                  ·
                    refine ⟨20178620355086294059073093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215238617120920469963446325 20178620355086294059073093)
                    ·
                      refine ⟨3783491316578680136076205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20178620355086294059073093 3783491316578680136076205)
                      ·
                        rfl

theorem cell23_7368323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_7368323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368323 prefixEnd_7368323 := by exact prefixLift 7368323
  have htrace : WordTrace (prefixWord ++ tailWord_7368323) baseStart_7368323 baseEnd_7368323 := by
    simpa [prefixWord, tailWord_7368323, baseEnd_7368323] using wordTrace_append hprefix tailTrace_7368323
  have hstable : (prefixWord ++ tailWord_7368323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368323).length < 2 ^ (prefixWord ++ tailWord_7368323).sum := by decide
  have hdescent : baseEnd_7368323 < baseStart_7368323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368351 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7368351 : Nat := 118140960795 + 7368351 * 2 ^ 59
def prefixEnd_7368351 : Nat := 4983230072969 + 3 ^ 40 * 7368351 * 2
def baseEnd_7368351 : Nat := 3783505694037006026526077

theorem tailTrace_7368351 : CollatzResearch.WordTrace tailWord_7368351 prefixEnd_7368351 3783505694037006026526077 := by
  unfold tailWord_7368351
  simp only [CollatzResearch.WordTrace]
  refine ⟨268745839328730216008440907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179163892885820144005627271 268745839328730216008440907)
  ·
    refine ⟨403118758993095324012661361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268745839328730216008440907 403118758993095324012661361)
    ·
      refine ⟨302339069244821493009496021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403118758993095324012661361 302339069244821493009496021)
      ·
        refine ⟨7086071935425503742410063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 302339069244821493009496021 7086071935425503742410063)
        ·
          refine ⟨10629107903138255613615095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086071935425503742410063 10629107903138255613615095)
          ·
            refine ⟨15943661854707383420422643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629107903138255613615095 15943661854707383420422643)
            ·
              refine ⟨23915492782061075130633965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15943661854707383420422643 23915492782061075130633965)
              ·
                refine ⟨8968309793272903173987737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23915492782061075130633965 8968309793272903173987737)
                ·
                  refine ⟨6726232344954677380490803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968309793272903173987737 6726232344954677380490803)
                  ·
                    refine ⟨10089348517432016070736205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726232344954677380490803 10089348517432016070736205)
                    ·
                      refine ⟨3783505694037006026526077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10089348517432016070736205 3783505694037006026526077)
                      ·
                        rfl

theorem cell23_7368351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7368351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368351 prefixEnd_7368351 := by exact prefixLift 7368351
  have htrace : WordTrace (prefixWord ++ tailWord_7368351) baseStart_7368351 baseEnd_7368351 := by
    simpa [prefixWord, tailWord_7368351, baseEnd_7368351] using wordTrace_append hprefix tailTrace_7368351
  have hstable : (prefixWord ++ tailWord_7368351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368351).length < 2 ^ (prefixWord ++ tailWord_7368351).sum := by decide
  have hdescent : baseEnd_7368351 < baseStart_7368351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368386 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7368386 : Nat := 118140960795 + 7368386 * 2 ^ 59
def prefixEnd_7368386 : Nat := 4983230072969 + 3 ^ 40 * 7368386 * 2
def baseEnd_7368386 : Nat := 3783523665859913389588417

theorem tailTrace_7368386 : CollatzResearch.WordTrace tailWord_7368386 prefixEnd_7368386 3783523665859913389588417 := by
  unfold tailWord_7368386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67186778970900854246491253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179164743922402277990643341 67186778970900854246491253)
  ·
    refine ⟨6298760528521955085608555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67186778970900854246491253 6298760528521955085608555)
    ·
      refine ⟨9448140792782932628412833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298760528521955085608555 9448140792782932628412833)
      ·
        refine ⟨7086105594587199471309625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448140792782932628412833 7086105594587199471309625)
        ·
          refine ⟨5314579195940399603482219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7086105594587199471309625 5314579195940399603482219)
          ·
            refine ⟨7971868793910599405223329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314579195940399603482219 7971868793910599405223329)
            ·
              refine ⟨5978901595432949553917497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971868793910599405223329 5978901595432949553917497)
              ·
                refine ⟨4484176196574712165438123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978901595432949553917497 4484176196574712165438123)
                ·
                  refine ⟨6726264294862068248157185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484176196574712165438123 6726264294862068248157185)
                  ·
                    refine ⟨5044698221146551186117889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726264294862068248157185 5044698221146551186117889)
                    ·
                      refine ⟨3783523665859913389588417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044698221146551186117889 3783523665859913389588417)
                      ·
                        rfl

theorem cell23_7368386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7368386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368386 prefixEnd_7368386 := by exact prefixLift 7368386
  have htrace : WordTrace (prefixWord ++ tailWord_7368386) baseStart_7368386 baseEnd_7368386 := by
    simpa [prefixWord, tailWord_7368386, baseEnd_7368386] using wordTrace_append hprefix tailTrace_7368386
  have hstable : (prefixWord ++ tailWord_7368386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368386).length < 2 ^ (prefixWord ++ tailWord_7368386).sum := by decide
  have hdescent : baseEnd_7368386 < baseStart_7368386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_7368403 : Nat := 118140960795 + 7368403 * 2 ^ 59
def prefixEnd_7368403 : Nat := 4983230072969 + 3 ^ 40 * 7368403 * 2
def baseEnd_7368403 : Nat := 3783532395031039823075837

theorem tailTrace_7368403 : CollatzResearch.WordTrace tailWord_7368403 prefixEnd_7368403 3783532395031039823075837 := by
  unfold tailWord_7368403
  simp only [CollatzResearch.WordTrace]
  refine ⟨268747735924541828889333863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179165157283027885926222575 268747735924541828889333863)
  ·
    refine ⟨403121603886812743334000795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268747735924541828889333863 403121603886812743334000795)
    ·
      refine ⟨604682405830219115001001193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403121603886812743334000795 604682405830219115001001193)
      ·
        refine ⟨453511804372664336250750895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604682405830219115001001193 453511804372664336250750895)
        ·
          refine ⟨680267706558996504376126343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453511804372664336250750895 680267706558996504376126343)
          ·
            refine ⟨1020401559838494756564189515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680267706558996504376126343 1020401559838494756564189515)
            ·
              refine ⟨1530602339757742134846284273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020401559838494756564189515 1530602339757742134846284273)
              ·
                refine ⟨1147951754818306601134713205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530602339757742134846284273 1147951754818306601134713205)
                ·
                  refine ⟨107620477014216243856379363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147951754818306601134713205 107620477014216243856379363)
                  ·
                    refine ⟨161430715521324365784569045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107620477014216243856379363 161430715521324365784569045)
                    ·
                      refine ⟨3783532395031039823075837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 161430715521324365784569045 3783532395031039823075837)
                      ·
                        rfl

theorem cell23_7368403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_7368403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368403 prefixEnd_7368403 := by exact prefixLift 7368403
  have htrace : WordTrace (prefixWord ++ tailWord_7368403) baseStart_7368403 baseEnd_7368403 := by
    simpa [prefixWord, tailWord_7368403, baseEnd_7368403] using wordTrace_append hprefix tailTrace_7368403
  have hstable : (prefixWord ++ tailWord_7368403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368403).length < 2 ^ (prefixWord ++ tailWord_7368403).sum := by decide
  have hdescent : baseEnd_7368403 < baseStart_7368403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368447 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 4, 2]
def baseStart_7368447 : Nat := 118140960795 + 7368447 * 2 ^ 59
def prefixEnd_7368447 : Nat := 4983230072969 + 3 ^ 40 * 7368447 * 2
def baseEnd_7368447 : Nat := 3783554988179837650925635

theorem tailTrace_7368447 : CollatzResearch.WordTrace tailWord_7368447 prefixEnd_7368447 3783554988179837650925635 := by
  unfold tailWord_7368447
  simp only [CollatzResearch.WordTrace]
  refine ⟨268749340736382424403935595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179166227157588282935957063 268749340736382424403935595)
  ·
    refine ⟨403124011104573636605903393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268749340736382424403935595 403124011104573636605903393)
    ·
      refine ⟨302343008328430227454427545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403124011104573636605903393 302343008328430227454427545)
      ·
        refine ⟨226757256246322670590820659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302343008328430227454427545 226757256246322670590820659)
        ·
          refine ⟨340135884369484005886230989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226757256246322670590820659 340135884369484005886230989)
          ·
            refine ⟨127550956638556502207336621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340135884369484005886230989 127550956638556502207336621)
            ·
              refine ⟨47831608739458688327751233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127550956638556502207336621 47831608739458688327751233)
              ·
                refine ⟨35873706554594016245813425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47831608739458688327751233 35873706554594016245813425)
                ·
                  refine ⟨26905279915945512184360069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35873706554594016245813425 26905279915945512184360069)
                  ·
                    refine ⟨5044739984239783534567513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26905279915945512184360069 5044739984239783534567513)
                    ·
                      refine ⟨3783554988179837650925635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044739984239783534567513 3783554988179837650925635)
                      ·
                        rfl

theorem cell23_7368447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_7368447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368447 prefixEnd_7368447 := by exact prefixLift 7368447
  have htrace : WordTrace (prefixWord ++ tailWord_7368447) baseStart_7368447 baseEnd_7368447 := by
    simpa [prefixWord, tailWord_7368447, baseEnd_7368447] using wordTrace_append hprefix tailTrace_7368447
  have hstable : (prefixWord ++ tailWord_7368447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368447).length < 2 ^ (prefixWord ++ tailWord_7368447).sum := by decide
  have hdescent : baseEnd_7368447 < baseStart_7368447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368537 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_7368537 : Nat := 118140960795 + 7368537 * 2 ^ 59
def prefixEnd_7368537 : Nat := 4983230072969 + 3 ^ 40 * 7368537 * 2
def baseEnd_7368537 : Nat := 3783601201438742298800221

theorem tailTrace_7368537 : CollatzResearch.WordTrace tailWord_7368537 prefixEnd_7368537 3783601201438742298800221 := by
  unfold tailWord_7368537
  simp only [CollatzResearch.WordTrace]
  refine ⟨268752623306056369774711865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179168415537370913183141243 268752623306056369774711865)
  ·
    refine ⟨201564467479542277331033899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268752623306056369774711865 201564467479542277331033899)
    ·
      refine ⟨302346701219313415996550849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201564467479542277331033899 302346701219313415996550849)
      ·
        refine ⟨226760025914485061997413137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302346701219313415996550849 226760025914485061997413137)
        ·
          refine ⟨170070019435863796498059853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226760025914485061997413137 170070019435863796498059853)
          ·
            refine ⟨63776257288448923686772445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170070019435863796498059853 63776257288448923686772445)
            ·
              refine ⟨23916096483168346382539667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63776257288448923686772445 23916096483168346382539667)
              ·
                refine ⟨35874144724752519573809501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23916096483168346382539667 35874144724752519573809501)
                ·
                  refine ⟨13452804271782194840178563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35874144724752519573809501 13452804271782194840178563)
                  ·
                    refine ⟨20179206407673292260267845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13452804271782194840178563 20179206407673292260267845)
                    ·
                      refine ⟨3783601201438742298800221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20179206407673292260267845 3783601201438742298800221)
                      ·
                        rfl

theorem cell23_7368537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_7368537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368537 prefixEnd_7368537 := by exact prefixLift 7368537
  have htrace : WordTrace (prefixWord ++ tailWord_7368537) baseStart_7368537 baseEnd_7368537 := by
    simpa [prefixWord, tailWord_7368537, baseEnd_7368537] using wordTrace_append hprefix tailTrace_7368537
  have hstable : (prefixWord ++ tailWord_7368537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368537).length < 2 ^ (prefixWord ++ tailWord_7368537).sum := by decide
  have hdescent : baseEnd_7368537 < baseStart_7368537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368605 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_7368605 : Nat := 118140960795 + 7368605 * 2 ^ 59
def prefixEnd_7368605 : Nat := 4983230072969 + 3 ^ 40 * 7368605 * 2
def baseEnd_7368605 : Nat := 3783636118123248032749909

theorem tailTrace_7368605 : CollatzResearch.WordTrace tailWord_7368605 prefixEnd_7368605 3783636118123248032749909 := by
  unfold tailWord_7368605
  simp only [CollatzResearch.WordTrace]
  refine ⟨268755103469810017388187269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179170068979873344925458179 268755103469810017388187269)
  ·
    refine ⟨50391581900589378260285113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268755103469810017388187269 50391581900589378260285113)
    ·
      refine ⟨37793686425442033695213835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50391581900589378260285113 37793686425442033695213835)
      ·
        refine ⟨56690529638163050542820753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37793686425442033695213835 56690529638163050542820753)
        ·
          refine ⟨42517897228622287907115565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56690529638163050542820753 42517897228622287907115565)
          ·
            refine ⟨15944211460733357965168337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42517897228622287907115565 15944211460733357965168337)
            ·
              refine ⟨11958158595550018473876253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15944211460733357965168337 11958158595550018473876253)
              ·
                refine ⟨4484309473331256927703595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11958158595550018473876253 4484309473331256927703595)
                ·
                  refine ⟨6726464209996885391555393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484309473331256927703595 6726464209996885391555393)
                  ·
                    refine ⟨5044848157497664043666545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726464209996885391555393 5044848157497664043666545)
                    ·
                      refine ⟨3783636118123248032749909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044848157497664043666545 3783636118123248032749909)
                      ·
                        rfl

theorem cell23_7368605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_7368605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368605 prefixEnd_7368605 := by exact prefixLift 7368605
  have htrace : WordTrace (prefixWord ++ tailWord_7368605) baseStart_7368605 baseEnd_7368605 := by
    simpa [prefixWord, tailWord_7368605, baseEnd_7368605] using wordTrace_append hprefix tailTrace_7368605
  have hstable : (prefixWord ++ tailWord_7368605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368605).length < 2 ^ (prefixWord ++ tailWord_7368605).sum := by decide
  have hdescent : baseEnd_7368605 < baseStart_7368605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368647 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_7368647 : Nat := 118140960795 + 7368647 * 2 ^ 59
def prefixEnd_7368647 : Nat := 4983230072969 + 3 ^ 40 * 7368647 * 2
def baseEnd_7368647 : Nat := 3783657684310736868424715

theorem tailTrace_7368647 : CollatzResearch.WordTrace tailWord_7368647 prefixEnd_7368647 3783657684310736868424715 := by
  unfold tailWord_7368647
  simp only [CollatzResearch.WordTrace]
  refine ⟨268756635335657858561216195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179171090223771905707477463 268756635335657858561216195)
  ·
    refine ⟨403134953003486787841824293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268756635335657858561216195 403134953003486787841824293)
    ·
      refine ⟨75587803688153772720342055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 403134953003486787841824293 75587803688153772720342055)
      ·
        refine ⟨113381705532230659080513083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75587803688153772720342055 113381705532230659080513083)
        ·
          refine ⟨170072558298345988620769625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113381705532230659080513083 170072558298345988620769625)
          ·
            refine ⟨127554418723759491465577219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170072558298345988620769625 127554418723759491465577219)
            ·
              refine ⟨191331628085639237198365829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127554418723759491465577219 191331628085639237198365829)
              ·
                refine ⟨35874680266057356974693593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191331628085639237198365829 35874680266057356974693593)
                ·
                  refine ⟨26906010199543017731020195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35874680266057356974693593 26906010199543017731020195)
                  ·
                    refine ⟨40359015299314526596530293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26906010199543017731020195 40359015299314526596530293)
                    ·
                      refine ⟨3783657684310736868424715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40359015299314526596530293 3783657684310736868424715)
                      ·
                        rfl

theorem cell23_7368647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_7368647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368647 prefixEnd_7368647 := by exact prefixLift 7368647
  have htrace : WordTrace (prefixWord ++ tailWord_7368647) baseStart_7368647 baseEnd_7368647 := by
    simpa [prefixWord, tailWord_7368647, baseEnd_7368647] using wordTrace_append hprefix tailTrace_7368647
  have hstable : (prefixWord ++ tailWord_7368647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368647).length < 2 ^ (prefixWord ++ tailWord_7368647).sum := by decide
  have hdescent : baseEnd_7368647 < baseStart_7368647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368648 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_7368648 : Nat := 118140960795 + 7368648 * 2 ^ 59
def prefixEnd_7368648 : Nat := 4983230072969 + 3 ^ 40 * 7368648 * 2
def baseEnd_7368648 : Nat := 3783658197791391364512211

theorem tailTrace_7368648 : CollatzResearch.WordTrace tailWord_7368648 prefixEnd_7368648 3783658197791391364512211 := by
  unfold tailWord_7368648
  simp only [CollatzResearch.WordTrace]
  refine ⟨134378335904327117866001299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179171114539102823821335065 134378335904327117866001299)
  ·
    refine ⟨201567503856490676799001949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134378335904327117866001299 201567503856490676799001949)
    ·
      refine ⟨75587813946184003799625731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201567503856490676799001949 75587813946184003799625731)
      ·
        refine ⟨113381720919276005699438597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75587813946184003799625731 113381720919276005699438597)
        ·
          refine ⟨21259072672364251068644737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113381720919276005699438597 21259072672364251068644737)
          ·
            refine ⟨15944304504273188301483553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21259072672364251068644737 15944304504273188301483553)
            ·
              refine ⟨11958228378204891226112665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15944304504273188301483553 11958228378204891226112665)
              ·
                refine ⟨8968671283653668419584499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11958228378204891226112665 8968671283653668419584499)
                ·
                  refine ⟨13453006925480502629376749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968671283653668419584499 13453006925480502629376749)
                  ·
                    refine ⟨5044877597055188486016281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13453006925480502629376749 5044877597055188486016281)
                    ·
                      refine ⟨3783658197791391364512211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044877597055188486016281 3783658197791391364512211)
                      ·
                        rfl

theorem cell23_7368648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_7368648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368648 prefixEnd_7368648 := by exact prefixLift 7368648
  have htrace : WordTrace (prefixWord ++ tailWord_7368648) baseStart_7368648 baseEnd_7368648 := by
    simpa [prefixWord, tailWord_7368648, baseEnd_7368648] using wordTrace_append hprefix tailTrace_7368648
  have hstable : (prefixWord ++ tailWord_7368648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368648).length < 2 ^ (prefixWord ++ tailWord_7368648).sum := by decide
  have hdescent : baseEnd_7368648 < baseStart_7368648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368657 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_7368657 : Nat := 118140960795 + 7368657 * 2 ^ 59
def prefixEnd_7368657 : Nat := 4983230072969 + 3 ^ 40 * 7368657 * 2
def baseEnd_7368657 : Nat := 3783662819117281829299669

theorem tailTrace_7368657 : CollatzResearch.WordTrace tailWord_7368657 prefixEnd_7368657 3783662819117281829299669 := by
  unfold tailWord_7368657
  simp only [CollatzResearch.WordTrace]
  refine ⟨268757000065621630269080225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179171333377081086846053483 268757000065621630269080225)
  ·
    refine ⟨201567750049216222701810169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268757000065621630269080225 201567750049216222701810169)
    ·
      refine ⟨151175812536912167026357627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201567750049216222701810169 151175812536912167026357627)
      ·
        refine ⟨226763718805368250539536441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151175812536912167026357627 226763718805368250539536441)
        ·
          refine ⟨170072789104026187904652331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226763718805368250539536441 170072789104026187904652331)
          ·
            refine ⟨255109183656039281856978497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170072789104026187904652331 255109183656039281856978497)
            ·
              refine ⟨191331887742029461392733873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255109183656039281856978497 191331887742029461392733873)
              ·
                refine ⟨143498915806522096044550405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191331887742029461392733873 143498915806522096044550405)
                ·
                  refine ⟨26906046713722893008353201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143498915806522096044550405 26906046713722893008353201)
                  ·
                    refine ⟨20179535035292169756264901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26906046713722893008353201 20179535035292169756264901)
                    ·
                      refine ⟨3783662819117281829299669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20179535035292169756264901 3783662819117281829299669)
                      ·
                        rfl

theorem cell23_7368657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_7368657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368657 prefixEnd_7368657 := by exact prefixLift 7368657
  have htrace : WordTrace (prefixWord ++ tailWord_7368657) baseStart_7368657 baseEnd_7368657 := by
    simpa [prefixWord, tailWord_7368657, baseEnd_7368657] using wordTrace_append hprefix tailTrace_7368657
  have hstable : (prefixWord ++ tailWord_7368657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368657).length < 2 ^ (prefixWord ++ tailWord_7368657).sum := by decide
  have hdescent : baseEnd_7368657 < baseStart_7368657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368684 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 5]
def baseStart_7368684 : Nat := 118140960795 + 7368684 * 2 ^ 59
def prefixEnd_7368684 : Nat := 4983230072969 + 3 ^ 40 * 7368684 * 2
def baseEnd_7368684 : Nat := 420408520343883691518005

theorem tailTrace_7368684 : CollatzResearch.WordTrace tailWord_7368684 prefixEnd_7368684 420408520343883691518005 := by
  unfold tailWord_7368684
  simp only [CollatzResearch.WordTrace]
  refine ⟨134378992418261906940156553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179171989891015875920208737 134378992418261906940156553)
  ·
    refine ⟨100784244313696430205117415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134378992418261906940156553 100784244313696430205117415)
    ·
      refine ⟨151176366470544645307676123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100784244313696430205117415 151176366470544645307676123)
      ·
        refine ⟨226764549705816967961514185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151176366470544645307676123 226764549705816967961514185)
        ·
          refine ⟨170073412279362725971135639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226764549705816967961514185 170073412279362725971135639)
          ·
            refine ⟨255110118419044088956703459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170073412279362725971135639 255110118419044088956703459)
            ·
              refine ⟨382665177628566133435055189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255110118419044088956703459 382665177628566133435055189)
              ·
                refine ⟨4484357550334759376192053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 382665177628566133435055189 4484357550334759376192053)
                ·
                  refine ⟨420408520343883691518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484357550334759376192053 420408520343883691518005)
                  ·
                    rfl

theorem cell23_7368684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_7368684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368684 prefixEnd_7368684 := by exact prefixLift 7368684
  have htrace : WordTrace (prefixWord ++ tailWord_7368684) baseStart_7368684 baseEnd_7368684 := by
    simpa [prefixWord, tailWord_7368684, baseEnd_7368684] using wordTrace_append hprefix tailTrace_7368684
  have hstable : (prefixWord ++ tailWord_7368684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368684).length < 2 ^ (prefixWord ++ tailWord_7368684).sum := by decide
  have hdescent : baseEnd_7368684 < baseStart_7368684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368704 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2]
def baseStart_7368704 : Nat := 118140960795 + 7368704 * 2 ^ 59
def prefixEnd_7368704 : Nat := 4983230072969 + 3 ^ 40 * 7368704 * 2
def baseEnd_7368704 : Nat := 3783686952708043145411953

theorem tailTrace_7368704 : CollatzResearch.WordTrace tailWord_7368704 prefixEnd_7368704 3783686952708043145411953 := by
  unfold tailWord_7368704
  simp only [CollatzResearch.WordTrace]
  refine ⟨134379357148225678648020583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179172476197634238197360777 134379357148225678648020583)
  ·
    refine ⟨201569035722338517972030875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134379357148225678648020583 201569035722338517972030875)
    ·
      refine ⟨302353553583507776958046313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201569035722338517972030875 302353553583507776958046313)
      ·
        refine ⟨226765165187630832718534735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302353553583507776958046313 226765165187630832718534735)
        ·
          refine ⟨340147747781446249077802103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226765165187630832718534735 340147747781446249077802103)
          ·
            refine ⟨510221621672169373616703155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340147747781446249077802103 510221621672169373616703155)
            ·
              refine ⟨765332432508254060425054733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510221621672169373616703155 765332432508254060425054733)
              ·
                refine ⟨286999662190595272659395525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765332432508254060425054733 286999662190595272659395525)
                ·
                  refine ⟨53812436660736613623636661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286999662190595272659395525 53812436660736613623636661)
                  ·
                    refine ⟨5044915936944057527215937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53812436660736613623636661 5044915936944057527215937)
                    ·
                      refine ⟨3783686952708043145411953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5044915936944057527215937 3783686952708043145411953)
                      ·
                        rfl

theorem cell23_7368704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_7368704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368704 prefixEnd_7368704 := by exact prefixLift 7368704
  have htrace : WordTrace (prefixWord ++ tailWord_7368704) baseStart_7368704 baseEnd_7368704 := by
    simpa [prefixWord, tailWord_7368704, baseEnd_7368704] using wordTrace_append hprefix tailTrace_7368704
  have hstable : (prefixWord ++ tailWord_7368704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368704).length < 2 ^ (prefixWord ++ tailWord_7368704).sum := by decide
  have hdescent : baseEnd_7368704 < baseStart_7368704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368747 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_7368747 : Nat := 118140960795 + 7368747 * 2 ^ 59
def prefixEnd_7368747 : Nat := 4983230072969 + 3 ^ 40 * 7368747 * 2
def baseEnd_7368747 : Nat := 3783709032376186477174255

theorem tailTrace_7368747 : CollatzResearch.WordTrace tailWord_7368747 prefixEnd_7368747 3783709032376186477174255 := by
  unfold tailWord_7368747
  simp only [CollatzResearch.WordTrace]
  refine ⟨268760282635295575639856495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179173521756863717093237663 268760282635295575639856495)
  ·
    refine ⟨403140423952943363459784743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268760282635295575639856495 403140423952943363459784743)
    ·
      refine ⟨604710635929415045189677115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403140423952943363459784743 604710635929415045189677115)
      ·
        refine ⟨907065953894122567784515673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604710635929415045189677115 907065953894122567784515673)
        ·
          refine ⟨680299465420591925838386755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907065953894122567784515673 680299465420591925838386755)
          ·
            refine ⟨1020449198130887888757580133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680299465420591925838386755 1020449198130887888757580133)
            ·
              refine ⟨191334224649541479142046275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1020449198130887888757580133 191334224649541479142046275)
              ·
                refine ⟨287001336974312218713069413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191334224649541479142046275 287001336974312218713069413)
                ·
                  refine ⟨53812750682683541008700515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287001336974312218713069413 53812750682683541008700515)
                  ·
                    refine ⟨80719126024025311513050773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53812750682683541008700515 80719126024025311513050773)
                    ·
                      refine ⟨3783709032376186477174255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80719126024025311513050773 3783709032376186477174255)
                      ·
                        rfl

theorem cell23_7368747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_7368747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368747 prefixEnd_7368747 := by exact prefixLift 7368747
  have htrace : WordTrace (prefixWord ++ tailWord_7368747) baseStart_7368747 baseEnd_7368747 := by
    simpa [prefixWord, tailWord_7368747, baseEnd_7368747] using wordTrace_append hprefix tailTrace_7368747
  have hstable : (prefixWord ++ tailWord_7368747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368747).length < 2 ^ (prefixWord ++ tailWord_7368747).sum := by decide
  have hdescent : baseEnd_7368747 < baseStart_7368747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368787 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 11]
def baseStart_7368787 : Nat := 118140960795 + 7368787 * 2 ^ 59
def prefixEnd_7368787 : Nat := 4983230072969 + 3 ^ 40 * 7368787 * 2
def baseEnd_7368787 : Nat := 1261243190534122106891357

theorem tailTrace_7368787 : CollatzResearch.WordTrace tailWord_7368787 prefixEnd_7368787 1261243190534122106891357 := by
  unfold tailWord_7368787
  simp only [CollatzResearch.WordTrace]
  refine ⟨268761741555150662471312615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179174494370100441647541743 268761741555150662471312615)
  ·
    refine ⟨403142612332725993706968923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268761741555150662471312615 403142612332725993706968923)
    ·
      refine ⟨604713918499088990560453385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403142612332725993706968923 604713918499088990560453385)
      ·
        refine ⟨453535438874316742920340039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604713918499088990560453385 453535438874316742920340039)
        ·
          refine ⟨680303158311475114380510059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453535438874316742920340039 680303158311475114380510059)
          ·
            refine ⟨1020454737467212671570765089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680303158311475114380510059 1020454737467212671570765089)
            ·
              refine ⟨765341053100409503678073817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020454737467212671570765089 765341053100409503678073817)
              ·
                refine ⟨574005789825307127758555363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765341053100409503678073817 574005789825307127758555363)
                ·
                  refine ⟨861008684737960691637833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574005789825307127758555363 861008684737960691637833045)
                  ·
                    refine ⟨1261243190534122106891357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 861008684737960691637833045 1261243190534122106891357)
                    ·
                      rfl

theorem cell23_7368787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_7368787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368787 prefixEnd_7368787 := by exact prefixLift 7368787
  have htrace : WordTrace (prefixWord ++ tailWord_7368787) baseStart_7368787 baseEnd_7368787 := by
    simpa [prefixWord, tailWord_7368787, baseEnd_7368787] using wordTrace_append hprefix tailTrace_7368787
  have hstable : (prefixWord ++ tailWord_7368787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368787).length < 2 ^ (prefixWord ++ tailWord_7368787).sum := by decide
  have hdescent : baseEnd_7368787 < baseStart_7368787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368804 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_7368804 : Nat := 118140960795 + 7368804 * 2 ^ 59
def prefixEnd_7368804 : Nat := 4983230072969 + 3 ^ 40 * 7368804 * 2
def baseEnd_7368804 : Nat := 1261246100257830918053831

theorem tailTrace_7368804 : CollatzResearch.WordTrace tailWord_7368804 prefixEnd_7368804 1261246100257830918053831 := by
  unfold tailWord_7368804
  simp only [CollatzResearch.WordTrace]
  refine ⟨134381180798044537187340733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179174907730726049583120977 134381180798044537187340733)
  ·
    refine ⟨50392942799266701445252775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134381180798044537187340733 50392942799266701445252775)
    ·
      refine ⟨75589414198900052167879163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50392942799266701445252775 75589414198900052167879163)
      ·
        refine ⟨113384121298350078251818745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75589414198900052167879163 113384121298350078251818745)
        ·
          refine ⟨85038090973762558688864059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113384121298350078251818745 85038090973762558688864059)
          ·
            refine ⟨127557136460643838033296089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85038090973762558688864059 127557136460643838033296089)
            ·
              refine ⟨95667852345482878524972067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127557136460643838033296089 95667852345482878524972067)
              ·
                refine ⟨143501778518224317787458101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95667852345482878524972067 143501778518224317787458101)
                ·
                  refine ⟨13453291736083529792574197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143501778518224317787458101 13453291736083529792574197)
                  ·
                    refine ⟨1261246100257830918053831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453291736083529792574197 1261246100257830918053831)
                    ·
                      rfl

theorem cell23_7368804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_7368804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368804 prefixEnd_7368804 := by exact prefixLift 7368804
  have htrace : WordTrace (prefixWord ++ tailWord_7368804) baseStart_7368804 baseEnd_7368804 := by
    simpa [prefixWord, tailWord_7368804, baseEnd_7368804] using wordTrace_append hprefix tailTrace_7368804
  have hstable : (prefixWord ++ tailWord_7368804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368804).length < 2 ^ (prefixWord ++ tailWord_7368804).sum := by decide
  have hdescent : baseEnd_7368804 < baseStart_7368804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368818 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7368818 : Nat := 118140960795 + 7368818 * 2 ^ 59
def prefixEnd_7368818 : Nat := 4983230072969 + 3 ^ 40 * 7368818 * 2
def baseEnd_7368818 : Nat := 3783745489502655699386429

theorem tailTrace_7368818 : CollatzResearch.WordTrace tailWord_7368818 prefixEnd_7368818 3783745489502655699386429 := by
  unfold tailWord_7368818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67190718054509588691422777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179175248145358903177127405 67190718054509588691422777)
  ·
    refine ⟨50393038540882191518567083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67190718054509588691422777 50393038540882191518567083)
    ·
      refine ⟨75589557811323287277850625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50393038540882191518567083 75589557811323287277850625)
      ·
        refine ⟨56692168358492465458387969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75589557811323287277850625 56692168358492465458387969)
        ·
          refine ⟨42519126268869349093790977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56692168358492465458387969 42519126268869349093790977)
          ·
            refine ⟨31889344701652011820343233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42519126268869349093790977 31889344701652011820343233)
            ·
              refine ⟨23917008526239008865257425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31889344701652011820343233 23917008526239008865257425)
              ·
                refine ⟨17937756394679256648943069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23917008526239008865257425 17937756394679256648943069)
                ·
                  refine ⟨6726658648004721243353651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17937756394679256648943069 6726658648004721243353651)
                  ·
                    refine ⟨10089987972007081865030477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726658648004721243353651 10089987972007081865030477)
                    ·
                      refine ⟨3783745489502655699386429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10089987972007081865030477 3783745489502655699386429)
                      ·
                        rfl

theorem cell23_7368818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7368818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368818 prefixEnd_7368818 := by exact prefixLift 7368818
  have htrace : WordTrace (prefixWord ++ tailWord_7368818) baseStart_7368818 baseEnd_7368818 := by
    simpa [prefixWord, tailWord_7368818, baseEnd_7368818] using wordTrace_append hprefix tailTrace_7368818
  have hstable : (prefixWord ++ tailWord_7368818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368818).length < 2 ^ (prefixWord ++ tailWord_7368818).sum := by decide
  have hdescent : baseEnd_7368818 < baseStart_7368818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368835 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 1, 1, 3]
def baseStart_7368835 : Nat := 118140960795 + 7368835 * 2 ^ 59
def prefixEnd_7368835 : Nat := 4983230072969 + 3 ^ 40 * 7368835 * 2
def baseEnd_7368835 : Nat := 3783754218673782132873851

theorem tailTrace_7368835 : CollatzResearch.WordTrace tailWord_7368835 prefixEnd_7368835 3783754218673782132873851 := by
  unfold tailWord_7368835
  simp only [CollatzResearch.WordTrace]
  refine ⟨268763492258976766669059959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179175661505984511112706639 268763492258976766669059959)
  ·
    refine ⟨403145238388465150003589939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268763492258976766669059959 403145238388465150003589939)
    ·
      refine ⟨604717857582697725005384909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403145238388465150003589939 604717857582697725005384909)
      ·
        refine ⟨226769196593511646877019341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604717857582697725005384909 226769196593511646877019341)
        ·
          refine ⟨85038448722566867578882253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226769196593511646877019341 85038448722566867578882253)
          ·
            refine ⟨31889418270962575342080845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85038448722566867578882253 31889418270962575342080845)
            ·
              refine ⟨11958531851610965753280317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31889418270962575342080845 11958531851610965753280317)
              ·
                refine ⟨4484449444354112157480119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11958531851610965753280317 4484449444354112157480119)
                ·
                  refine ⟨6726674166531168236220179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484449444354112157480119 6726674166531168236220179)
                  ·
                    refine ⟨10090011249796752354330269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726674166531168236220179 10090011249796752354330269)
                    ·
                      refine ⟨3783754218673782132873851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090011249796752354330269 3783754218673782132873851)
                      ·
                        rfl

theorem cell23_7368835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_7368835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368835 prefixEnd_7368835 := by exact prefixLift 7368835
  have htrace : WordTrace (prefixWord ++ tailWord_7368835) baseStart_7368835 baseEnd_7368835 := by
    simpa [prefixWord, tailWord_7368835, baseEnd_7368835] using wordTrace_append hprefix tailTrace_7368835
  have hstable : (prefixWord ++ tailWord_7368835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368835).length < 2 ^ (prefixWord ++ tailWord_7368835).sum := by decide
  have hdescent : baseEnd_7368835 < baseStart_7368835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368841 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_7368841 : Nat := 118140960795 + 7368841 * 2 ^ 59
def prefixEnd_7368841 : Nat := 4983230072969 + 3 ^ 40 * 7368841 * 2
def baseEnd_7368841 : Nat := 3783757299557709109398823

theorem tailTrace_7368841 : CollatzResearch.WordTrace tailWord_7368841 prefixEnd_7368841 3783757299557709109398823 := by
  unfold tailWord_7368841
  simp only [CollatzResearch.WordTrace]
  refine ⟨268763711096955029693778377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179175807397970019795852251 268763711096955029693778377)
  ·
    refine ⟨201572783322716272270333783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268763711096955029693778377 201572783322716272270333783)
    ·
      refine ⟨302359174984074408405500675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201572783322716272270333783 302359174984074408405500675)
      ·
        refine ⟨453538762476111612608251013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302359174984074408405500675 453538762476111612608251013)
        ·
          refine ⟨85038517964270927364047065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453538762476111612608251013 85038517964270927364047065)
          ·
            refine ⟨63778888473203195523035299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85038517964270927364047065 63778888473203195523035299)
            ·
              refine ⟨95668332709804793284552949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63778888473203195523035299 95668332709804793284552949)
              ·
                refine ⟨8968906191544199370426839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95668332709804793284552949 8968906191544199370426839)
                ·
                  refine ⟨13453359287316299055640259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968906191544199370426839 13453359287316299055640259)
                  ·
                    refine ⟨20180038930974448583460389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13453359287316299055640259 20180038930974448583460389)
                    ·
                      refine ⟨3783757299557709109398823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20180038930974448583460389 3783757299557709109398823)
                      ·
                        rfl

theorem cell23_7368841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_7368841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368841 prefixEnd_7368841 := by exact prefixLift 7368841
  have htrace : WordTrace (prefixWord ++ tailWord_7368841) baseStart_7368841 baseEnd_7368841 := by
    simpa [prefixWord, tailWord_7368841, baseEnd_7368841] using wordTrace_append hprefix tailTrace_7368841
  have hstable : (prefixWord ++ tailWord_7368841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368841).length < 2 ^ (prefixWord ++ tailWord_7368841).sum := by decide
  have hdescent : baseEnd_7368841 < baseStart_7368841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368851 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 2, 4]
def baseStart_7368851 : Nat := 118140960795 + 7368851 * 2 ^ 59
def prefixEnd_7368851 : Nat := 4983230072969 + 3 ^ 40 * 7368851 * 2
def baseEnd_7368851 : Nat := 1261254144788084690091259

theorem tailTrace_7368851 : CollatzResearch.WordTrace tailWord_7368851 prefixEnd_7368851 1261254144788084690091259 := by
  unfold tailWord_7368851
  simp only [CollatzResearch.WordTrace]
  refine ⟨268764075826918801401642407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179176050551279200934428271 268764075826918801401642407)
  ·
    refine ⟨403146113740378202102463611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268764075826918801401642407 403146113740378202102463611)
    ·
      refine ⟨604719170610567303153695417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403146113740378202102463611 604719170610567303153695417)
      ·
        refine ⟨453539377957925477365271563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604719170610567303153695417 453539377957925477365271563)
        ·
          refine ⟨680309066936888216047907345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453539377957925477365271563 680309066936888216047907345)
          ·
            refine ⟨510231800202666162035930509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680309066936888216047907345 510231800202666162035930509)
            ·
              refine ⟨191336925075999810763473941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510231800202666162035930509 191336925075999810763473941)
              ·
                refine ⟨8968918362937491129537841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191336925075999810763473941 8968918362937491129537841)
                ·
                  refine ⟨6726688772203118347153381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968918362937491129537841 6726688772203118347153381)
                  ·
                    refine ⟨1261254144788084690091259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726688772203118347153381 1261254144788084690091259)
                    ·
                      rfl

theorem cell23_7368851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 4].length) (baseStart_7368851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368851 prefixEnd_7368851 := by exact prefixLift 7368851
  have htrace : WordTrace (prefixWord ++ tailWord_7368851) baseStart_7368851 baseEnd_7368851 := by
    simpa [prefixWord, tailWord_7368851, baseEnd_7368851] using wordTrace_append hprefix tailTrace_7368851
  have hstable : (prefixWord ++ tailWord_7368851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368851).length < 2 ^ (prefixWord ++ tailWord_7368851).sum := by decide
  have hdescent : baseEnd_7368851 < baseStart_7368851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368861 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_7368861 : Nat := 118140960795 + 7368861 * 2 ^ 59
def prefixEnd_7368861 : Nat := 4983230072969 + 3 ^ 40 * 7368861 * 2
def baseEnd_7368861 : Nat := 3783767569170799031148731

theorem tailTrace_7368861 : CollatzResearch.WordTrace tailWord_7368861 prefixEnd_7368861 3783767569170799031148731 := by
  unfold tailWord_7368861
  simp only [CollatzResearch.WordTrace]
  refine ⟨268764440556882573109506437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179176293704588382073004291 268764440556882573109506437)
  ·
    refine ⟨50393332604415482458032457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268764440556882573109506437 50393332604415482458032457)
    ·
      refine ⟨37794999453311611843524343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50393332604415482458032457 37794999453311611843524343)
      ·
        refine ⟨56692499179967417765286515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37794999453311611843524343 56692499179967417765286515)
        ·
          refine ⟨85038748769951126647929773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56692499179967417765286515 85038748769951126647929773)
          ·
            refine ⟨31889530788731672492973665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85038748769951126647929773 31889530788731672492973665)
            ·
              refine ⟨23917148091548754369730249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31889530788731672492973665 23917148091548754369730249)
              ·
                refine ⟨17937861068661565777297687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23917148091548754369730249 17937861068661565777297687)
                ·
                  refine ⟨26906791602992348665946531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17937861068661565777297687 26906791602992348665946531)
                  ·
                    refine ⟨40360187404488522998919797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26906791602992348665946531 40360187404488522998919797)
                    ·
                      refine ⟨3783767569170799031148731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40360187404488522998919797 3783767569170799031148731)
                      ·
                        rfl

theorem cell23_7368861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_7368861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368861 prefixEnd_7368861 := by exact prefixLift 7368861
  have htrace : WordTrace (prefixWord ++ tailWord_7368861) baseStart_7368861 baseEnd_7368861 := by
    simpa [prefixWord, tailWord_7368861, baseEnd_7368861] using wordTrace_append hprefix tailTrace_7368861
  have hstable : (prefixWord ++ tailWord_7368861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368861).length < 2 ^ (prefixWord ++ tailWord_7368861).sum := by decide
  have hdescent : baseEnd_7368861 < baseStart_7368861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368864 : List Nat := [2, 1, 1, 4, 2, 2, 1, 10]
def baseStart_7368864 : Nat := 118140960795 + 7368864 * 2 ^ 59
def prefixEnd_7368864 : Nat := 4983230072969 + 3 ^ 40 * 7368864 * 2
def baseEnd_7368864 : Nat := 140139596652324537755971

theorem tailTrace_7368864 : CollatzResearch.WordTrace tailWord_7368864 prefixEnd_7368864 140139596652324537755971 := by
  unfold tailWord_7368864
  simp only [CollatzResearch.WordTrace]
  refine ⟨134382274987935852310932823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179176366650581136414577097 134382274987935852310932823)
  ·
    refine ⟨201573412481903778466399235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134382274987935852310932823 201573412481903778466399235)
    ·
      refine ⟨302360118722855667699598853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201573412481903778466399235 302360118722855667699598853)
      ·
        refine ⟨56692522260535437693674785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302360118722855667699598853 56692522260535437693674785)
        ·
          refine ⟨42519391695401578270256089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56692522260535437693674785 42519391695401578270256089)
          ·
            refine ⟨31889543771551183702692067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42519391695401578270256089 31889543771551183702692067)
            ·
              refine ⟨47834315657326775554038101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31889543771551183702692067 47834315657326775554038101)
              ·
                refine ⟨140139596652324537755971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47834315657326775554038101 140139596652324537755971)
                ·
                  rfl

theorem cell23_7368864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_7368864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368864 prefixEnd_7368864 := by exact prefixLift 7368864
  have htrace : WordTrace (prefixWord ++ tailWord_7368864) baseStart_7368864 baseEnd_7368864 := by
    simpa [prefixWord, tailWord_7368864, baseEnd_7368864] using wordTrace_append hprefix tailTrace_7368864
  have hstable : (prefixWord ++ tailWord_7368864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368864).length < 2 ^ (prefixWord ++ tailWord_7368864).sum := by decide
  have hdescent : baseEnd_7368864 < baseStart_7368864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368891 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3]
def baseStart_7368891 : Nat := 118140960795 + 7368891 * 2 ^ 59
def prefixEnd_7368891 : Nat := 4983230072969 + 3 ^ 40 * 7368891 * 2
def baseEnd_7368891 : Nat := 3783782973590433913773593

theorem tailTrace_7368891 : CollatzResearch.WordTrace tailWord_7368891 prefixEnd_7368891 3783782973590433913773593 := by
  unfold tailWord_7368891
  simp only [CollatzResearch.WordTrace]
  refine ⟨268765534746773888233098527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179177023164515925488732351 268765534746773888233098527)
  ·
    refine ⟨403148302120160832349647791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268765534746773888233098527 403148302120160832349647791)
    ·
      refine ⟨604722453180241248524471687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403148302120160832349647791 604722453180241248524471687)
      ·
        refine ⟨907083679770361872786707531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604722453180241248524471687 907083679770361872786707531)
        ·
          refine ⟨1360625519655542809180061297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907083679770361872786707531 1360625519655542809180061297)
          ·
            refine ⟨1020469139741657106885045973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360625519655542809180061297 1020469139741657106885045973)
            ·
              refine ⟨23917245462695088442618265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1020469139741657106885045973 23917245462695088442618265)
              ·
                refine ⟨17937934097021316331963699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23917245462695088442618265 17937934097021316331963699)
                ·
                  refine ⟨26906901145531974497945549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17937934097021316331963699 26906901145531974497945549)
                  ·
                    refine ⟨10090087929574490436729581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26906901145531974497945549 10090087929574490436729581)
                    ·
                      refine ⟨3783782973590433913773593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090087929574490436729581 3783782973590433913773593)
                      ·
                        rfl

theorem cell23_7368891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].length) (baseStart_7368891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368891 prefixEnd_7368891 := by exact prefixLift 7368891
  have htrace : WordTrace (prefixWord ++ tailWord_7368891) baseStart_7368891 baseEnd_7368891 := by
    simpa [prefixWord, tailWord_7368891, baseEnd_7368891] using wordTrace_append hprefix tailTrace_7368891
  have hstable : (prefixWord ++ tailWord_7368891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368891).length < 2 ^ (prefixWord ++ tailWord_7368891).sum := by decide
  have hdescent : baseEnd_7368891 < baseStart_7368891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368898 : List Nat := [3, 5, 1, 1, 1, 12]
def baseStart_7368898 : Nat := 118140960795 + 7368898 * 2 ^ 59
def prefixEnd_7368898 : Nat := 4983230072969 + 3 ^ 40 * 7368898 * 2
def baseEnd_7368898 : Nat := 15571138139732573606527

theorem tailTrace_7368898 : CollatzResearch.WordTrace tailWord_7368898 prefixEnd_7368898 15571138139732573606527 := by
  unfold tailWord_7368898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67191447514437132107150837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179177193371832352285735565 67191447514437132107150837)
  ·
    refine ⟨6299198204478481135045391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67191447514437132107150837 6299198204478481135045391)
    ·
      refine ⟨9448797306717721702568087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299198204478481135045391 9448797306717721702568087)
      ·
        refine ⟨14173195960076582553852131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448797306717721702568087 14173195960076582553852131)
        ·
          refine ⟨21259793940114873830778197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173195960076582553852131 21259793940114873830778197)
          ·
            refine ⟨15571138139732573606527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21259793940114873830778197 15571138139732573606527)
            ·
              rfl

theorem cell23_7368898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 12].length) (baseStart_7368898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368898 prefixEnd_7368898 := by exact prefixLift 7368898
  have htrace : WordTrace (prefixWord ++ tailWord_7368898) baseStart_7368898 baseEnd_7368898 := by
    simpa [prefixWord, tailWord_7368898, baseEnd_7368898] using wordTrace_append hprefix tailTrace_7368898
  have hstable : (prefixWord ++ tailWord_7368898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368898).length < 2 ^ (prefixWord ++ tailWord_7368898).sum := by decide
  have hdescent : baseEnd_7368898 < baseStart_7368898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368925 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7368925 : Nat := 118140960795 + 7368925 * 2 ^ 59
def prefixEnd_7368925 : Nat := 4983230072969 + 3 ^ 40 * 7368925 * 2
def baseEnd_7368925 : Nat := 3783800431932686780748437

theorem tailTrace_7368925 : CollatzResearch.WordTrace tailWord_7368925 prefixEnd_7368925 3783800431932686780748437 := by
  unfold tailWord_7368925
  simp only [CollatzResearch.WordTrace]
  refine ⟨268766774828650712039836229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179177849885767141359890819 268766774828650712039836229)
  ·
    refine ⟨50393770280372008507469293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268766774828650712039836229 50393770280372008507469293)
    ·
      refine ⟨18897663855139503190300985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50393770280372008507469293 18897663855139503190300985)
      ·
        refine ⟨14173247891354627392725739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18897663855139503190300985 14173247891354627392725739)
        ·
          refine ⟨21259871837031941089088609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173247891354627392725739 21259871837031941089088609)
          ·
            refine ⟨15944903877773955816816457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21259871837031941089088609 15944903877773955816816457)
            ·
              refine ⟨11958677908330466862612343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15944903877773955816816457 11958677908330466862612343)
              ·
                refine ⟨17938016862495700293918515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11958677908330466862612343 17938016862495700293918515)
                ·
                  refine ⟨26907025293743550440877773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17938016862495700293918515 26907025293743550440877773)
                  ·
                    refine ⟨10090134485153831415329165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26907025293743550440877773 10090134485153831415329165)
                    ·
                      refine ⟨3783800431932686780748437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090134485153831415329165 3783800431932686780748437)
                      ·
                        rfl

theorem cell23_7368925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7368925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368925 prefixEnd_7368925 := by exact prefixLift 7368925
  have htrace : WordTrace (prefixWord ++ tailWord_7368925) baseStart_7368925 baseEnd_7368925 := by
    simpa [prefixWord, tailWord_7368925, baseEnd_7368925] using wordTrace_append hprefix tailTrace_7368925
  have hstable : (prefixWord ++ tailWord_7368925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368925).length < 2 ^ (prefixWord ++ tailWord_7368925).sum := by decide
  have hdescent : baseEnd_7368925 < baseStart_7368925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368935 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7368935 : Nat := 118140960795 + 7368935 * 2 ^ 59
def prefixEnd_7368935 : Nat := 4983230072969 + 3 ^ 40 * 7368935 * 2
def baseEnd_7368935 : Nat := 3783805566739231741623391

theorem tailTrace_7368935 : CollatzResearch.WordTrace tailWord_7368935 prefixEnd_7368935 3783805566739231741623391 := by
  unfold tailWord_7368935
  simp only [CollatzResearch.WordTrace]
  refine ⟨268767139558614483747700259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179178093039076322498466839 268767139558614483747700259)
  ·
    refine ⟨403150709337921725621550389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268767139558614483747700259 403150709337921725621550389)
    ·
      refine ⟨37795379000430161777020349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 403150709337921725621550389 37795379000430161777020349)
      ·
        refine ⟨14173267125161310666382631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37795379000430161777020349 14173267125161310666382631)
        ·
          refine ⟨21259900687741965999573947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173267125161310666382631 21259900687741965999573947)
          ·
            refine ⟨31889851031612948999360921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21259900687741965999573947 31889851031612948999360921)
            ·
              refine ⟨23917388273709711749520691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31889851031612948999360921 23917388273709711749520691)
              ·
                refine ⟨35876082410564567624281037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23917388273709711749520691 35876082410564567624281037)
                ·
                  refine ⟨13453530903961712859105389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35876082410564567624281037 13453530903961712859105389)
                  ·
                    refine ⟨5045074088985642322164521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13453530903961712859105389 5045074088985642322164521)
                    ·
                      refine ⟨3783805566739231741623391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045074088985642322164521 3783805566739231741623391)
                      ·
                        rfl

theorem cell23_7368935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7368935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368935 prefixEnd_7368935 := by exact prefixLift 7368935
  have htrace : WordTrace (prefixWord ++ tailWord_7368935) baseStart_7368935 baseEnd_7368935 := by
    simpa [prefixWord, tailWord_7368935, baseEnd_7368935] using wordTrace_append hprefix tailTrace_7368935
  have hstable : (prefixWord ++ tailWord_7368935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368935).length < 2 ^ (prefixWord ++ tailWord_7368935).sum := by decide
  have hdescent : baseEnd_7368935 < baseStart_7368935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368961 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_7368961 : Nat := 118140960795 + 7368961 * 2 ^ 59
def prefixEnd_7368961 : Nat := 4983230072969 + 3 ^ 40 * 7368961 * 2
def baseEnd_7368961 : Nat := 3783818917236248639898271

theorem tailTrace_7368961 : CollatzResearch.WordTrace tailWord_7368961 prefixEnd_7368961 3783818917236248639898271 := by
  unfold tailWord_7368961
  simp only [CollatzResearch.WordTrace]
  refine ⟨268768087856520290188146737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179178725237680193458764491 268768087856520290188146737)
  ·
    refine ⟨201576065892390217641110053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268768087856520290188146737 201576065892390217641110053)
    ·
      refine ⟨37795512354823165807708135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201576065892390217641110053 37795512354823165807708135)
      ·
        refine ⟨56693268532234748711562203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37795512354823165807708135 56693268532234748711562203)
        ·
          refine ⟨85039902798352123067343305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56693268532234748711562203 85039902798352123067343305)
          ·
            refine ⟨63779927098764092300507479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85039902798352123067343305 63779927098764092300507479)
            ·
              refine ⟨95669890648146138450761219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63779927098764092300507479 95669890648146138450761219)
              ·
                refine ⟨143504835972219207676141829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95669890648146138450761219 143504835972219207676141829)
                ·
                  refine ⟨26907156744791101439276593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143504835972219207676141829 26907156744791101439276593)
                  ·
                    refine ⟨20180367558593326079457445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26907156744791101439276593 20180367558593326079457445)
                    ·
                      refine ⟨3783818917236248639898271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20180367558593326079457445 3783818917236248639898271)
                      ·
                        rfl

theorem cell23_7368961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_7368961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368961 prefixEnd_7368961 := by exact prefixLift 7368961
  have htrace : WordTrace (prefixWord ++ tailWord_7368961) baseStart_7368961 baseEnd_7368961 := by
    simpa [prefixWord, tailWord_7368961, baseEnd_7368961] using wordTrace_append hprefix tailTrace_7368961
  have hstable : (prefixWord ++ tailWord_7368961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368961).length < 2 ^ (prefixWord ++ tailWord_7368961).sum := by decide
  have hdescent : baseEnd_7368961 < baseStart_7368961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368965 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_7368965 : Nat := 118140960795 + 7368965 * 2 ^ 59
def prefixEnd_7368965 : Nat := 4983230072969 + 3 ^ 40 * 7368965 * 2
def baseEnd_7368965 : Nat := 3783820971158866624248253

theorem tailTrace_7368965 : CollatzResearch.WordTrace tailWord_7368965 prefixEnd_7368965 3783820971158866624248253 := by
  unfold tailWord_7368965
  simp only [CollatzResearch.WordTrace]
  refine ⟨268768233748505798871292349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179178822499003865914194899 268768233748505798871292349)
  ·
    refine ⟨100788087655689674576734631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268768233748505798871292349 100788087655689674576734631)
    ·
      refine ⟨151182131483534511865101947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100788087655689674576734631 151182131483534511865101947)
      ·
        refine ⟨226773197225301767797652921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151182131483534511865101947 226773197225301767797652921)
        ·
          refine ⟨170079897918976325848239691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226773197225301767797652921 170079897918976325848239691)
          ·
            refine ⟨255119846878464488772359537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170079897918976325848239691 255119846878464488772359537)
            ·
              refine ⟨191339885158848366579269653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255119846878464488772359537 191339885158848366579269653)
              ·
                refine ⟨8969057116821017183403265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191339885158848366579269653 8969057116821017183403265)
                ·
                  refine ⟨6726792837615762887552449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8969057116821017183403265 6726792837615762887552449)
                  ·
                    refine ⟨5045094628211822165664337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726792837615762887552449 5045094628211822165664337)
                    ·
                      refine ⟨3783820971158866624248253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045094628211822165664337 3783820971158866624248253)
                      ·
                        rfl

theorem cell23_7368965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_7368965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368965 prefixEnd_7368965 := by exact prefixLift 7368965
  have htrace : WordTrace (prefixWord ++ tailWord_7368965) baseStart_7368965 baseEnd_7368965 := by
    simpa [prefixWord, tailWord_7368965, baseEnd_7368965] using wordTrace_append hprefix tailTrace_7368965
  have hstable : (prefixWord ++ tailWord_7368965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368965).length < 2 ^ (prefixWord ++ tailWord_7368965).sum := by decide
  have hdescent : baseEnd_7368965 < baseStart_7368965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7368971 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 7]
def baseStart_7368971 : Nat := 118140960795 + 7368971 * 2 ^ 59
def prefixEnd_7368971 : Nat := 4983230072969 + 3 ^ 40 * 7368971 * 2
def baseEnd_7368971 : Nat := 420424894671421511197025

theorem tailTrace_7368971 : CollatzResearch.WordTrace tailWord_7368971 prefixEnd_7368971 420424894671421511197025 := by
  unfold tailWord_7368971
  simp only [CollatzResearch.WordTrace]
  refine ⟨268768452586484061896010767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179178968390989374597340511 268768452586484061896010767)
  ·
    refine ⟨403152678879726092844016151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268768452586484061896010767 403152678879726092844016151)
    ·
      refine ⟨604729018319589139266024227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403152678879726092844016151 604729018319589139266024227)
      ·
        refine ⟨907093527479383708899036341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604729018319589139266024227 907093527479383708899036341)
        ·
          refine ⟨85040018201192222709284657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 907093527479383708899036341 85040018201192222709284657)
          ·
            refine ⟨63780013650894167031963493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85040018201192222709284657 63780013650894167031963493)
            ·
              refine ⟨11958752559542656318493155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63780013650894167031963493 11958752559542656318493155)
              ·
                refine ⟨17938128839313984477739733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11958752559542656318493155 17938128839313984477739733)
                ·
                  refine ⟨420424894671421511197025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17938128839313984477739733 420424894671421511197025)
                  ·
                    rfl

theorem cell23_7368971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 7].length) (baseStart_7368971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7368971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7368971 prefixEnd_7368971 := by exact prefixLift 7368971
  have htrace : WordTrace (prefixWord ++ tailWord_7368971) baseStart_7368971 baseEnd_7368971 := by
    simpa [prefixWord, tailWord_7368971, baseEnd_7368971] using wordTrace_append hprefix tailTrace_7368971
  have hstable : (prefixWord ++ tailWord_7368971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7368971).length < 2 ^ (prefixWord ++ tailWord_7368971).sum := by decide
  have hdescent : baseEnd_7368971 < baseStart_7368971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7368971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369011 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_7369011 : Nat := 118140960795 + 7369011 * 2 ^ 59
def prefixEnd_7369011 : Nat := 4983230072969 + 3 ^ 40 * 7369011 * 2
def baseEnd_7369011 : Nat := 3783844591268973444273041

theorem tailTrace_7369011 : CollatzResearch.WordTrace tailWord_7369011 prefixEnd_7369011 3783844591268973444273041 := by
  unfold tailWord_7369011
  simp only [CollatzResearch.WordTrace]
  refine ⟨268769911506339148727466887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179179941004226099151644591 268769911506339148727466887)
  ·
    refine ⟨403154867259508723091200331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268769911506339148727466887 403154867259508723091200331)
    ·
      refine ⟨604732300889263084636800497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403154867259508723091200331 604732300889263084636800497)
      ·
        refine ⟨453549225666947313477600373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604732300889263084636800497 453549225666947313477600373)
        ·
          refine ⟨42520239906276310638525035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453549225666947313477600373 42520239906276310638525035)
          ·
            refine ⟨63780359859414465957787553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42520239906276310638525035 63780359859414465957787553)
            ·
              refine ⟨47835269894560849468340665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63780359859414465957787553 47835269894560849468340665)
              ·
                refine ⟨35876452420920637101255499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47835269894560849468340665 35876452420920637101255499)
                ·
                  refine ⟨53814678631380955651883249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35876452420920637101255499 53814678631380955651883249)
                  ·
                    refine ⟨40361008973535716738912437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53814678631380955651883249 40361008973535716738912437)
                    ·
                      refine ⟨3783844591268973444273041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40361008973535716738912437 3783844591268973444273041)
                      ·
                        rfl

theorem cell23_7369011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_7369011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369011 prefixEnd_7369011 := by exact prefixLift 7369011
  have htrace : WordTrace (prefixWord ++ tailWord_7369011) baseStart_7369011 baseEnd_7369011 := by
    simpa [prefixWord, tailWord_7369011, baseEnd_7369011] using wordTrace_append hprefix tailTrace_7369011
  have hstable : (prefixWord ++ tailWord_7369011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369011).length < 2 ^ (prefixWord ++ tailWord_7369011).sum := by decide
  have hdescent : baseEnd_7369011 < baseStart_7369011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369018 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_7369018 : Nat := 118140960795 + 7369018 * 2 ^ 59
def prefixEnd_7369018 : Nat := 4983230072969 + 3 ^ 40 * 7369018 * 2
def baseEnd_7369018 : Nat := 1261282728544518305628503

theorem tailTrace_7369018 : CollatzResearch.WordTrace tailWord_7369018 prefixEnd_7369018 1261282728544518305628503 := by
  unfold tailWord_7369018
  simp only [CollatzResearch.WordTrace]
  refine ⟨67192541704328447230742927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179180111211542525948647805 67192541704328447230742927)
  ·
    refine ⟨100788812556492670846114391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67192541704328447230742927 100788812556492670846114391)
    ·
      refine ⟨151183218834739006269171587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100788812556492670846114391 151183218834739006269171587)
      ·
        refine ⟨226774828252108509403757381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151183218834739006269171587 226774828252108509403757381)
        ·
          refine ⟨42520280297270345513204509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226774828252108509403757381 42520280297270345513204509)
          ·
            refine ⟨15945105111476379567451691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42520280297270345513204509 15945105111476379567451691)
            ·
              refine ⟨23917657667214569351177537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945105111476379567451691 23917657667214569351177537)
              ·
                refine ⟨17938243250410927013383153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23917657667214569351177537 17938243250410927013383153)
                ·
                  refine ⟨13453682437808195260037365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17938243250410927013383153 13453682437808195260037365)
                  ·
                    refine ⟨1261282728544518305628503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453682437808195260037365 1261282728544518305628503)
                    ·
                      rfl

theorem cell23_7369018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_7369018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369018 prefixEnd_7369018 := by exact prefixLift 7369018
  have htrace : WordTrace (prefixWord ++ tailWord_7369018) baseStart_7369018 baseEnd_7369018 := by
    simpa [prefixWord, tailWord_7369018, baseEnd_7369018] using wordTrace_append hprefix tailTrace_7369018
  have hstable : (prefixWord ++ tailWord_7369018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369018).length < 2 ^ (prefixWord ++ tailWord_7369018).sum := by decide
  have hdescent : baseEnd_7369018 < baseStart_7369018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369022 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_7369022 : Nat := 118140960795 + 7369022 * 2 ^ 59
def prefixEnd_7369022 : Nat := 4983230072969 + 3 ^ 40 * 7369022 * 2
def baseEnd_7369022 : Nat := 420427804395130322359499

theorem tailTrace_7369022 : CollatzResearch.WordTrace tailWord_7369022 prefixEnd_7369022 420427804395130322359499 := by
  unfold tailWord_7369022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33596289088662412200764665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179180208472866198404078213 33596289088662412200764665)
  ·
    refine ⟨25197216816496809150573499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33596289088662412200764665 25197216816496809150573499)
    ·
      refine ⟨37795825224745213725860249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25197216816496809150573499 37795825224745213725860249)
      ·
        refine ⟨28346868918558910294395187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37795825224745213725860249 28346868918558910294395187)
        ·
          refine ⟨42520303377838365441592781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28346868918558910294395187 42520303377838365441592781)
          ·
            refine ⟨15945113766689387040597293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42520303377838365441592781 15945113766689387040597293)
            ·
              refine ⟨5979417662508520140223985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15945113766689387040597293 5979417662508520140223985)
              ·
                refine ⟨4484563246881390105167989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979417662508520140223985 4484563246881390105167989)
                ·
                  refine ⟨420427804395130322359499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484563246881390105167989 420427804395130322359499)
                  ·
                    rfl

theorem cell23_7369022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_7369022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369022 prefixEnd_7369022 := by exact prefixLift 7369022
  have htrace : WordTrace (prefixWord ++ tailWord_7369022) baseStart_7369022 baseEnd_7369022 := by
    simpa [prefixWord, tailWord_7369022, baseEnd_7369022] using wordTrace_append hprefix tailTrace_7369022
  have hstable : (prefixWord ++ tailWord_7369022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369022).length < 2 ^ (prefixWord ++ tailWord_7369022).sum := by decide
  have hdescent : baseEnd_7369022 < baseStart_7369022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369052 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7369052 : Nat := 118140960795 + 7369052 * 2 ^ 59
def prefixEnd_7369052 : Nat := 4983230072969 + 3 ^ 40 * 7369052 * 2
def baseEnd_7369052 : Nat := 1261288547991935927953451

theorem tailTrace_7369052 : CollatzResearch.WordTrace tailWord_7369052 prefixEnd_7369052 1261288547991935927953451 := by
  unfold tailWord_7369052
  simp only [CollatzResearch.WordTrace]
  refine ⟨134385703449595306364854705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179180937932793741819806273 134385703449595306364854705)
  ·
    refine ⟨100789277587196479773641029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134385703449595306364854705 100789277587196479773641029)
    ·
      refine ⟨18897989547599339957557693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100789277587196479773641029 18897989547599339957557693)
      ·
        refine ⟨7086746080349752484084135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18897989547599339957557693 7086746080349752484084135)
        ·
          refine ⟨10630119120524628726126203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086746080349752484084135 10630119120524628726126203)
          ·
            refine ⟨15945178680786943089189305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630119120524628726126203 15945178680786943089189305)
            ·
              refine ⟨11958884010590207316891979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15945178680786943089189305 11958884010590207316891979)
              ·
                refine ⟨17938326015885310975337969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11958884010590207316891979 17938326015885310975337969)
                ·
                  refine ⟨13453744511913983231503477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17938326015885310975337969 13453744511913983231503477)
                  ·
                    refine ⟨1261288547991935927953451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453744511913983231503477 1261288547991935927953451)
                    ·
                      rfl

theorem cell23_7369052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7369052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369052 prefixEnd_7369052 := by exact prefixLift 7369052
  have htrace : WordTrace (prefixWord ++ tailWord_7369052) baseStart_7369052 baseEnd_7369052 := by
    simpa [prefixWord, tailWord_7369052, baseEnd_7369052] using wordTrace_append hprefix tailTrace_7369052
  have hstable : (prefixWord ++ tailWord_7369052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369052).length < 2 ^ (prefixWord ++ tailWord_7369052).sum := by decide
  have hdescent : baseEnd_7369052 < baseStart_7369052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369065 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 1, 4]
def baseStart_7369065 : Nat := 118140960795 + 7369065 * 2 ^ 59
def prefixEnd_7369065 : Nat := 4983230072969 + 3 ^ 40 * 7369065 * 2
def baseEnd_7369065 : Nat := 1261290773074772077665931

theorem tailTrace_7369065 : CollatzResearch.WordTrace tailWord_7369065 prefixEnd_7369065 1261290773074772077665931 := by
  unfold tailWord_7369065
  simp only [CollatzResearch.WordTrace]
  refine ⟨268771881048143515949932649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179181254032095677299955099 268771881048143515949932649)
  ·
    refine ⟨201578910786107636962449487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268771881048143515949932649 201578910786107636962449487)
    ·
      refine ⟨302368366179161455443674231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201578910786107636962449487 302368366179161455443674231)
      ·
        refine ⟨453552549268742183165511347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302368366179161455443674231 453552549268742183165511347)
        ·
          refine ⟨680328823903113274748267021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453552549268742183165511347 680328823903113274748267021)
          ·
            refine ⟨255123308963667478030600133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680328823903113274748267021 255123308963667478030600133)
            ·
              refine ⟨47835620430687652130737525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255123308963667478030600133 47835620430687652130737525)
              ·
                refine ⟨4484589415376967387256643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47835620430687652130737525 4484589415376967387256643)
                ·
                  refine ⟨6726884123065451080884965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484589415376967387256643 6726884123065451080884965)
                  ·
                    refine ⟨1261290773074772077665931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726884123065451080884965 1261290773074772077665931)
                    ·
                      rfl

theorem cell23_7369065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_7369065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369065 prefixEnd_7369065 := by exact prefixLift 7369065
  have htrace : WordTrace (prefixWord ++ tailWord_7369065) baseStart_7369065 baseEnd_7369065 := by
    simpa [prefixWord, tailWord_7369065, baseEnd_7369065] using wordTrace_append hprefix tailTrace_7369065
  have hstable : (prefixWord ++ tailWord_7369065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369065).length < 2 ^ (prefixWord ++ tailWord_7369065).sum := by decide
  have hdescent : baseEnd_7369065 < baseStart_7369065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369081 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7369081 : Nat := 118140960795 + 7369081 * 2 ^ 59
def prefixEnd_7369081 : Nat := 4983230072969 + 3 ^ 40 * 7369081 * 2
def baseEnd_7369081 : Nat := 3783880534914788170397719

theorem tailTrace_7369081 : CollatzResearch.WordTrace tailWord_7369081 prefixEnd_7369081 3783880534914788170397719 := by
  unfold tailWord_7369081
  simp only [CollatzResearch.WordTrace]
  refine ⟨268772464616085550682515097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179181643077390367121676731 268772464616085550682515097)
  ·
    refine ⟨201579348462064163011886323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268772464616085550682515097 201579348462064163011886323)
    ·
      refine ⟨302369022693096244517829485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201579348462064163011886323 302369022693096244517829485)
      ·
        refine ⟨113388383509911091694186057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302369022693096244517829485 113388383509911091694186057)
        ·
          refine ⟨85041287632433318770639543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113388383509911091694186057 85041287632433318770639543)
          ·
            refine ⟨127561931448649978155959315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85041287632433318770639543 127561931448649978155959315)
            ·
              refine ⟨191342897172974967233938973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127561931448649978155959315 191342897172974967233938973)
              ·
                refine ⟨71753586439865612712727115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191342897172974967233938973 71753586439865612712727115)
                ·
                  refine ⟨107630379659798419069090673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71753586439865612712727115 107630379659798419069090673)
                  ·
                    refine ⟨80722784744848814301818005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107630379659798419069090673 80722784744848814301818005)
                    ·
                      refine ⟨3783880534914788170397719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80722784744848814301818005 3783880534914788170397719)
                      ·
                        rfl

theorem cell23_7369081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7369081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369081 prefixEnd_7369081 := by exact prefixLift 7369081
  have htrace : WordTrace (prefixWord ++ tailWord_7369081) baseStart_7369081 baseEnd_7369081 := by
    simpa [prefixWord, tailWord_7369081, baseEnd_7369081] using wordTrace_append hprefix tailTrace_7369081
  have hstable : (prefixWord ++ tailWord_7369081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369081).length < 2 ^ (prefixWord ++ tailWord_7369081).sum := by decide
  have hdescent : baseEnd_7369081 < baseStart_7369081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369131 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_7369131 : Nat := 118140960795 + 7369131 * 2 ^ 59
def prefixEnd_7369131 : Nat := 4983230072969 + 3 ^ 40 * 7369131 * 2
def baseEnd_7369131 : Nat := 3783906208947512974772489

theorem tailTrace_7369131 : CollatzResearch.WordTrace tailWord_7369131 prefixEnd_7369131 3783906208947512974772489 := by
  unfold tailWord_7369131
  simp only [CollatzResearch.WordTrace]
  refine ⟨268774288265904409221835247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179182858843936272814556831 268774288265904409221835247)
  ·
    refine ⟨403161432398856613832752871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268774288265904409221835247 403161432398856613832752871)
    ·
      refine ⟨604742148598284920749129307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403161432398856613832752871 604742148598284920749129307)
      ·
        refine ⟨907113222897427381123693961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604742148598284920749129307 907113222897427381123693961)
        ·
          refine ⟨680334917173070535842770471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907113222897427381123693961 680334917173070535842770471)
          ·
            refine ⟨1020502375759605803764155707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680334917173070535842770471 1020502375759605803764155707)
            ·
              refine ⟨1530753563639408705646233561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020502375759605803764155707 1530753563639408705646233561)
              ·
                refine ⟨1148065172729556529234675171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530753563639408705646233561 1148065172729556529234675171)
                ·
                  refine ⟨1722097759094334793852012757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148065172729556529234675171 1722097759094334793852012757)
                  ·
                    refine ⟨40361666228773471730906549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1722097759094334793852012757 40361666228773471730906549)
                    ·
                      refine ⟨3783906208947512974772489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40361666228773471730906549 3783906208947512974772489)
                      ·
                        rfl

theorem cell23_7369131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_7369131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369131 prefixEnd_7369131 := by exact prefixLift 7369131
  have htrace : WordTrace (prefixWord ++ tailWord_7369131) baseStart_7369131 baseEnd_7369131 := by
    simpa [prefixWord, tailWord_7369131, baseEnd_7369131] using wordTrace_append hprefix tailTrace_7369131
  have hstable : (prefixWord ++ tailWord_7369131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369131).length < 2 ^ (prefixWord ++ tailWord_7369131).sum := by decide
  have hdescent : baseEnd_7369131 < baseStart_7369131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369162 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_7369162 : Nat := 118140960795 + 7369162 * 2 ^ 59
def prefixEnd_7369162 : Nat := 4983230072969 + 3 ^ 40 * 7369162 * 2
def baseEnd_7369162 : Nat := 3783922126847802353484847

theorem tailTrace_7369162 : CollatzResearch.WordTrace tailWord_7369162 prefixEnd_7369162 3783922126847802353484847 := by
  unfold tailWord_7369162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67193854732198025379053435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 179183612619194734344142493 67193854732198025379053435)
  ·
    refine ⟨100790782098297038068580153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67193854732198025379053435 100790782098297038068580153)
    ·
      refine ⟨75593086573722778551435115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100790782098297038068580153 75593086573722778551435115)
      ·
        refine ⟨113389629860584167827152673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75593086573722778551435115 113389629860584167827152673)
        ·
          refine ⟨85042222395438125870364505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113389629860584167827152673 85042222395438125870364505)
          ·
            refine ⟨63781666796578594402773379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85042222395438125870364505 63781666796578594402773379)
            ·
              refine ⟨95672500194867891604160069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63781666796578594402773379 95672500194867891604160069)
              ·
                refine ⟨17938593786537729675780013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95672500194867891604160069 17938593786537729675780013)
                ·
                  refine ⟨6726972669951648628417505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17938593786537729675780013 6726972669951648628417505)
                  ·
                    refine ⟨5045229502463736471313129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726972669951648628417505 5045229502463736471313129)
                    ·
                      refine ⟨3783922126847802353484847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045229502463736471313129 3783922126847802353484847)
                      ·
                        rfl

theorem cell23_7369162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_7369162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369162 prefixEnd_7369162 := by exact prefixLift 7369162
  have htrace : WordTrace (prefixWord ++ tailWord_7369162) baseStart_7369162 baseEnd_7369162 := by
    simpa [prefixWord, tailWord_7369162, baseEnd_7369162] using wordTrace_append hprefix tailTrace_7369162
  have hstable : (prefixWord ++ tailWord_7369162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369162).length < 2 ^ (prefixWord ++ tailWord_7369162).sum := by decide
  have hdescent : baseEnd_7369162 < baseStart_7369162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369195 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 3]
def baseStart_7369195 : Nat := 118140960795 + 7369195 * 2 ^ 59
def prefixEnd_7369195 : Nat := 4983230072969 + 3 ^ 40 * 7369195 * 2
def baseEnd_7369195 : Nat := 3783939071709400724372195

theorem tailTrace_7369195 : CollatzResearch.WordTrace tailWord_7369195 prefixEnd_7369195 3783939071709400724372195 := by
  unfold tailWord_7369195
  simp only [CollatzResearch.WordTrace]
  refine ⟨268776622537672548152165039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179184415025115032101443359 268776622537672548152165039)
  ·
    refine ⟨403164933806508822228247559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268776622537672548152165039 403164933806508822228247559)
    ·
      refine ⟨604747400709763233342371339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403164933806508822228247559 604747400709763233342371339)
      ·
        refine ⟨907121101064644850013557009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604747400709763233342371339 907121101064644850013557009)
        ·
          refine ⟨680340825798483637510167757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907121101064644850013557009 680340825798483637510167757)
          ·
            refine ⟨255127809674431364066312909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680340825798483637510167757 255127809674431364066312909)
            ·
              refine ⟨95672928627911761524867341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255127809674431364066312909 95672928627911761524867341)
              ·
                refine ⟨35877348235466910571825253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95672928627911761524867341 35877348235466910571825253)
                ·
                  refine ⟨6727002794150045732217235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35877348235466910571825253 6727002794150045732217235)
                  ·
                    refine ⟨10090504191225068598325853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727002794150045732217235 10090504191225068598325853)
                    ·
                      refine ⟨3783939071709400724372195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090504191225068598325853 3783939071709400724372195)
                      ·
                        rfl

theorem cell23_7369195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 3].length) (baseStart_7369195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369195 prefixEnd_7369195 := by exact prefixLift 7369195
  have htrace : WordTrace (prefixWord ++ tailWord_7369195) baseStart_7369195 baseEnd_7369195 := by
    simpa [prefixWord, tailWord_7369195, baseEnd_7369195] using wordTrace_append hprefix tailTrace_7369195
  have hstable : (prefixWord ++ tailWord_7369195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369195).length < 2 ^ (prefixWord ++ tailWord_7369195).sum := by decide
  have hdescent : baseEnd_7369195 < baseStart_7369195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369196 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_7369196 : Nat := 118140960795 + 7369196 * 2 ^ 59
def prefixEnd_7369196 : Nat := 4983230072969 + 3 ^ 40 * 7369196 * 2
def baseEnd_7369196 : Nat := 3783939585190055220459691

theorem tailTrace_7369196 : CollatzResearch.WordTrace tailWord_7369196 prefixEnd_7369196 3783939585190055220459691 := by
  unfold tailWord_7369196
  simp only [CollatzResearch.WordTrace]
  refine ⟨134388329505334462661475721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179184439340445950215300961 134388329505334462661475721)
  ·
    refine ⟨100791247129000846996106791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134388329505334462661475721 100791247129000846996106791)
    ·
      refine ⟨151186870693501270494160187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100791247129000846996106791 151186870693501270494160187)
      ·
        refine ⟨226780306040251905741240281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151186870693501270494160187 226780306040251905741240281)
        ·
          refine ⟨170085229530188929305930211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226780306040251905741240281 170085229530188929305930211)
          ·
            refine ⟨255127844295283393958895317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170085229530188929305930211 255127844295283393958895317)
            ·
              refine ⟨5979558850670704545911609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255127844295283393958895317 5979558850670704545911609)
              ·
                refine ⟨4484669138003028409433707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979558850670704545911609 4484669138003028409433707)
                ·
                  refine ⟨6727003707004542614150561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484669138003028409433707 6727003707004542614150561)
                  ·
                    refine ⟨5045252780253406960612921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727003707004542614150561 5045252780253406960612921)
                    ·
                      refine ⟨3783939585190055220459691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045252780253406960612921 3783939585190055220459691)
                      ·
                        rfl

theorem cell23_7369196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_7369196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369196 prefixEnd_7369196 := by exact prefixLift 7369196
  have htrace : WordTrace (prefixWord ++ tailWord_7369196) baseStart_7369196 baseEnd_7369196 := by
    simpa [prefixWord, tailWord_7369196, baseEnd_7369196] using wordTrace_append hprefix tailTrace_7369196
  have hstable : (prefixWord ++ tailWord_7369196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369196).length < 2 ^ (prefixWord ++ tailWord_7369196).sum := by decide
  have hdescent : baseEnd_7369196 < baseStart_7369196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369229 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7369229 : Nat := 118140960795 + 7369229 * 2 ^ 59
def prefixEnd_7369229 : Nat := 4983230072969 + 3 ^ 40 * 7369229 * 2
def baseEnd_7369229 : Nat := 3783956530051653591347039

theorem tailTrace_7369229 : CollatzResearch.WordTrace tailWord_7369229 prefixEnd_7369229 3783956530051653591347039 := by
  unfold tailWord_7369229
  simp only [CollatzResearch.WordTrace]
  refine ⟨268777862619549371958902741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179185241746366247972601827 268777862619549371958902741)
  ·
    refine ⟨6299481155145688405286783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 268777862619549371958902741 6299481155145688405286783)
    ·
      refine ⟨9449221732718532607930175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299481155145688405286783 9449221732718532607930175)
      ·
        refine ⟨14173832599077798911895263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449221732718532607930175 14173832599077798911895263)
        ·
          refine ⟨21260748898616698367842895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173832599077798911895263 21260748898616698367842895)
          ·
            refine ⟨31891123347925047551764343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21260748898616698367842895 31891123347925047551764343)
            ·
              refine ⟨47836685021887571327646515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31891123347925047551764343 47836685021887571327646515)
              ·
                refine ⟨71755027532831356991469773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47836685021887571327646515 71755027532831356991469773)
                ·
                  refine ⟨26908135324811758871801165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71755027532831356991469773 26908135324811758871801165)
                  ·
                    refine ⟨10090550746804409576925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26908135324811758871801165 10090550746804409576925437)
                    ·
                      refine ⟨3783956530051653591347039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10090550746804409576925437 3783956530051653591347039)
                      ·
                        rfl

theorem cell23_7369229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7369229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369229 prefixEnd_7369229 := by exact prefixLift 7369229
  have htrace : WordTrace (prefixWord ++ tailWord_7369229) baseStart_7369229 baseEnd_7369229 := by
    simpa [prefixWord, tailWord_7369229, baseEnd_7369229] using wordTrace_append hprefix tailTrace_7369229
  have hstable : (prefixWord ++ tailWord_7369229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369229).length < 2 ^ (prefixWord ++ tailWord_7369229).sum := by decide
  have hdescent : baseEnd_7369229 < baseStart_7369229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369262 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7369262 : Nat := 118140960795 + 7369262 * 2 ^ 59
def prefixEnd_7369262 : Nat := 4983230072969 + 3 ^ 40 * 7369262 * 2
def baseEnd_7369262 : Nat := 1261324491637750654078129

theorem tailTrace_7369262 : CollatzResearch.WordTrace tailWord_7369262 prefixEnd_7369262 1261324491637750654078129 := by
  unfold tailWord_7369262
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597383278553727324356755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 179186044152286545729902693 33597383278553727324356755)
  ·
    refine ⟨50396074917830590986535133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33597383278553727324356755 50396074917830590986535133)
    ·
      refine ⟨18898528094186471619950675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50396074917830590986535133 18898528094186471619950675)
      ·
        refine ⟨28347792141279707429926013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898528094186471619950675 28347792141279707429926013)
        ·
          refine ⟨10630422052979890286222255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28347792141279707429926013 10630422052979890286222255)
          ·
            refine ⟨15945633079469835429333383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630422052979890286222255 15945633079469835429333383)
            ·
              refine ⟨23918449619204753144000075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945633079469835429333383 23918449619204753144000075)
              ·
                refine ⟨35877674428807129716000113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23918449619204753144000075 35877674428807129716000113)
                ·
                  refine ⟨26908255821605347287000085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35877674428807129716000113 26908255821605347287000085)
                  ·
                    refine ⟨1261324491637750654078129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26908255821605347287000085 1261324491637750654078129)
                    ·
                      rfl

theorem cell23_7369262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7369262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369262 prefixEnd_7369262 := by exact prefixLift 7369262
  have htrace : WordTrace (prefixWord ++ tailWord_7369262) baseStart_7369262 baseEnd_7369262 := by
    simpa [prefixWord, tailWord_7369262, baseEnd_7369262] using wordTrace_append hprefix tailTrace_7369262
  have hstable : (prefixWord ++ tailWord_7369262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369262).length < 2 ^ (prefixWord ++ tailWord_7369262).sum := by decide
  have hdescent : baseEnd_7369262 < baseStart_7369262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369269 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7369269 : Nat := 118140960795 + 7369269 * 2 ^ 59
def prefixEnd_7369269 : Nat := 4983230072969 + 3 ^ 40 * 7369269 * 2
def baseEnd_7369269 : Nat := 3783977069277833434846855

theorem tailTrace_7369269 : CollatzResearch.WordTrace tailWord_7369269 prefixEnd_7369269 3783977069277833434846855 := by
  unfold tailWord_7369269
  simp only [CollatzResearch.WordTrace]
  refine ⟨268779321539404458790358861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 179186214359602972526905907 268779321539404458790358861)
  ·
    refine ⟨100792245577276672046384573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268779321539404458790358861 100792245577276672046384573)
    ·
      refine ⟨37797092091478752017394215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100792245577276672046384573 37797092091478752017394215)
      ·
        refine ⟨56695638137218128026091323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37797092091478752017394215 56695638137218128026091323)
        ·
          refine ⟨85043457205827192039136985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56695638137218128026091323 85043457205827192039136985)
          ·
            refine ⟨63782592904370394029352739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85043457205827192039136985 63782592904370394029352739)
            ·
              refine ⟨95673889356555591044029109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63782592904370394029352739 95673889356555591044029109)
              ·
                refine ⟨8969427127177086660377729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95673889356555591044029109 8969427127177086660377729)
                ·
                  refine ⟨6727070345382814995283297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8969427127177086660377729 6727070345382814995283297)
                  ·
                    refine ⟨5045302759037111246462473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727070345382814995283297 5045302759037111246462473)
                    ·
                      refine ⟨3783977069277833434846855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045302759037111246462473 3783977069277833434846855)
                      ·
                        rfl

theorem cell23_7369269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7369269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369269 prefixEnd_7369269 := by exact prefixLift 7369269
  have htrace : WordTrace (prefixWord ++ tailWord_7369269) baseStart_7369269 baseEnd_7369269 := by
    simpa [prefixWord, tailWord_7369269, baseEnd_7369269] using wordTrace_append hprefix tailTrace_7369269
  have hstable : (prefixWord ++ tailWord_7369269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369269).length < 2 ^ (prefixWord ++ tailWord_7369269).sum := by decide
  have hdescent : baseEnd_7369269 < baseStart_7369269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369286 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7369286 : Nat := 118140960795 + 7369286 * 2 ^ 59
def prefixEnd_7369286 : Nat := 4983230072969 + 3 ^ 40 * 7369286 * 2
def baseEnd_7369286 : Nat := 3783985798448959868334277

theorem tailTrace_7369286 : CollatzResearch.WordTrace tailWord_7369286 prefixEnd_7369286 3783985798448959868334277 := by
  unfold tailWord_7369286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399373174385714709178991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 179186627720228580462485141 8399373174385714709178991)
  ·
    refine ⟨12599059761578572063768487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8399373174385714709178991 12599059761578572063768487)
    ·
      refine ⟨18898589642367858095652731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599059761578572063768487 18898589642367858095652731)
      ·
        refine ⟨28347884463551787143479097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898589642367858095652731 28347884463551787143479097)
        ·
          refine ⟨21260913347663840357609323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28347884463551787143479097 21260913347663840357609323)
          ·
            refine ⟨31891370021495760536413985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21260913347663840357609323 31891370021495760536413985)
            ·
              refine ⟨23918527516121820402310489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31891370021495760536413985 23918527516121820402310489)
              ·
                refine ⟨17938895637091365301732867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23918527516121820402310489 17938895637091365301732867)
                ·
                  refine ⟨26908343455637047952599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17938895637091365301732867 26908343455637047952599301)
                  ·
                    refine ⟨5045314397931946491112369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26908343455637047952599301 5045314397931946491112369)
                    ·
                      refine ⟨3783985798448959868334277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5045314397931946491112369 3783985798448959868334277)
                      ·
                        rfl

theorem cell23_7369286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7369286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369286 prefixEnd_7369286 := by exact prefixLift 7369286
  have htrace : WordTrace (prefixWord ++ tailWord_7369286) baseStart_7369286 baseEnd_7369286 := by
    simpa [prefixWord, tailWord_7369286, baseEnd_7369286] using wordTrace_append hprefix tailTrace_7369286
  have hstable : (prefixWord ++ tailWord_7369286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369286).length < 2 ^ (prefixWord ++ tailWord_7369286).sum := by decide
  have hdescent : baseEnd_7369286 < baseStart_7369286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7369292 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 5]
def baseStart_7369292 : Nat := 118140960795 + 7369292 * 2 ^ 59
def prefixEnd_7369292 : Nat := 4983230072969 + 3 ^ 40 * 7369292 * 2
def baseEnd_7369292 : Nat := 420443208814765204984361

theorem tailTrace_7369292 : CollatzResearch.WordTrace tailWord_7369292 prefixEnd_7369292 420443208814765204984361 := by
  unfold tailWord_7369292
  simp only [CollatzResearch.WordTrace]
  refine ⟨134390080209160566859223065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 179186773612214089145630753 134390080209160566859223065)
  ·
    refine ⟨100792560156870425144417299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134390080209160566859223065 100792560156870425144417299)
    ·
      refine ⟨151188840235305637716625949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100792560156870425144417299 151188840235305637716625949)
      ·
        refine ⟨56695815088239614143734731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151188840235305637716625949 56695815088239614143734731)
        ·
          refine ⟨85043722632359421215602097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56695815088239614143734731 85043722632359421215602097)
          ·
            refine ⟨63782791974269565911701573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85043722632359421215602097 63782791974269565911701573)
            ·
              refine ⟨11959273495175543608444045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63782791974269565911701573 11959273495175543608444045)
              ·
                refine ⟨4484727560690828853166517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11959273495175543608444045 4484727560690828853166517)
                ·
                  refine ⟨420443208814765204984361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484727560690828853166517 420443208814765204984361)
                  ·
                    rfl

theorem cell23_7369292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_7369292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7369292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7369292 prefixEnd_7369292 := by exact prefixLift 7369292
  have htrace : WordTrace (prefixWord ++ tailWord_7369292) baseStart_7369292 baseEnd_7369292 := by
    simpa [prefixWord, tailWord_7369292, baseEnd_7369292] using wordTrace_append hprefix tailTrace_7369292
  have hstable : (prefixWord ++ tailWord_7369292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7369292).length < 2 ^ (prefixWord ++ tailWord_7369292).sum := by decide
  have hdescent : baseEnd_7369292 < baseStart_7369292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7369292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
