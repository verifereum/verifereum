Theory vfmTest2594[no_sig_docs]
Ancestors vfmTestDefs2594
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2594_0.nsv", "result2594_1.nsv", "result2594_2.nsv", "result2594_3.nsv"];
val thyn = "vfmTestDefs2594";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
