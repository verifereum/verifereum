Theory vfmTest1528[no_sig_docs]
Ancestors vfmTestDefs1528
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1528_0.nsv", "result1528_1.nsv", "result1528_2.nsv", "result1528_3.nsv", "result1528_4.nsv", "result1528_5.nsv", "result1528_6.nsv"];
val thyn = "vfmTestDefs1528";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
