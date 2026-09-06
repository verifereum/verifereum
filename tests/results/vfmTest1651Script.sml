Theory vfmTest1651[no_sig_docs]
Ancestors vfmTestDefs1651
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1651_0.nsv", "result1651_1.nsv", "result1651_2.nsv", "result1651_3.nsv"];
val thyn = "vfmTestDefs1651";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
