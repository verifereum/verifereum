Theory vfmTest2611[no_sig_docs]
Ancestors vfmTestDefs2611
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2611_0.nsv", "result2611_1.nsv", "result2611_2.nsv", "result2611_3.nsv"];
val thyn = "vfmTestDefs2611";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
