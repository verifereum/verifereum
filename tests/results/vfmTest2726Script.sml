Theory vfmTest2726[no_sig_docs]
Ancestors vfmTestDefs2726
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2726_0.nsv", "result2726_1.nsv", "result2726_2.nsv", "result2726_3.nsv"];
val thyn = "vfmTestDefs2726";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
