Theory vfmTest0316[no_sig_docs]
Ancestors vfmTestDefs0316
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0316_0.nsv", "result0316_1.nsv"];
val thyn = "vfmTestDefs0316";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
