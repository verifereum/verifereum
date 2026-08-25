Theory vfmTest0257[no_sig_docs]
Ancestors vfmTestDefs0257
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0257_0.nsv", "result0257_1.nsv", "result0257_2.nsv", "result0257_3.nsv"];
val thyn = "vfmTestDefs0257";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
