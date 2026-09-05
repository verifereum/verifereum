Theory vfmTest0256[no_sig_docs]
Ancestors vfmTestDefs0256
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0256_0.nsv", "result0256_1.nsv", "result0256_2.nsv", "result0256_3.nsv"];
val thyn = "vfmTestDefs0256";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
