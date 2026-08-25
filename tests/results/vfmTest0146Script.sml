Theory vfmTest0146[no_sig_docs]
Ancestors vfmTestDefs0146
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0146_0.nsv", "result0146_1.nsv", "result0146_2.nsv"];
val thyn = "vfmTestDefs0146";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
