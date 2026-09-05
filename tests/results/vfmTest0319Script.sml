Theory vfmTest0319[no_sig_docs]
Ancestors vfmTestDefs0319
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0319_0.nsv", "result0319_1.nsv"];
val thyn = "vfmTestDefs0319";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
