Theory vfmTest0304[no_sig_docs]
Ancestors vfmTestDefs0304
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0304_0.nsv", "result0304_1.nsv", "result0304_2.nsv"];
val thyn = "vfmTestDefs0304";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
