Theory vfmTest0265[no_sig_docs]
Ancestors vfmTestDefs0265
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0265_0.nsv", "result0265_1.nsv", "result0265_2.nsv", "result0265_3.nsv"];
val thyn = "vfmTestDefs0265";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
