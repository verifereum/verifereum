Theory vfmTest3072[no_sig_docs]
Ancestors vfmTestDefs3072
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3072_0.nsv", "result3072_1.nsv", "result3072_2.nsv", "result3072_3.nsv"];
val thyn = "vfmTestDefs3072";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
