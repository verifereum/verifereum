Theory vfmTest3137[no_sig_docs]
Ancestors vfmTestDefs3137
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3137_0.nsv", "result3137_1.nsv", "result3137_2.nsv", "result3137_3.nsv"];
val thyn = "vfmTestDefs3137";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
