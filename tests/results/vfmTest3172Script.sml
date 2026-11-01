Theory vfmTest3172[no_sig_docs]
Ancestors vfmTestDefs3172
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3172_0.nsv", "result3172_1.nsv"];
val thyn = "vfmTestDefs3172";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
