Theory vfmTest3076[no_sig_docs]
Ancestors vfmTestDefs3076
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3076_0.nsv", "result3076_1.nsv", "result3076_2.nsv"];
val thyn = "vfmTestDefs3076";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
