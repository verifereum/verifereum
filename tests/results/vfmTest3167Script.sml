Theory vfmTest3167[no_sig_docs]
Ancestors vfmTestDefs3167
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3167_0.nsv", "result3167_1.nsv", "result3167_2.nsv", "result3167_3.nsv"];
val thyn = "vfmTestDefs3167";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
