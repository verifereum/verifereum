Theory vfmTest3168[no_sig_docs]
Ancestors vfmTestDefs3168
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3168_0.nsv", "result3168_1.nsv", "result3168_2.nsv"];
val thyn = "vfmTestDefs3168";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
