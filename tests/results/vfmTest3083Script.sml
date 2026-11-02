Theory vfmTest3083[no_sig_docs]
Ancestors vfmTestDefs3083
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3083_0.nsv", "result3083_1.nsv", "result3083_2.nsv", "result3083_3.nsv"];
val thyn = "vfmTestDefs3083";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
