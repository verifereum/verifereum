Theory vfmTest3025[no_sig_docs]
Ancestors vfmTestDefs3025
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3025_0.nsv", "result3025_1.nsv", "result3025_2.nsv", "result3025_3.nsv", "result3025_4.nsv"];
val thyn = "vfmTestDefs3025";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
