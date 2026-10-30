Theory vfmTest3101[no_sig_docs]
Ancestors vfmTestDefs3101
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3101_0.nsv", "result3101_1.nsv", "result3101_2.nsv", "result3101_3.nsv", "result3101_4.nsv", "result3101_5.nsv"];
val thyn = "vfmTestDefs3101";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
