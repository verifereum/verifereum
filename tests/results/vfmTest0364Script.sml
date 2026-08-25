Theory vfmTest0364[no_sig_docs]
Ancestors vfmTestDefs0364
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0364_0.nsv", "result0364_1.nsv", "result0364_2.nsv", "result0364_3.nsv", "result0364_4.nsv", "result0364_5.nsv"];
val thyn = "vfmTestDefs0364";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
