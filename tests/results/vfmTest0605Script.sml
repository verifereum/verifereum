Theory vfmTest0605[no_sig_docs]
Ancestors vfmTestDefs0605
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0605_0.nsv", "result0605_1.nsv", "result0605_2.nsv", "result0605_3.nsv", "result0605_4.nsv", "result0605_5.nsv", "result0605_6.nsv", "result0605_7.nsv", "result0605_8.nsv"];
val thyn = "vfmTestDefs0605";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
