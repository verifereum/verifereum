Theory vfmTest0339[no_sig_docs]
Ancestors vfmTestDefs0339
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0339_0.nsv", "result0339_1.nsv", "result0339_2.nsv", "result0339_3.nsv", "result0339_4.nsv", "result0339_5.nsv", "result0339_6.nsv", "result0339_7.nsv", "result0339_8.nsv", "result0339_9.nsv"];
val thyn = "vfmTestDefs0339";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
