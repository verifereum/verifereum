Theory vfmTest0586[no_sig_docs]
Ancestors vfmTestDefs0586
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0586_0.nsv", "result0586_1.nsv", "result0586_2.nsv", "result0586_3.nsv", "result0586_4.nsv", "result0586_5.nsv", "result0586_6.nsv", "result0586_7.nsv"];
val thyn = "vfmTestDefs0586";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
