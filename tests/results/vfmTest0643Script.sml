Theory vfmTest0643[no_sig_docs]
Ancestors vfmTestDefs0643
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0643_0.nsv", "result0643_1.nsv", "result0643_2.nsv", "result0643_3.nsv", "result0643_4.nsv", "result0643_5.nsv", "result0643_6.nsv", "result0643_7.nsv"];
val thyn = "vfmTestDefs0643";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
