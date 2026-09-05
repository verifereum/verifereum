Theory vfmTest0061[no_sig_docs]
Ancestors vfmTestDefs0061
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0061_0.nsv", "result0061_1.nsv", "result0061_2.nsv", "result0061_3.nsv", "result0061_4.nsv", "result0061_5.nsv", "result0061_6.nsv", "result0061_7.nsv"];
val thyn = "vfmTestDefs0061";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
