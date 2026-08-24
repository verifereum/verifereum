Theory vfmTest0817[no_sig_docs]
Ancestors vfmTestDefs0817
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0817_0.nsv", "result0817_1.nsv", "result0817_2.nsv", "result0817_3.nsv", "result0817_4.nsv", "result0817_5.nsv", "result0817_6.nsv", "result0817_7.nsv"];
val thyn = "vfmTestDefs0817";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
