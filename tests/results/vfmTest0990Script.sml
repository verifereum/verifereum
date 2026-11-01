Theory vfmTest0990[no_sig_docs]
Ancestors vfmTestDefs0990
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0990_0.nsv", "result0990_1.nsv", "result0990_2.nsv", "result0990_3.nsv", "result0990_4.nsv", "result0990_5.nsv", "result0990_6.nsv", "result0990_7.nsv", "result0990_8.nsv"];
val thyn = "vfmTestDefs0990";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
