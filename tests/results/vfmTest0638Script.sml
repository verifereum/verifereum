Theory vfmTest0638[no_sig_docs]
Ancestors vfmTestDefs0638
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0638_0.nsv", "result0638_1.nsv", "result0638_2.nsv", "result0638_3.nsv", "result0638_4.nsv", "result0638_5.nsv", "result0638_6.nsv", "result0638_7.nsv"];
val thyn = "vfmTestDefs0638";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
