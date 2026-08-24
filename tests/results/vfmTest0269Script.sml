Theory vfmTest0269[no_sig_docs]
Ancestors vfmTestDefs0269
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0269_0.nsv", "result0269_1.nsv", "result0269_2.nsv", "result0269_3.nsv", "result0269_4.nsv", "result0269_5.nsv", "result0269_6.nsv", "result0269_7.nsv", "result0269_8.nsv"];
val thyn = "vfmTestDefs0269";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
