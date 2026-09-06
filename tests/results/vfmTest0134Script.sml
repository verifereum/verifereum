Theory vfmTest0134[no_sig_docs]
Ancestors vfmTestDefs0134
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0134_0.nsv", "result0134_1.nsv", "result0134_2.nsv", "result0134_3.nsv", "result0134_4.nsv", "result0134_5.nsv", "result0134_6.nsv", "result0134_7.nsv", "result0134_8.nsv", "result0134_9.nsv", "result0134_10.nsv", "result0134_11.nsv", "result0134_12.nsv", "result0134_13.nsv", "result0134_14.nsv", "result0134_15.nsv", "result0134_16.nsv", "result0134_17.nsv"];
val thyn = "vfmTestDefs0134";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
