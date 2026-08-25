Theory vfmTest0457[no_sig_docs]
Ancestors vfmTestDefs0457
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0457_0.nsv", "result0457_1.nsv", "result0457_2.nsv", "result0457_3.nsv", "result0457_4.nsv", "result0457_5.nsv", "result0457_6.nsv", "result0457_7.nsv", "result0457_8.nsv", "result0457_9.nsv", "result0457_10.nsv", "result0457_11.nsv", "result0457_12.nsv", "result0457_13.nsv", "result0457_14.nsv", "result0457_15.nsv", "result0457_16.nsv"];
val thyn = "vfmTestDefs0457";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
