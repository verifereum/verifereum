Theory vfmTest0445[no_sig_docs]
Ancestors vfmTestDefs0445
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0445_0.nsv", "result0445_1.nsv", "result0445_2.nsv", "result0445_3.nsv", "result0445_4.nsv", "result0445_5.nsv", "result0445_6.nsv", "result0445_7.nsv", "result0445_8.nsv", "result0445_9.nsv", "result0445_10.nsv", "result0445_11.nsv"];
val thyn = "vfmTestDefs0445";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
