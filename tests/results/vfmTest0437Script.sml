Theory vfmTest0437[no_sig_docs]
Ancestors vfmTestDefs0437
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0437_0.nsv", "result0437_1.nsv", "result0437_2.nsv", "result0437_3.nsv", "result0437_4.nsv", "result0437_5.nsv", "result0437_6.nsv", "result0437_7.nsv", "result0437_8.nsv", "result0437_9.nsv", "result0437_10.nsv", "result0437_11.nsv", "result0437_12.nsv", "result0437_13.nsv", "result0437_14.nsv", "result0437_15.nsv"];
val thyn = "vfmTestDefs0437";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
